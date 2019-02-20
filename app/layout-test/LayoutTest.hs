{-|
Copyright   : (c) 2018, Commonwealth Scientific and Industrial Research Organisation
License     : BSD3
Maintainer  : dave.laing.80@gmail.com
Stability   : experimental
Portability : non-portable
-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module LayoutTest where

import Control.Monad (replicateM, when, unless, forM)
import Data.Foldable
import Data.Text (Text)
import qualified Data.Text as Text
import qualified Data.Text.Unsafe as Text

import Control.Monad.State (MonadState, evalStateT, get, put)
import Control.Monad.Except (MonadError, runExcept, throwError)

import Control.Lens hiding (elements)

import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.QuickCheck

import Syntax.Prefix
import Syntax.Token
import Syntax.Dyck
import Syntax.Rope
import Relative.Class
import Relative.Cat hiding (null)
import qualified Relative.Cat as Cat
import Relative.Delta
import Rev
import qualified Syntax.Lexer as Lex
import Syntax.Layout

import Debug.Trace

linesToLayouts :: Delta -> [Text] -> (Delta, [Layout])
linesToLayouts d0 ts =
  let
    f (d, ls) t =
      let dt = Delta . Text.lengthWord16 $ t
      in
        ( d <> dt
        , ls <> pure (dyckLayout dt (fromText t) (Lex.lex t))
        )
  in
    foldl' f (d0, mempty) ts

textToLayouts :: Text -> [Layout]
textToLayouts t =
  let
    ts' = Text.lines t
    ts = case ts' of
      [] -> []
      _ -> fmap (<> "\n") (init ts') ++ [last ts']
    f :: Int -> Layout
    f i = (\(x, y) -> g x y) $ splitAt i ts
    g :: [Text] -> [Text] -> Layout
    g x y =
      let
        (d, ls1) = linesToLayouts 0 x
        (_, ls2) = linesToLayouts d y
        f1 = fold ls1
        f2 = fold ls2
      in
        f1 <> f2
  in
    fmap f [0..length ts - 1]

textToLayoutsNoVV :: Text -> [Layout]
textToLayoutsNoVV t =
  let
    ts' = Text.lines t
    ts = case ts' of
      [] -> []
      _ -> fmap (<> "\n") (init ts') ++ [last ts']
    f :: Int -> [Layout]
    f i = (\(x, y) -> g x y) $ splitAt i ts
    g :: [Text] -> [Text] -> [Layout]
    g x y =
      let
        (d, ls1) = linesToLayouts 0 x
        (_, ls2) = linesToLayouts d y
        f1 = fold ls1
        f2 = fold ls2
      in
        case (f1, f2) of
          (V _ _ _ _, V _ _ _ _) -> []
          _ -> pure $ f1 <> f2
  in
    foldMap f [0..length ts - 1]

allEq :: Eq a => [a] -> Bool
allEq xs =
  and $ zipWith (==) xs (tail xs)

newtype Layouts = Layouts [Layout]
  deriving (Eq)

showLayouts :: Layouts -> [Text]
showLayouts (Layouts ls) = foldMap (("" :) . showLayout) ls

showLayout :: Layout -> [Text]
showLayout (E d) =
  ["E " <> Text.pack (show d)]
showLayout (S d r) =
  ["S " <> Text.pack (show d)] ++
  fmap ("  " <>) (showRun r)
showLayout (V d l m r) =
  ["V " <> Text.pack (show d)] ++
  showCat "    " l ++
  fmap ("  " <>) (showRun m) ++
  showRevCat "    " r

showDycks :: Cat Dyck -> [Text]
showDycks ds = case preview _Cons ds of
  Nothing -> []
  Just (r, rs) -> [Text.pack (show r)] ++ showDycks rs

showRun :: Run -> [Text]
showRun (Run p ds ts es pr) =
  ["Run"] ++
  ["  " <> Text.pack (show p)] ++
  fmap ("  " <>) (showDycks ds) ++
  ["  " <> Text.pack (show ts)] ++
  ["  " <> Text.pack (show es)] ++
  ["  " <> Text.pack (show pr)]

showCat :: Text -> Cat Run -> [Text]
showCat pad cs = case preview _Cons cs of
  Nothing -> []
  Just (r, rs) -> fmap (pad <>) (showRun r) ++ showCat pad rs

showRevCat :: Text -> Rev Cat Run -> [Text]
showRevCat pad (Rev cs) = showCat pad (revCat cs)

instance Show Layouts where
  show = Text.unpack . Text.unlines .  showLayouts

data DeltaError =
    DeltaOutOfOrder Delta Delta
  | BadRange Delta Delta Delta
  | DyckEmpty Delta
  | DyckMismatch [Delta] [Delta]
  | DyckErrorMismatch [Delta] [Delta]
  deriving (Eq, Ord, Show)

checkLayouts :: [Layout] -> Either DeltaError ()
checkLayouts =
  runExcept . flip evalStateT (Delta 0) . traverse_ (\l -> put (Delta 0) >> checkLayout l)

checkLayout :: (MonadState Delta m, MonadError DeltaError m) => Layout -> m ()
checkLayout (E d) = do
  checkDelta d
  put d
checkLayout (S _ r) = do
  checkRun r
checkLayout (V _ l m r) = do
  checkCatRun l
  checkRun m
  checkRevCatRun r

checkDelta :: (MonadState Delta m, MonadError DeltaError m) => Delta -> m ()
checkDelta d = do
  d' <- get
  when (d < d') $
    throwError $ DeltaOutOfOrder d' d

checkRun :: (MonadState Delta m, MonadError DeltaError m) => Run -> m ()
checkRun (Run _ ds ts es _) = do
  d <- get
  dd <- checkCatDyck ds
  dt <- checkDyck ts
  when (dd /= dt) $
    throwError $ DyckMismatch dd dt
  when (null dd) $ do
    throwError $ DyckEmpty d
  let m = maximum dd
  checkErrors d m es
  put m
  pure ()

checkCatRun :: (MonadState Delta m, MonadError DeltaError m) => Cat Run -> m ()
checkCatRun cr = case preview _Cons cr of
  Nothing -> pure ()
  Just (r, rs) -> do
    checkRun r
    checkCatRun rs

checkRevCatRun :: (MonadState Delta m, MonadError DeltaError m) => Rev Cat Run -> m ()
checkRevCatRun (Rev r) = checkCatRun (revCat r)

checkDyck :: (MonadState Delta m, MonadError DeltaError m) => Dyck -> m [Delta]
checkDyck (Dyck _ ts1 _ ts2 _ _) = do
  let ts = catTokenDeltas ts1 <> catTokenDeltas ts2
  old <- get
  _ <- forM ts $ \d -> do
    checkDelta d
    put d
  put old
  pure ts

checkCatDyck :: (MonadState Delta m, MonadError DeltaError m) => Cat Dyck -> m [Delta]
checkCatDyck cs = case preview _Cons cs of
  Nothing -> pure []
  Just (d, ds) -> do
    a <- checkDyck d
    b <- checkCatDyck ds
    pure $ a ++ b

checkErrors :: (MonadError DeltaError m) => Delta -> Delta -> Cat LayoutMismatch -> m ()
checkErrors d1 d2 cs = case preview _Cons cs of
  Nothing -> pure ()
  Just (e, es) -> do
    checkError d1 d2 e
    checkErrors d1 d2 es

checkError :: (MonadError DeltaError m) => Delta -> Delta -> LayoutMismatch -> m ()
checkError d1 d2 (LayoutMismatch d _ _) = do
  unless (d1 <= d && d < d2) $
    throwError $ BadRange d1 d d2

tokenDeltas :: Token -> [Delta]
tokenDeltas (Token d _) = [d]
tokenDeltas (TokenName d _) = [d]
tokenDeltas (TokenKeyword d _) = [d]
tokenDeltas (TokenInteger d _) = [d]
tokenDeltas (TokenDouble d _) = [d]
tokenDeltas (TokenString d _) = [d]
tokenDeltas (TokenChar d _) = [d]
tokenDeltas (TokenNested _ ds) = catTokenDeltas ds
tokenDeltas (TokenMismatch  _ _ ds) = catTokenDeltas ds
tokenDeltas (TokenUnmatchedOpening _) = []
tokenDeltas (TokenUnmatchedClosing _) = []
tokenDeltas (TokenLexicalError d _) = [d]

catTokenDeltas :: Cat Token -> [Delta]
catTokenDeltas cs = case preview _Cons cs of
  Nothing -> []
  Just (t, ts) -> tokenDeltas t ++ catTokenDeltas ts

-- The property to target is
--   allEq . textToLayouts $ txt
--
-- The text would come from one of two models
-- - one with no mismatched indents
-- - one with at least one mismatched indents

newtype Indent = Indent { unIndent :: Int }
  deriving (Eq, Ord, Show)

instance Arbitrary Indent where
  arbitrary = Indent <$> choose (1, 5)
  shrink = fmap Indent . shrink . unIndent

data IndentedLine = IndentedLine { _indent :: Text, _line :: Text}
  deriving (Eq, Ord, Show)

makeLenses ''IndentedLine

indentedLineToText :: IndentedLine -> Text
indentedLineToText (IndentedLine i l) = i <> l

instance Arbitrary IndentedLine where
  arbitrary = do
    Indent i <- arbitrary
    t <- elements ["one", "two", "three", "four", "five", "six", "seven", "eight", "nine", "ten"]
    pure $ IndentedLine (Text.pack (replicate (2 * i) ' ')) t

newtype ModelLines = ModelLines { modelLines :: [IndentedLine] }
  deriving (Eq, Ord, Semigroup, Monoid)

modelLinesToText :: ModelLines -> Text
modelLinesToText (ModelLines ts) =
  Text.unlines . fmap indentedLineToText $ ts

instance Show ModelLines where
  show = Text.unpack . modelLinesToText

instance Arbitrary ModelLines where
  arbitrary = do
    n <- choose (0, 5)
    xs <- replicateM n arbitrary
    pure $ ModelLines xs
  shrink (ModelLines xs) =
    ModelLines <$> shrinkList (const []) xs

newtype ModelLinesWithErrors = ModelLinesWithErrors ModelLines
  deriving (Eq, Ord, Semigroup, Monoid)

modelLinesWithErrorsToText :: ModelLinesWithErrors -> Text
modelLinesWithErrorsToText (ModelLinesWithErrors ml) = modelLinesToText ml

instance Show ModelLinesWithErrors where
  show = Text.unpack . modelLinesWithErrorsToText

hasTab :: ModelLines -> Bool
hasTab (ModelLines ls) = any (Text.isInfixOf "\t" . _indent) ls

addTab :: ModelLines -> Gen ModelLines
addTab (ModelLines ls) = do
  let l1 = length ls
  if l1 == 0
  then pure $ ModelLines []
  else do
    n <- choose (0, l1 - 1)
    let
      l = ls !! n
      l2 = Text.length (_indent l)
    m <- choose (0, l2 - 1)
    let ls' = ls & ix n . indent . ix m .~ '\t'
    pure $ ModelLines ls'

instance Arbitrary ModelLinesWithErrors where
  arbitrary = arbitrary >>= fmap ModelLinesWithErrors . addTab
  shrink (ModelLinesWithErrors ml) =
    ModelLinesWithErrors <$> filter hasTab (shrink ml)

data ModelLinesWithDo =
    MLWDLines ModelLines
  | MLWDDo Indent ModelLinesWithDo
  | MLWDTwo ModelLinesWithDo ModelLinesWithDo
  | MLWDThree ModelLinesWithDo ModelLinesWithDo ModelLinesWithDo
  deriving (Eq, Ord)

hasDo :: ModelLinesWithDo -> Bool
hasDo (MLWDLines _) = False
hasDo (MLWDDo _ _) = True
hasDo (MLWDTwo m1 m2) = hasDo m1 || hasDo m2
hasDo (MLWDThree m1 m2 m3) = hasDo m1 || hasDo m2 || hasDo m3

modelLinesWithDoToModelLines :: ModelLinesWithDo -> ModelLines
modelLinesWithDoToModelLines (MLWDLines ml) =
  ml
modelLinesWithDoToModelLines (MLWDDo (Indent i) mlwd) =
  let
    ModelLines ml = modelLinesWithDoToModelLines mlwd
    it = Text.pack (replicate i ' ')
  in
    ModelLines . (IndentedLine it "do" :) . fmap (\(IndentedLine j l) -> IndentedLine (it <> j) l) $ ml
modelLinesWithDoToModelLines (MLWDTwo mlwd1 mlwd2) =
  modelLinesWithDoToModelLines mlwd1 <>
  modelLinesWithDoToModelLines mlwd2
modelLinesWithDoToModelLines (MLWDThree mlwd1 mlwd2 mlwd3) =
  modelLinesWithDoToModelLines mlwd1 <>
  modelLinesWithDoToModelLines mlwd2 <>
  modelLinesWithDoToModelLines mlwd3

modelLinesWithDoToText :: ModelLinesWithDo -> Text
modelLinesWithDoToText = modelLinesToText . modelLinesWithDoToModelLines

instance Show ModelLinesWithDo where
  show = Text.unpack . modelLinesWithDoToText

genMLWD :: Int -> Gen ModelLinesWithDo
genMLWD s =
  let
      genLines = MLWDLines <$> arbitrary
      genDo = MLWDDo <$> arbitrary <*> genMLWD (s - 1)
      s2 = s `div` 2
      genTwo = MLWDTwo <$> genMLWD s2 <*> genMLWD s2
      s3 = s `div` 3
      genThree = MLWDThree <$> genMLWD s3 <*> genMLWD s3 <*> genMLWD s3
  in
    if s <= 1 then genLines else oneof [genLines, genDo, genTwo, genThree]

instance Arbitrary ModelLinesWithDo where
  arbitrary =
    suchThat (sized genMLWD) hasDo
  shrink (MLWDLines ml) =
    MLWDLines <$> shrink ml
  shrink (MLWDDo i ml) =
    if hasDo ml then [ml] else [] ++ (MLWDDo i <$> shrink ml)
  shrink (MLWDTwo m1 m2) =
    if hasDo m1 then [m1] else [] ++
    if hasDo m2 then [m2] else [] ++
    if hasDo m1 || hasDo m2 then [MLWDTwo n1 n2 | (n1, n2) <- shrink (m1, m2)] else []
  shrink (MLWDThree m1 m2 m3) =
    if hasDo m1 then [m1] else [] ++
    if hasDo m2 then [m2] else [] ++
    if hasDo m3 then [m3] else [] ++
    if hasDo m1 || hasDo m2 || hasDo m3 then [MLWDThree n1 n2 n3 | (n1, n2, n3) <- shrink (m1, m2, m3)] else []

newtype ModelLinesWithDoAndErrors = ModelLinesWithDoAndErrors ModelLinesWithDo
  deriving (Eq, Ord)

modelLinesWithDoAndErrorsToText :: ModelLinesWithDoAndErrors -> Text
modelLinesWithDoAndErrorsToText (ModelLinesWithDoAndErrors mlwd) = modelLinesWithDoToText mlwd

instance Show ModelLinesWithDoAndErrors where
  show = Text.unpack . modelLinesWithDoAndErrorsToText

hasTabWd :: ModelLinesWithDo -> Bool
hasTabWd (MLWDLines ml) =
  hasTab ml
hasTabWd (MLWDDo _ mlwd) =
  hasTabWd mlwd
hasTabWd (MLWDTwo m1 m2) =
  hasTabWd m1 || hasTabWd m2
hasTabWd (MLWDThree m1 m2 m3) =
  hasTabWd m1 || hasTabWd m2 || hasTabWd m3

addTabWd :: ModelLinesWithDo -> Gen ModelLinesWithDo
addTabWd (MLWDLines ml) =
  MLWDLines <$> addTab ml
addTabWd (MLWDDo i mlwd) =
  MLWDDo i <$> addTabWd mlwd
addTabWd (MLWDTwo m1 m2) =
  oneof [ MLWDTwo <$> addTabWd m1 <*> pure m2
        , MLWDTwo <$> pure m1 <*> addTabWd m2
        ]
addTabWd (MLWDThree m1 m2 m3) =
  oneof [ MLWDThree <$> addTabWd m1 <*> pure m2 <*> pure m3
        , MLWDThree <$> pure m1 <*> addTabWd m2 <*> pure m3
        , MLWDThree <$> pure m1 <*> pure m2 <*> addTabWd m3
        ]

instance Arbitrary ModelLinesWithDoAndErrors where
  arbitrary = arbitrary >>= fmap ModelLinesWithDoAndErrors . addTabWd
  shrink (ModelLinesWithDoAndErrors mlwd) =
    ModelLinesWithDoAndErrors <$> filter hasTabWd (shrink mlwd)

exampleF1 :: Text
exampleF1 =
  "do\n\
  \  foo\n\
  \    bar\n\
  \"

exampleF2 :: Text
exampleF2 =
  "foo\n\
  \  bar\n\
  \baz\n\
  \"

exampleF3 :: Text
exampleF3 =
  "do\n\
  \  foo\n\
  \    bar\n\
  \  two\n\
  \"

exampleF4 :: Text
exampleF4 =
  "foo\n\
  \  bar\n\
  \    baz\n\
  \two\n\
  \"

exampleF5 :: Text
exampleF5 =
  "do\n\
  \  three\n\
  \  foo\n\
  \bar\n\
  \"

exampleF6 :: Text
exampleF6 =
  "  one\n\
  \two\n\
  \  three\n\
  \"

exampleF7 :: Text
exampleF7 =
  "one\n\
  \  two\n\
  \  three\n\
  \"

exampleF8 :: Text
exampleF8 =
  "    one\n\
  \  two\n\
  \    three\n\
  \four\n\
  \"

exampleF9 :: Text
exampleF9 =
  "      one\n\
  \    two\n\
  \  three\n\
  \four\n\
  \"

exampleF10 :: Text
exampleF10 =
  "  one\n\
  \do\n\
  \  two\n\
  \  three\n\
  \"

-- this is the case that requires the trailing prefixes
exampleE1 :: Text
exampleE1 =
  "foo\n\
  \\t\tbar\n\
  \  \tbaz\n\
  \"

exampleE2 :: Text
exampleE2 =
  "foo\n\
  \bar\n\
  \  baz\n\
  \\t  two\n\
  \"

exampleE3 :: Text
exampleE3 =
  "foo\n\
  \   bar\n\
  \ \t baz\n\
  \two\n\
  \"

exampleE4 :: Text
exampleE4 =
  "\t   one\n\
  \  two\n\
  \    three\n\
  \"

exampleE5 :: Text
exampleE5 =
  "    one\n\
  \\t two\n\
  \    three\n\
  \"

exampleE6 :: Text
exampleE6 =
  "    one\n\
  \  two\n\
  \\t   three\n\
  \"

exampleE7 :: Text
exampleE7 =
  "\t     one\n\
  \    two\n\
  \  three\n\
  \"

exampleE8 :: Text
exampleE8 =
  "      one\n\
  \\t   two\n\
  \  three\n\
  \"

exampleE9 :: Text
exampleE9 =
  "      one\n\
  \    two\n\
  \\t three\n\
  \"

exampleE10 :: Text
exampleE10 =
  "\tone\n\
  \  two\n\
  \    three\n\
  \  four\n\
  \"

exampleE11 :: Text
exampleE11 =
  "       one\n\
  \   \ttwo\n\
  \       three\n\
  \    four\n\
  \"

testAllEq :: Text -> Property
testAllEq x =
  let
    ls = textToLayouts x
  in
    counterexample (show (Layouts ls)) (collect (length . Text.lines $ x) . (=== True) . allEq $ ls)

testAllEqNoVV :: Text -> Property
testAllEqNoVV x =
  let
    ls = textToLayoutsNoVV x
  in
    counterexample (show (Layouts ls)) (collect (length . Text.lines $ x) . (=== True) . allEq $ ls)

testDeltas :: Text -> Property
testDeltas x =
  let
    ls = textToLayouts x
  in
    counterexample (show (Layouts ls)) ((=== Right ()) . checkLayouts $ ls)

assertAllEq :: Text -> Assertion
assertAllEq t =
  let
    ls = textToLayouts t
  in
    if allEq ls
    then pure ()
    else assertFailure (show (Layouts ls))

assertAllEqTo :: Text -> Layout -> Assertion
assertAllEqTo t l =
  let
    ls = l : textToLayouts t
  in
    if allEq ls
    then pure ()
    else assertFailure (show (Layouts ls))

test_layout :: TestTree
test_layout = testGroup "layout"
  [
    testCase "F1"  $ assertAllEq exampleF1
  , testCase "F2"  $ assertAllEq exampleF2
  , testCase "F3"  $ assertAllEq exampleF3
  , testCase "F4"  $ assertAllEq exampleF4
  , testCase "F5"  $ assertAllEq exampleF5
  , testCase "F6"  $ assertAllEq exampleF6
  , testCase "F7"  $ assertAllEq exampleF7
  , testCase "F8"  $ assertAllEq exampleF8
  , testCase "F9"  $ assertAllEq exampleF9
  , testCase "F10" $ assertAllEq exampleF10
  , testCase "E1"  $ assertAllEq exampleE1
  , testCase "E2"  $ assertAllEq exampleE2
  , testCase "E3"  $ assertAllEq exampleE3
  , testCase "E4"  $ assertAllEq exampleE4
  , testCase "E5"  $ assertAllEq exampleE5
  , testCase "E6"  $ assertAllEq exampleE6
  , testCase "E7"  $ assertAllEq exampleE7
  , testCase "E8"  $ assertAllEq exampleE8
  , testCase "E9"  $ assertAllEq exampleE9
  , testCase "E10"  $ assertAllEq exampleE10
  , testCase "E11"  $ assertAllEq exampleE11
  -- , testProperty "all eq (no do, no errors)" $ testAllEq . modelLinesToText
  -- , testProperty "deltas (no do, no errors)" $ testDeltas . modelLinesToText
  -- , testProperty "all eq (with do, no errors)" $ testAllEq . modelLinesWithDoToText
  -- , testProperty "deltas (with do, no errors)" $ testDeltas . modelLinesWithDoToText
  , testProperty "all eq (no do, with errors)" $ testAllEqNoVV . modelLinesWithErrorsToText
  -- , testProperty "deltas (no do, with errors)" $ testDeltas . modelLinesWithErrorsToText
  -- , testProperty "all eq (with do, with errors)" $ testAllEqNoVV . modelLinesWithDoAndErrorsToText
  -- , testProperty "deltas (with do, with errors)" $ testDeltas . modelLinesWithDoAndErrorsToText
  ]
