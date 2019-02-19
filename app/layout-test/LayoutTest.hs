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
      in
        (trace "=== L ===" (fold ls1)) <> (trace "=== R ===" (fold ls2))
  in
    trace "=========" $ fmap f [0..length ts - 1]

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
  "      one\n\
  \\t two\n\
  \    three\n\
  \    four\n\
  \"

-- one

exampleI1E0 :: Text
exampleI1E0 =
  "   one\n\
  \"

resultI1E0 :: Layout
resultI1E0 =
  let
    pt1 = "   "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
  in
    S 6 $
      Run p1 (Cat.singleton l1) l1 Empty p1

exampleI1E1 :: Text
exampleI1E1 =
  " \t one\n\
  \"

resultI1E1 :: Layout
resultI1E1 =
  let
    pt1 = " \t "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
  in
    S 6 $
      Run p1 (Cat.singleton l1) l1 Empty p1

-- two

exampleI11E00 :: Text
exampleI11E00 =
  "   one\n\
  \   two\n\
  \"

resultI11E00 :: Layout
resultI11E00 =
  let
    pt1 = "   "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = "   "
    p2 = Prefix pt2
    l2 = rel 7 $ Lex.lex $ pt2 <> "two\n"
  in
    V 13
      Empty
      (Run p1 (Cat.singleton l1) l1 Empty p1)
      (Rev . Cat.singleton $ Run p2 (Cat.singleton l2) l2 Empty p2)

exampleI11E01 :: Text
exampleI11E01 =
  "   one\n\
  \ \t two\n\
  \"

resultI11E01 :: Layout
resultI11E01 =
  let
    pt1 = "   "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = " \t "
    p2 = Prefix pt2
    l2 = rel 7 $ Lex.lex $ pt2 <> "two\n"
  in
    V 13
      Empty
      (Run p1 (Cat.singleton l1) l1 Empty p1)
      (Rev . Cat.singleton $ Run p2 (Cat.singleton l2) l2 (Cat.singleton $ LayoutMismatch 7 p1 p2) p2)

exampleI11E10 :: Text
exampleI11E10 =
  " \t one\n\
  \   two\n\
  \"

resultI11E10 :: Layout
resultI11E10 =
  let
    pt1 = " \t "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = "   "
    p2 = Prefix pt2
    l2 = rel 7 $ Lex.lex $ pt2 <> "two\n"
  in
    V 13
      Empty
      (Run p1 (Cat.singleton l1) l1 Empty p1)
      (Rev . Cat.singleton $ Run p2 (Cat.singleton l2) l2 (Cat.singleton $ LayoutMismatch 7 p1 p2) p2)

exampleI11E11 :: Text
exampleI11E11 =
  " \t one\n\
  \ \t two\n\
  \"

resultI11E11 :: Layout
resultI11E11 =
  let
    pt1 = " \t "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = " \t "
    p2 = Prefix pt2
    l2 = rel 7 $ Lex.lex $ pt2 <> "two\n"
  in
    V 13
      Empty
      (Run p1 (Cat.singleton l1) l1 Empty p1)
      (Rev . Cat.singleton $ Run p2 (Cat.singleton l2) l2 Empty p2)

exampleI12E00 :: Text
exampleI12E00 =
  "   one\n\
  \      two\n\
  \"

resultI12E00 :: Layout
resultI12E00 =
  let
    pt1 = "   "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = "      "
    p2 = Prefix pt2
    l2 = rel 7 $ Lex.lex $ pt2 <> "two\n"
  in
    S 16 $
      Run p1 (Cat.singleton l1 <> Cat.singleton l2) (l1 <> l2) Empty p2

exampleI12E01 :: Text
exampleI12E01 =
  "   one\n\
  \ \t    two\n\
  \"

resultI12E01 :: Layout
resultI12E01 =
  let
    pt1 = "   "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = " \t    "
    p2 = Prefix pt2
    l2 = rel 7 $ Lex.lex $ pt2 <> "two\n"
  in
    V 16
      Empty
      (Run p1 (Cat.singleton l1) l1 Empty p1)
      (Rev . Cat.singleton $ Run p2 (Cat.singleton l2) l2 (Cat.singleton (LayoutMismatch 7 p1 p2)) p2)

exampleI12E02 :: Text
exampleI12E02 =
  "   one\n\
  \    \t two\n\
  \"

resultI12E02 :: Layout
resultI12E02 =
  let
    pt1 = "   "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = "    \t "
    p2 = Prefix pt2
    l2 = rel 7 $ Lex.lex $ pt2 <> "two\n"
  in
    S 16 $
      Run p1 (Cat.singleton l1 <> Cat.singleton l2) (l1 <> l2) Empty p2

exampleI12E10 :: Text
exampleI12E10 =
  " \t one\n\
  \      two\n\
  \"

resultI12E10 :: Layout
resultI12E10 =
  let
    pt1 = " \t "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = "      "
    p2 = Prefix pt2
    l2 = rel 7 $ Lex.lex $ pt2 <> "two\n"
  in
    V 16
      Empty
      (Run p1 (Cat.singleton l1) l1 Empty p1)
      (Rev . Cat.singleton $ Run p2 (Cat.singleton l2) l2 (Cat.singleton (LayoutMismatch 7 p1 p2)) p2)

exampleI12E11 :: Text
exampleI12E11 =
  " \t one\n\
  \ \t    two\n\
  \"

resultI12E11 :: Layout
resultI12E11 =
  let
    pt1 = " \t "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = " \t    "
    p2 = Prefix pt2
    l2 = rel 7 $ Lex.lex $ pt2 <> "two\n"
  in
    S 16 $
      Run p1 (Cat.singleton l1 <> Cat.singleton l2) (l1 <> l2) Empty p2

exampleI12E12 :: Text
exampleI12E12 =
  " \t one\n\
  \    \t two\n\
  \"

resultI12E12 :: Layout
resultI12E12 =
  let
    pt1 = " \t "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = "    \t "
    p2 = Prefix pt2
    l2 = rel 7 $ Lex.lex $ pt2 <> "two\n"
  in
    V 16
      Empty
      (Run p1 (Cat.singleton l1) l1 Empty p1)
      (Rev . Cat.singleton $ Run p2 (Cat.singleton l2) l2 (Cat.singleton (LayoutMismatch 7 p1 p2)) p2)

exampleI21E00 :: Text
exampleI21E00 =
  "      one\n\
  \   two\n\
  \"

resultI21E00 :: Layout
resultI21E00 =
  let
    pt1 = "      "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = "   "
    p2 = Prefix pt2
    l2 = rel 10 $ Lex.lex $ pt2 <> "two\n"
  in
    V 16
      (Cat.singleton $ Run p1 (Cat.singleton l1) l1 Empty p1)
      (Run p2 (Cat.singleton l2) l2 Empty p2)
      Empty

exampleI21E01 :: Text
exampleI21E01 =
  "      one\n\
  \ \t two\n\
  \"

resultI21E01 :: Layout
resultI21E01 =
  let
    pt1 = "      "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = " \t "
    p2 = Prefix pt2
    l2 = rel 10 $ Lex.lex $ pt2 <> "two\n"
  in
    V 16
       Empty
      (Run p1 (Cat.singleton l1) l1 Empty p1)
      (Rev . Cat.singleton $ Run p2 (Cat.singleton l2) l2 (Cat.singleton $ LayoutMismatch 10 p1 p2) p2)

exampleI21E10 :: Text
exampleI21E10 =
  " \t    one\n\
  \   two\n\
  \"

resultI21E10 :: Layout
resultI21E10 =
  let
    pt1 = " \t    "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = "   "
    p2 = Prefix pt2
    l2 = rel 10 $ Lex.lex $ pt2 <> "two\n"
  in
    V 16
       Empty
      (Run p1 (Cat.singleton l1) l1 Empty p1)
      (Rev . Cat.singleton $ Run p2 (Cat.singleton l2) l2 (Cat.singleton $ LayoutMismatch 10 p1 p2) p2)

exampleI21E11 :: Text
exampleI21E11 =
  " \t    one\n\
  \ \t two\n\
  \"

resultI21E11 :: Layout
resultI21E11 =
  let
    pt1 = " \t    "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = " \t "
    p2 = Prefix pt2
    l2 = rel 10 $ Lex.lex $ pt2 <> "two\n"
  in
    V 16
      (Cat.singleton $ Run p1 (Cat.singleton l1) l1 Empty p1)
      (Run p2 (Cat.singleton l2) l2 Empty p2)
      Empty

exampleI21E20 :: Text
exampleI21E20 =
  "    \t one\n\
  \   two\n\
  \"

resultI21E20 :: Layout
resultI21E20 =
  let
    pt1 = "    \t "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = "   "
    p2 = Prefix pt2
    l2 = rel 10 $ Lex.lex $ pt2 <> "two\n"
  in
    V 16
      (Cat.singleton $ Run p1 (Cat.singleton l1) l1 Empty p1)
      (Run p2 (Cat.singleton l2) l2 Empty p2)
       Empty

exampleI21E21 :: Text
exampleI21E21 =
  "    \t one\n\
  \ \t two\n\
  \"

resultI21E21 :: Layout
resultI21E21 =
  let
    pt1 = "    \t "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = " \t "
    p2 = Prefix pt2
    l2 = rel 10 $ Lex.lex $ pt2 <> "two\n"
  in
    V 16
       Empty
      (Run p1 (Cat.singleton l1) l1 Empty p1)
      (Rev . Cat.singleton $ Run p2 (Cat.singleton l2) l2 (Cat.singleton $ LayoutMismatch 10 p1 p2) p2)

exampleI22E00 :: Text
exampleI22E00 =
  "      one\n\
  \      two\n\
  \"

resultI22E00 :: Layout
resultI22E00 =
  let
    pt1 = "      "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = "      "
    p2 = Prefix pt2
    l2 = rel 10 $ Lex.lex $ pt2 <> "two\n"
  in
    V 19
       Empty
      (Run p1 (Cat.singleton l1) l1 Empty p1)
      (Rev . Cat.singleton $ Run p2 (Cat.singleton l2) l2 Empty p2)

exampleI22E01 :: Text
exampleI22E01 =
  "      one\n\
  \ \t    two\n\
  \"

resultI22E01 :: Layout
resultI22E01 =
  let
    pt1 = "      "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = " \t    "
    p2 = Prefix pt2
    l2 = rel 10 $ Lex.lex $ pt2 <> "two\n"
  in
    V 19
       Empty
      (Run p1 (Cat.singleton l1) l1 Empty p1)
      (Rev . Cat.singleton $ Run p2 (Cat.singleton l2) l2 (Cat.singleton $ LayoutMismatch 10 p1 p2) p2)

exampleI22E02 :: Text
exampleI22E02 =
  "      one\n\
  \    \t two\n\
  \"

resultI22E02 :: Layout
resultI22E02 =
  let
    pt1 = "      "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = "    \t "
    p2 = Prefix pt2
    l2 = rel 10 $ Lex.lex $ pt2 <> "two\n"
  in
    V 19
       Empty
      (Run p1 (Cat.singleton l1) l1 Empty p1)
      (Rev . Cat.singleton $ Run p2 (Cat.singleton l2) l2 (Cat.singleton $ LayoutMismatch 10 p1 p2) p2)

exampleI22E10 :: Text
exampleI22E10 =
  " \t    one\n\
  \      two\n\
  \"

resultI22E10 :: Layout
resultI22E10 =
  let
    pt1 = " \t    "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = "      "
    p2 = Prefix pt2
    l2 = rel 10 $ Lex.lex $ pt2 <> "two\n"
  in
    V 19
       Empty
      (Run p1 (Cat.singleton l1) l1 Empty p1)
      (Rev . Cat.singleton $ Run p2 (Cat.singleton l2) l2 (Cat.singleton $ LayoutMismatch 10 p1 p2) p2)

exampleI22E11 :: Text
exampleI22E11 =
  " \t    one\n\
  \ \t    two\n\
  \"

resultI22E11 :: Layout
resultI22E11 =
  let
    pt1 = " \t    "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = " \t    "
    p2 = Prefix pt2
    l2 = rel 10 $ Lex.lex $ pt2 <> "two\n"
  in
    V 19
       Empty
      (Run p1 (Cat.singleton l1) l1 Empty p1)
      (Rev . Cat.singleton $ Run p2 (Cat.singleton l2) l2 Empty p2)

exampleI22E12 :: Text
exampleI22E12 =
  " \t    one\n\
  \    \t two\n\
  \"

resultI22E12 :: Layout
resultI22E12 =
  let
    pt1 = " \t    "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = "    \t "
    p2 = Prefix pt2
    l2 = rel 10 $ Lex.lex $ pt2 <> "two\n"
  in
    V 19
       Empty
      (Run p1 (Cat.singleton l1) l1 Empty p1)
      (Rev . Cat.singleton $ Run p2 (Cat.singleton l2) l2 (Cat.singleton $ LayoutMismatch 10 p1 p2) p2)

exampleI22E20 :: Text
exampleI22E20 =
  "    \t one\n\
  \      two\n\
  \"

resultI22E20 :: Layout
resultI22E20 =
  let
    pt1 = "    \t "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = "      "
    p2 = Prefix pt2
    l2 = rel 10 $ Lex.lex $ pt2 <> "two\n"
  in
    V 19
       Empty
      (Run p1 (Cat.singleton l1) l1 Empty p1)
      (Rev . Cat.singleton $ Run p2 (Cat.singleton l2) l2 (Cat.singleton $ LayoutMismatch 10 p1 p2) p2)

exampleI22E21 :: Text
exampleI22E21 =
  "    \t one\n\
  \ \t    two\n\
  \"

resultI22E21 :: Layout
resultI22E21 =
  let
    pt1 = "    \t "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = " \t    "
    p2 = Prefix pt2
    l2 = rel 10 $ Lex.lex $ pt2 <> "two\n"
  in
    V 19
       Empty
      (Run p1 (Cat.singleton l1) l1 Empty p1)
      (Rev . Cat.singleton $ Run p2 (Cat.singleton l2) l2 (Cat.singleton $ LayoutMismatch 10 p1 p2) p2)

exampleI22E22 :: Text
exampleI22E22 =
  "    \t one\n\
  \    \t two\n\
  \"

resultI22E22 :: Layout
resultI22E22 =
  let
    pt1 = "    \t "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = "    \t "
    p2 = Prefix pt2
    l2 = rel 10 $ Lex.lex $ pt2 <> "two\n"
  in
    V 19
       Empty
      (Run p1 (Cat.singleton l1) l1 Empty p1)
      (Rev . Cat.singleton $ Run p2 (Cat.singleton l2) l2 Empty p2)

exampleI111E000 :: Text
exampleI111E000 =
  "   one\n\
  \   two\n\
  \   three\n\
  \"

resultI111E000 :: Layout
resultI111E000 =
  let
    pt1 = "   "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = "   "
    p2 = Prefix pt2
    l2 = rel 7 $ Lex.lex $ pt2 <> "two\n"
    pt3 = "   "
    p3 = Prefix pt3
    l3 = rel 14 $ Lex.lex $ pt3 <> "three\n"
  in
    V 22
       Empty
      (Run p1 (Cat.singleton l1) l1 Empty p1)
      ((Rev . Cat.singleton $ Run p2 (Cat.singleton l2) l2 Empty p2) <>
       (Rev . Cat.singleton $ Run p3 (Cat.singleton l3) l3 Empty p3))

exampleI111E001 :: Text
exampleI111E001 =
  "   one\n\
  \   two\n\
  \ \t three\n\
  \"

resultI111E001 :: Layout
resultI111E001 =
  let
    pt1 = "   "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = "   "
    p2 = Prefix pt2
    l2 = rel 7 $ Lex.lex $ pt2 <> "two\n"
    pt3 = " \t "
    p3 = Prefix pt3
    l3 = rel 14 $ Lex.lex $ pt3 <> "three\n"
  in
    V 22
       Empty
      (Run p1 (Cat.singleton l1) l1 Empty p1)
      ((Rev . Cat.singleton $ Run p2 (Cat.singleton l2) l2 Empty p2) <>
       (Rev . Cat.singleton $ Run p3 (Cat.singleton l3) l3 (Cat.singleton $ LayoutMismatch 14 p2 p3) p3))

exampleI111E010 :: Text
exampleI111E010 =
  "   one\n\
  \ \t two\n\
  \   three\n\
  \"

resultI111E010 :: Layout
resultI111E010 =
  let
    pt1 = "   "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = " \t "
    p2 = Prefix pt2
    l2 = rel 7 $ Lex.lex $ pt2 <> "two\n"
    pt3 = "   "
    p3 = Prefix pt3
    l3 = rel 14 $ Lex.lex $ pt3 <> "three\n"
  in
    V 22
       Empty
      (Run p1 (Cat.singleton l1) l1 Empty p1)
      ((Rev . Cat.singleton $ Run p2 (Cat.singleton l2) l2 (Cat.singleton $ LayoutMismatch 7 p1 p2) p2) <>
       (Rev . Cat.singleton $ Run p3 (Cat.singleton l3) l3 (Cat.singleton $ LayoutMismatch 14 p2 p3) p3))

exampleI111E011 :: Text
exampleI111E011 =
  "   one\n\
  \ \t two\n\
  \ \t three\n\
  \"

resultI111E011 :: Layout
resultI111E011 =
  let
    pt1 = "   "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = " \t "
    p2 = Prefix pt2
    l2 = rel 7 $ Lex.lex $ pt2 <> "two\n"
    pt3 = " \t "
    p3 = Prefix pt3
    l3 = rel 14 $ Lex.lex $ pt3 <> "three\n"
  in
    V 22
       Empty
      (Run p1 (Cat.singleton l1) l1 Empty p1)
      ((Rev . Cat.singleton $ Run p2 (Cat.singleton l2) l2 (Cat.singleton $ LayoutMismatch 7 p1 p2) p2) <>
       (Rev . Cat.singleton $ Run p3 (Cat.singleton l3) l3 Empty p3))

exampleI111E100 :: Text
exampleI111E100 =
  " \t one\n\
  \   two\n\
  \   three\n\
  \"

resultI111E100 :: Layout
resultI111E100 =
  let
    pt1 = " \t "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = "   "
    p2 = Prefix pt2
    l2 = rel 7 $ Lex.lex $ pt2 <> "two\n"
    pt3 = "   "
    p3 = Prefix pt3
    l3 = rel 14 $ Lex.lex $ pt3 <> "three\n"
  in
    V 22
       Empty
      (Run p1 (Cat.singleton l1) l1 Empty p1)
      ((Rev . Cat.singleton $ Run p2 (Cat.singleton l2) l2 (Cat.singleton $ LayoutMismatch 7 p1 p2) p2) <>
       (Rev . Cat.singleton $ Run p3 (Cat.singleton l3) l3 Empty p3))

exampleI111E101 :: Text
exampleI111E101 =
  " \t one\n\
  \   two\n\
  \ \t three\n\
  \"

resultI111E101 :: Layout
resultI111E101 =
  let
    pt1 = " \t "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = "   "
    p2 = Prefix pt2
    l2 = rel 7 $ Lex.lex $ pt2 <> "two\n"
    pt3 = " \t "
    p3 = Prefix pt3
    l3 = rel 14 $ Lex.lex $ pt3 <> "three\n"
  in
    V 22
       Empty
      (Run p1 (Cat.singleton l1) l1 Empty p1)
      ((Rev . Cat.singleton $ Run p2 (Cat.singleton l2) l2 (Cat.singleton $ LayoutMismatch 7 p1 p2) p2) <>
       (Rev . Cat.singleton $ Run p3 (Cat.singleton l3) l3 (Cat.singleton $ LayoutMismatch 14 p2 p3) p3))

exampleI111E110 :: Text
exampleI111E110 =
  " \t one\n\
  \ \t two\n\
  \   three\n\
  \"

resultI111E110 :: Layout
resultI111E110 =
  let
    pt1 = " \t "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = " \t "
    p2 = Prefix pt2
    l2 = rel 7 $ Lex.lex $ pt2 <> "two\n"
    pt3 = "   "
    p3 = Prefix pt3
    l3 = rel 14 $ Lex.lex $ pt3 <> "three\n"
  in
    V 22
       Empty
      (Run p1 (Cat.singleton l1) l1 Empty p1)
      ((Rev . Cat.singleton $ Run p2 (Cat.singleton l2) l2 Empty p2) <>
       (Rev . Cat.singleton $ Run p3 (Cat.singleton l3) l3 (Cat.singleton $ LayoutMismatch 14 p2 p3) p3))

exampleI111E111 :: Text
exampleI111E111 =
  " \t one\n\
  \ \t two\n\
  \ \t three\n\
  \"

resultI111E111 :: Layout
resultI111E111 =
  let
    pt1 = " \t "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = " \t "
    p2 = Prefix pt2
    l2 = rel 7 $ Lex.lex $ pt2 <> "two\n"
    pt3 = " \t "
    p3 = Prefix pt3
    l3 = rel 14 $ Lex.lex $ pt3 <> "three\n"
  in
    V 22
       Empty
      (Run p1 (Cat.singleton l1) l1 Empty p1)
      ((Rev . Cat.singleton $ Run p2 (Cat.singleton l2) l2 Empty p2) <>
       (Rev . Cat.singleton $ Run p3 (Cat.singleton l3) l3 Empty p3))

exampleI112E000 :: Text
exampleI112E000 =
  "   one\n\
  \   two\n\
  \      three\n\
  \"

resultI112E000 :: Layout
resultI112E000 =
  let
    pt1 = "   "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = "   "
    p2 = Prefix pt2
    l2 = rel 7 $ Lex.lex $ pt2 <> "two\n"
    pt3 = "      "
    p3 = Prefix pt3
    l3 = rel 14 $ Lex.lex $ pt3 <> "three\n"
  in
    V 25
      Empty
      (Run p1 (Cat.singleton l1) l1 Empty p1)
      (Rev . Cat.singleton $ Run p2 (Cat.singleton l2 <> Cat.singleton l3) (l2 <> l3) Empty p3)

exampleI112E001 :: Text
exampleI112E001 =
  "   one\n\
  \   two\n\
  \ \t    three\n\
  \"

resultI112E001 :: Layout
resultI112E001 =
  let
    pt1 = "   "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = "   "
    p2 = Prefix pt2
    l2 = rel 7 $ Lex.lex $ pt2 <> "two\n"
    pt3 = " \t    "
    p3 = Prefix pt3
    l3 = rel 14 $ Lex.lex $ pt3 <> "three\n"
  in
    V 25
       Empty
      (Run p1 (Cat.singleton l1) l1 Empty p1)
      ((Rev . Cat.singleton $ Run p2 (Cat.singleton l2) l2 Empty p2) <>
       (Rev . Cat.singleton $ Run p3 (Cat.singleton l3) l3 (Cat.singleton $ LayoutMismatch 14 p2 p3) p3))

exampleI112E002 :: Text
exampleI112E002 =
  "   one\n\
  \   two\n\
  \    \t three\n\
  \"

resultI112E002 :: Layout
resultI112E002 =
  let
    pt1 = "   "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = "   "
    p2 = Prefix pt2
    l2 = rel 7 $ Lex.lex $ pt2 <> "two\n"
    pt3 = "    \t "
    p3 = Prefix pt3
    l3 = rel 14 $ Lex.lex $ pt3 <> "three\n"
  in
    V 25
       Empty
      (Run p1 (Cat.singleton l1) l1 Empty p1)
      (Rev . Cat.singleton $ Run p2 (Cat.singleton l2 <> Cat.singleton l3) (l2 <> l3) Empty p3)

exampleI112E010 :: Text
exampleI112E010 =
  "   one\n\
  \ \t two\n\
  \      three\n\
  \"

resultI112E010 :: Layout
resultI112E010 =
  let
    pt1 = "   "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = " \t "
    p2 = Prefix pt2
    l2 = rel 7 $ Lex.lex $ pt2 <> "two\n"
    pt3 = "      "
    p3 = Prefix pt3
    l3 = rel 14 $ Lex.lex $ pt3 <> "three\n"
  in
    V 25
       Empty
      (Run p1 (Cat.singleton l1) l1 Empty p1)
      ((Rev . Cat.singleton $ Run p2 (Cat.singleton l2) l2 (Cat.singleton $ LayoutMismatch 7 p1 p2) p2) <>
       (Rev . Cat.singleton $ Run p3 (Cat.singleton l3) l3 (Cat.singleton $ LayoutMismatch 14 p2 p3) p3))

exampleI112E011 :: Text
exampleI112E011 =
  "   one\n\
  \ \t two\n\
  \ \t    three\n\
  \"

resultI112E011 :: Layout
resultI112E011 =
  let
    pt1 = "   "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = " \t "
    p2 = Prefix pt2
    l2 = rel 7 $ Lex.lex $ pt2 <> "two\n"
    pt3 = " \t    "
    p3 = Prefix pt3
    l3 = rel 14 $ Lex.lex $ pt3 <> "three\n"
  in
    V 25
       Empty
      (Run p1 (Cat.singleton l1) l1 Empty p1)
      (Rev . Cat.singleton $ Run p2 (Cat.singleton l2 <> Cat.singleton l3) (l2 <> l3) (Cat.singleton $ LayoutMismatch 7 p1 p2) p3)

exampleI112E012 :: Text
exampleI112E012 =
  "   one\n\
  \ \t two\n\
  \    \t three\n\
  \"

resultI112E012 :: Layout
resultI112E012 =
  let
    pt1 = "   "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = " \t "
    p2 = Prefix pt2
    l2 = rel 7 $ Lex.lex $ pt2 <> "two\n"
    pt3 = "    \t "
    p3 = Prefix pt3
    l3 = rel 14 $ Lex.lex $ pt3 <> "three\n"
  in
    V 25
       Empty
      (Run p1 (Cat.singleton l1) l1 Empty p1)
      ((Rev . Cat.singleton $ Run p2 (Cat.singleton l2) l2 (Cat.singleton $ LayoutMismatch 7 p1 p2) p2) <>
       (Rev . Cat.singleton $ Run p3 (Cat.singleton l3) l3 (Cat.singleton $ LayoutMismatch 14 p2 p3) p3))

exampleI112E100 :: Text
exampleI112E100 =
  " \t one\n\
  \   two\n\
  \      three\n\
  \"

resultI112E100 :: Layout
resultI112E100 =
  let
    pt1 = " \t "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = "   "
    p2 = Prefix pt2
    l2 = rel 7 $ Lex.lex $ pt2 <> "two\n"
    pt3 = "      "
    p3 = Prefix pt3
    l3 = rel 14 $ Lex.lex $ pt3 <> "three\n"
  in
    V 25
       Empty
      (Run p1 (Cat.singleton l1) l1 Empty p1)
      (Rev . Cat.singleton $ Run p2 (Cat.singleton l2 <> Cat.singleton l3) (l2 <> l3) (Cat.singleton $ LayoutMismatch 7 p1 p2) p3)

exampleI112E101 :: Text
exampleI112E101 =
  " \t one\n\
  \   two\n\
  \ \t    three\n\
  \"

resultI112E101 :: Layout
resultI112E101 =
  let
    pt1 = " \t "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = "   "
    p2 = Prefix pt2
    l2 = rel 7 $ Lex.lex $ pt2 <> "two\n"
    pt3 = " \t    "
    p3 = Prefix pt3
    l3 = rel 14 $ Lex.lex $ pt3 <> "three\n"
  in
    V 25
       Empty
      (Run p1 (Cat.singleton l1) l1 Empty p1)
      ((Rev . Cat.singleton $ Run p2 (Cat.singleton l2) l2 (Cat.singleton $ LayoutMismatch 7 p1 p2) p2) <>
       (Rev . Cat.singleton $ Run p3 (Cat.singleton l3) l3 (Cat.singleton $ LayoutMismatch 14 p2 p3) p3))

exampleI112E102 :: Text
exampleI112E102 =
  " \t one\n\
  \   two\n\
  \    \t three\n\
  \"

resultI112E102 :: Layout
resultI112E102 =
  let
    pt1 = " \t "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = "   "
    p2 = Prefix pt2
    l2 = rel 7 $ Lex.lex $ pt2 <> "two\n"
    pt3 = "    \t "
    p3 = Prefix pt3
    l3 = rel 14 $ Lex.lex $ pt3 <> "three\n"
  in
    V 25
       Empty
      (Run p1 (Cat.singleton l1) l1 Empty p1)
      (Rev . Cat.singleton $ Run p2 (Cat.singleton l2 <> Cat.singleton l3) (l2 <> l3) (Cat.singleton $ LayoutMismatch 7 p1 p2) p3)

exampleI112E110 :: Text
exampleI112E110 =
  " \t one\n\
  \ \t two\n\
  \      three\n\
  \"

resultI112E110 :: Layout
resultI112E110 =
  let
    pt1 = " \t "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = " \t "
    p2 = Prefix pt2
    l2 = rel 7 $ Lex.lex $ pt2 <> "two\n"
    pt3 = "      "
    p3 = Prefix pt3
    l3 = rel 14 $ Lex.lex $ pt3 <> "three\n"
  in
    V 25
       Empty
      (Run p1 (Cat.singleton l1) l1 Empty p1)
      ((Rev . Cat.singleton $ Run p2 (Cat.singleton l2) l2 Empty p2) <>
       (Rev . Cat.singleton $ Run p3 (Cat.singleton l3) l3 (Cat.singleton $ LayoutMismatch 14 p2 p3) p3))

exampleI112E111 :: Text
exampleI112E111 =
  " \t one\n\
  \ \t two\n\
  \ \t    three\n\
  \"

resultI112E111 :: Layout
resultI112E111 =
  let
    pt1 = " \t "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = " \t "
    p2 = Prefix pt2
    l2 = rel 7 $ Lex.lex $ pt2 <> "two\n"
    pt3 = " \t    "
    p3 = Prefix pt3
    l3 = rel 14 $ Lex.lex $ pt3 <> "three\n"
  in
    V 25
       Empty
      (Run p1 (Cat.singleton l1) l1 Empty p1)
      (Rev . Cat.singleton $ Run p2 (Cat.singleton l2 <> Cat.singleton l3) (l2 <> l3) Empty p3)

exampleI112E112 :: Text
exampleI112E112 =
  " \t one\n\
  \ \t two\n\
  \    \t three\n\
  \"

resultI112E112 :: Layout
resultI112E112 =
  let
    pt1 = " \t "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = " \t "
    p2 = Prefix pt2
    l2 = rel 7 $ Lex.lex $ pt2 <> "two\n"
    pt3 = "    \t "
    p3 = Prefix pt3
    l3 = rel 14 $ Lex.lex $ pt3 <> "three\n"
  in
    V 25
       Empty
      (Run p1 (Cat.singleton l1) l1 Empty p1)
      ((Rev . Cat.singleton $ Run p2 (Cat.singleton l2) l2 Empty p2) <>
       (Rev . Cat.singleton $ Run p3 (Cat.singleton l3) l3 (Cat.singleton $ LayoutMismatch 14 p2 p3) p3))

exampleI113E000 :: Text
exampleI113E000 =
  "   one\n\
  \   two\n\
  \         three\n\
  \"

resultI113E000 :: Layout
resultI113E000 =
  let
    pt1 = "   "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = "   "
    p2 = Prefix pt2
    l2 = rel 7 $ Lex.lex $ pt2 <> "two\n"
    pt3 = "         "
    p3 = Prefix pt3
    l3 = rel 14 $ Lex.lex $ pt3 <> "three\n"
  in
    V 28
       Empty
      (Run p1 (Cat.singleton l1) l1 Empty p1)
      (Rev . Cat.singleton $ Run p2 (Cat.singleton l2 <> Cat.singleton l3) (l2 <> l3) Empty p3)

exampleI113E001 :: Text
exampleI113E001 =
  "   one\n\
  \   two\n\
  \ \t       three\n\
  \"

resultI113E001 :: Layout
resultI113E001 =
  let
    pt1 = "   "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = "   "
    p2 = Prefix pt2
    l2 = rel 7 $ Lex.lex $ pt2 <> "two\n"
    pt3 = " \t       "
    p3 = Prefix pt3
    l3 = rel 14 $ Lex.lex $ pt3 <> "three\n"
  in
    V 28
       Empty
      (Run p1 (Cat.singleton l1) l1 Empty p1)
      ((Rev . Cat.singleton $ Run p2 (Cat.singleton l2) l2 Empty p2) <>
       (Rev . Cat.singleton $ Run p3 (Cat.singleton l3) l3 (Cat.singleton $ LayoutMismatch 14 p2 p3) p3))

exampleI113E002 :: Text
exampleI113E002 =
  "   one\n\
  \   two\n\
  \    \t    three\n\
  \"

resultI113E002 :: Layout
resultI113E002 =
  let
    pt1 = "   "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = "   "
    p2 = Prefix pt2
    l2 = rel 7 $ Lex.lex $ pt2 <> "two\n"
    pt3 = "    \t    "
    p3 = Prefix pt3
    l3 = rel 14 $ Lex.lex $ pt3 <> "three\n"
  in
    V 28
       Empty
      (Run p1 (Cat.singleton l1) l1 Empty p1)
      (Rev . Cat.singleton $ Run p2 (Cat.singleton l2 <> Cat.singleton l3) (l2 <> l3) Empty p3)

exampleI113E003 :: Text
exampleI113E003 =
  "   one\n\
  \   two\n\
  \       \t three\n\
  \"

resultI113E003 :: Layout
resultI113E003 =
  let
    pt1 = "   "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = "   "
    p2 = Prefix pt2
    l2 = rel 7 $ Lex.lex $ pt2 <> "two\n"
    pt3 = "       \t "
    p3 = Prefix pt3
    l3 = rel 14 $ Lex.lex $ pt3 <> "three\n"
  in
    V 28
       Empty
      (Run p1 (Cat.singleton l1) l1 Empty p1)
      (Rev . Cat.singleton $ Run p2 (Cat.singleton l2 <> Cat.singleton l3) (l2 <> l3) Empty p3)

exampleI113E010 :: Text
exampleI113E010 =
  "   one\n\
  \ \t two\n\
  \         three\n\
  \"

resultI113E010 :: Layout
resultI113E010 =
  let
    pt1 = "   "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = " \t "
    p2 = Prefix pt2
    l2 = rel 7 $ Lex.lex $ pt2 <> "two\n"
    pt3 = "         "
    p3 = Prefix pt3
    l3 = rel 14 $ Lex.lex $ pt3 <> "three\n"
  in
    V 28
       Empty
      (Run p1 (Cat.singleton l1) l1 Empty p1)
      ((Rev . Cat.singleton $ Run p2 (Cat.singleton l2) l2 (Cat.singleton $ LayoutMismatch 7 p1 p2) p2) <>
       (Rev . Cat.singleton $ Run p3 (Cat.singleton l3) l3 (Cat.singleton $ LayoutMismatch 14 p2 p3) p3))

exampleI113E011 :: Text
exampleI113E011 =
  "   one\n\
  \ \t two\n\
  \ \t       three\n\
  \"

resultI113E011 :: Layout
resultI113E011 =
  let
    pt1 = "   "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = " \t "
    p2 = Prefix pt2
    l2 = rel 7 $ Lex.lex $ pt2 <> "two\n"
    pt3 = " \t       "
    p3 = Prefix pt3
    l3 = rel 14 $ Lex.lex $ pt3 <> "three\n"
  in
    V 28
       Empty
      (Run p1 (Cat.singleton l1) l1 Empty p1)
      (Rev . Cat.singleton $ Run p2 (Cat.singleton l2 <> Cat.singleton l3) (l2 <> l3) (Cat.singleton $ LayoutMismatch 7 p1 p2) p3)

exampleI113E012 :: Text
exampleI113E012 =
  "   one\n\
  \ \t two\n\
  \    \t    three\n\
  \"

resultI113E012 :: Layout
resultI113E012 =
  let
    pt1 = "   "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = " \t "
    p2 = Prefix pt2
    l2 = rel 7 $ Lex.lex $ pt2 <> "two\n"
    pt3 = "    \t    "
    p3 = Prefix pt3
    l3 = rel 14 $ Lex.lex $ pt3 <> "three\n"
  in
    V 28
       Empty
      (Run p1 (Cat.singleton l1) l1 Empty p1)
      ((Rev . Cat.singleton $ Run p2 (Cat.singleton l2) l2 (Cat.singleton $ LayoutMismatch 7 p1 p2) p2) <>
       (Rev . Cat.singleton $ Run p3 (Cat.singleton l3) l3 (Cat.singleton $ LayoutMismatch 14 p2 p3) p3))

exampleI113E013 :: Text
exampleI113E013 =
  "   one\n\
  \ \t two\n\
  \       \t three\n\
  \"

resultI113E013 :: Layout
resultI113E013 =
  let
    pt1 = "   "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = " \t "
    p2 = Prefix pt2
    l2 = rel 7 $ Lex.lex $ pt2 <> "two\n"
    pt3 = "       \t "
    p3 = Prefix pt3
    l3 = rel 14 $ Lex.lex $ pt3 <> "three\n"
  in
    V 28
       Empty
      (Run p1 (Cat.singleton l1) l1 Empty p1)
      ((Rev . Cat.singleton $ Run p2 (Cat.singleton l2) l2 (Cat.singleton $ LayoutMismatch 7 p1 p2) p2) <>
       (Rev . Cat.singleton $ Run p3 (Cat.singleton l3) l3 (Cat.singleton $ LayoutMismatch 14 p2 p3) p3))

exampleI113E100 :: Text
exampleI113E100 =
  " \t one\n\
  \   two\n\
  \         three\n\
  \"

resultI113E100 :: Layout
resultI113E100 =
  let
    pt1 = " \t "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = "   "
    p2 = Prefix pt2
    l2 = rel 7 $ Lex.lex $ pt2 <> "two\n"
    pt3 = "         "
    p3 = Prefix pt3
    l3 = rel 14 $ Lex.lex $ pt3 <> "three\n"
  in
    V 28
       Empty
      (Run p1 (Cat.singleton l1) l1 Empty p1)
      (Rev . Cat.singleton $ Run p2 (Cat.singleton l2 <> Cat.singleton l3) (l2 <> l3) (Cat.singleton $ LayoutMismatch 7 p1 p2) p3)

exampleI113E101 :: Text
exampleI113E101 =
  " \t one\n\
  \   two\n\
  \ \t       three\n\
  \"

resultI113E101 :: Layout
resultI113E101 =
  let
    pt1 = " \t "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = "   "
    p2 = Prefix pt2
    l2 = rel 7 $ Lex.lex $ pt2 <> "two\n"
    pt3 = " \t       "
    p3 = Prefix pt3
    l3 = rel 14 $ Lex.lex $ pt3 <> "three\n"
  in
    V 28
       Empty
      (Run p1 (Cat.singleton l1) l1 Empty p1)
      ((Rev . Cat.singleton $ Run p2 (Cat.singleton l2) l2 (Cat.singleton $ LayoutMismatch 7 p1 p2) p2) <>
       (Rev . Cat.singleton $ Run p3 (Cat.singleton l3) l3 (Cat.singleton $ LayoutMismatch 14 p2 p3) p3))

exampleI113E102 :: Text
exampleI113E102 =
  " \t one\n\
  \   two\n\
  \    \t    three\n\
  \"

resultI113E102 :: Layout
resultI113E102 =
  let
    pt1 = " \t "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = "   "
    p2 = Prefix pt2
    l2 = rel 7 $ Lex.lex $ pt2 <> "two\n"
    pt3 = "    \t    "
    p3 = Prefix pt3
    l3 = rel 14 $ Lex.lex $ pt3 <> "three\n"
  in
    V 28
       Empty
      (Run p1 (Cat.singleton l1) l1 Empty p1)
      (Rev . Cat.singleton $ Run p2 (Cat.singleton l2 <> Cat.singleton l3) (l2 <> l3) (Cat.singleton $ LayoutMismatch 7 p1 p2) p3)

exampleI113E103 :: Text
exampleI113E103 =
  " \t one\n\
  \   two\n\
  \       \t three\n\
  \"

resultI113E103 :: Layout
resultI113E103 =
  let
    pt1 = " \t "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = "   "
    p2 = Prefix pt2
    l2 = rel 7 $ Lex.lex $ pt2 <> "two\n"
    pt3 = "       \t "
    p3 = Prefix pt3
    l3 = rel 14 $ Lex.lex $ pt3 <> "three\n"
  in
    V 28
       Empty
      (Run p1 (Cat.singleton l1) l1 Empty p1)
      (Rev . Cat.singleton $ Run p2 (Cat.singleton l2 <> Cat.singleton l3) (l2 <> l3) (Cat.singleton $ LayoutMismatch 7 p1 p2) p3)

exampleI113E110 :: Text
exampleI113E110 =
  " \t one\n\
  \ \t two\n\
  \         three\n\
  \"

resultI113E110 :: Layout
resultI113E110 =
  let
    pt1 = " \t "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = " \t "
    p2 = Prefix pt2
    l2 = rel 7 $ Lex.lex $ pt2 <> "two\n"
    pt3 = "         "
    p3 = Prefix pt3
    l3 = rel 14 $ Lex.lex $ pt3 <> "three\n"
  in
    V 28
       Empty
      (Run p1 (Cat.singleton l1) l1 Empty p1)
      ((Rev . Cat.singleton $ Run p2 (Cat.singleton l2) l2 Empty p2) <>
       (Rev . Cat.singleton $ Run p3 (Cat.singleton l3) l3 (Cat.singleton $ LayoutMismatch 14 p2 p3) p3))

exampleI113E111 :: Text
exampleI113E111 =
  " \t one\n\
  \ \t two\n\
  \ \t       three\n\
  \"

resultI113E111 :: Layout
resultI113E111 =
  let
    pt1 = " \t "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = " \t "
    p2 = Prefix pt2
    l2 = rel 7 $ Lex.lex $ pt2 <> "two\n"
    pt3 = " \t       "
    p3 = Prefix pt3
    l3 = rel 14 $ Lex.lex $ pt3 <> "three\n"
  in
    V 28
       Empty
      (Run p1 (Cat.singleton l1) l1 Empty p1)
      (Rev . Cat.singleton $ Run p2 (Cat.singleton l2 <> Cat.singleton l3) (l2 <> l3) Empty p3)

exampleI113E112 :: Text
exampleI113E112 =
  " \t one\n\
  \ \t two\n\
  \    \t    three\n\
  \"

resultI113E112 :: Layout
resultI113E112 =
  let
    pt1 = " \t "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = " \t "
    p2 = Prefix pt2
    l2 = rel 7 $ Lex.lex $ pt2 <> "two\n"
    pt3 = "    \t    "
    p3 = Prefix pt3
    l3 = rel 14 $ Lex.lex $ pt3 <> "three\n"
  in
    V 28
       Empty
      (Run p1 (Cat.singleton l1) l1 Empty p1)
      ((Rev . Cat.singleton $ Run p2 (Cat.singleton l2) l2 Empty p2) <>
       (Rev . Cat.singleton $ Run p3 (Cat.singleton l3) l3 (Cat.singleton $ LayoutMismatch 14 p2 p3) p3))

exampleI113E113 :: Text
exampleI113E113 =
  " \t one\n\
  \ \t two\n\
  \       \t three\n\
  \"

resultI113E113 :: Layout
resultI113E113 =
  let
    pt1 = " \t "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = " \t "
    p2 = Prefix pt2
    l2 = rel 7 $ Lex.lex $ pt2 <> "two\n"
    pt3 = "       \t "
    p3 = Prefix pt3
    l3 = rel 14 $ Lex.lex $ pt3 <> "three\n"
  in
    V 28
       Empty
      (Run p1 (Cat.singleton l1) l1 Empty p1)
      ((Rev . Cat.singleton $ Run p2 (Cat.singleton l2) l2 Empty p2) <>
       (Rev . Cat.singleton $ Run p3 (Cat.singleton l3) l3 (Cat.singleton $ LayoutMismatch 14 p2 p3) p3))

exampleI121E000 :: Text
exampleI121E000 =
  "   one\n\
  \      two\n\
  \   three\n\
  \"

resultI121E000 :: Layout
resultI121E000 = E 0

exampleI121E001 :: Text
exampleI121E001 =
  "   one\n\
  \      two\n\
  \ \t three\n\
  \"

resultI121E001 :: Layout
resultI121E001 = E 0

exampleI121E010 :: Text
exampleI121E010 =
  "   one\n\
  \ \t    two\n\
  \   three\n\
  \"

resultI121E010 :: Layout
resultI121E010 = E 0

exampleI121E011 :: Text
exampleI121E011 =
  "   one\n\
  \ \t    two\n\
  \ \t three\n\
  \"

resultI121E011 :: Layout
resultI121E011 = E 0

exampleI121E020 :: Text
exampleI121E020 =
  "   one\n\
  \    \t two\n\
  \   three\n\
  \"

resultI121E020 :: Layout
resultI121E020 = E 0

exampleI121E021 :: Text
exampleI121E021 =
  "   one\n\
  \    \t two\n\
  \ \t three\n\
  \"

resultI121E021 :: Layout
resultI121E021 = E 0

exampleI121E100 :: Text
exampleI121E100 =
  " \t one\n\
  \      two\n\
  \   three\n\
  \"

resultI121E100 :: Layout
resultI121E100 = E 0

exampleI121E101 :: Text
exampleI121E101 =
  " \t one\n\
  \      two\n\
  \ \t three\n\
  \"

resultI121E101 :: Layout
resultI121E101 = E 0

exampleI121E110 :: Text
exampleI121E110 =
  " \t one\n\
  \ \t    two\n\
  \   three\n\
  \"

resultI121E110 :: Layout
resultI121E110 = E 0

exampleI121E111 :: Text
exampleI121E111 =
  " \t one\n\
  \ \t    two\n\
  \ \t three\n\
  \"

resultI121E111 :: Layout
resultI121E111 = E 0

exampleI121E120 :: Text
exampleI121E120 =
  " \t one\n\
  \    \t two\n\
  \   three\n\
  \"

resultI121E120 :: Layout
resultI121E120 = E 0

exampleI121E121 :: Text
exampleI121E121 =
  " \t one\n\
  \    \t two\n\
  \ \t three\n\
  \"

resultI121E121 :: Layout
resultI121E121 = E 0

exampleI122E000 :: Text
exampleI122E000 =
  "   one\n\
  \      two\n\
  \      three\n\
  \"

resultI122E000 :: Layout
resultI122E000 = E 0

exampleI122E001 :: Text
exampleI122E001 =
  "   one\n\
  \      two\n\
  \ \t    three\n\
  \"

resultI122E001 :: Layout
resultI122E001 = E 0

exampleI122E002 :: Text
exampleI122E002 =
  "   one\n\
  \      two\n\
  \   \t three\n\
  \"

resultI122E002 :: Layout
resultI122E002 = E 0

exampleI122E010 :: Text
exampleI122E010 =
  "   one\n\
  \ \t    two\n\
  \      three\n\
  \"

resultI122E010 :: Layout
resultI122E010 = E 0

exampleI122E011 :: Text
exampleI122E011 =
  "   one\n\
  \ \t    two\n\
  \ \t    three\n\
  \"

resultI122E011 :: Layout
resultI122E011 = E 0

exampleI122E012 :: Text
exampleI122E012 =
  "   one\n\
  \ \t    two\n\
  \    \t three\n\
  \"

resultI122E012 :: Layout
resultI122E012 = E 0

exampleI122E020 :: Text
exampleI122E020 =
  "   one\n\
  \    \t two\n\
  \      three\n\
  \"

resultI122E020 :: Layout
resultI122E020 = E 0

exampleI122E021 :: Text
exampleI122E021 =
  "   one\n\
  \    \t two\n\
  \ \t    three\n\
  \"

resultI122E021 :: Layout
resultI122E021 = E 0

exampleI122E022 :: Text
exampleI122E022 =
  "   one\n\
  \    \t two\n\
  \    \t three\n\
  \"

resultI122E022 :: Layout
resultI122E022 = E 0

exampleI122E100 :: Text
exampleI122E100 =
  " \t one\n\
  \      two\n\
  \      three\n\
  \"

resultI122E100 :: Layout
resultI122E100 = E 0

exampleI122E101 :: Text
exampleI122E101 =
  " \t one\n\
  \      two\n\
  \ \t    three\n\
  \"

resultI122E101 :: Layout
resultI122E101 = E 0

exampleI122E102 :: Text
exampleI122E102 =
  " \t one\n\
  \      two\n\
  \    \t three\n\
  \"

resultI122E102 :: Layout
resultI122E102 = E 0

exampleI122E110 :: Text
exampleI122E110 =
  " \t one\n\
  \ \t    two\n\
  \      three\n\
  \"

resultI122E110 :: Layout
resultI122E110 = E 0

exampleI122E111 :: Text
exampleI122E111 =
  " \t one\n\
  \ \t    two\n\
  \ \t    three\n\
  \"

resultI122E111 :: Layout
resultI122E111 = E 0

exampleI122E112 :: Text
exampleI122E112 =
  " \t one\n\
  \ \t    two\n\
  \    \t three\n\
  \"

resultI122E112 :: Layout
resultI122E112 = E 0

exampleI122E120 :: Text
exampleI122E120 =
  " \t one\n\
  \    \t two\n\
  \      three\n\
  \"

resultI122E120 :: Layout
resultI122E120 = E 0

exampleI122E121 :: Text
exampleI122E121 =
  " \t one\n\
  \    \t two\n\
  \ \t    three\n\
  \"

resultI122E121 :: Layout
resultI122E121 = E 0

exampleI122E122 :: Text
exampleI122E122 =
  " \t one\n\
  \    \t two\n\
  \    \t three\n\
  \"

resultI122E122 :: Layout
resultI122E122 = E 0

exampleI123E000 :: Text
exampleI123E000 =
  "   one\n\
  \      two\n\
  \         three\n\
  \"

resultI123E000 :: Layout
resultI123E000 = E 0

exampleI123E001 :: Text
exampleI123E001 =
  "   one\n\
  \      two\n\
  \ \t       three\n\
  \"

resultI123E001 :: Layout
resultI123E001 = E 0

exampleI123E002 :: Text
exampleI123E002 =
  "   one\n\
  \      two\n\
  \    \t    three\n\
  \"

resultI123E002 :: Layout
resultI123E002 = E 0

exampleI123E003 :: Text
exampleI123E003 =
  "   one\n\
  \      two\n\
  \       \t three\n\
  \"

resultI123E003 :: Layout
resultI123E003 = E 0

exampleI123E010 :: Text
exampleI123E010 =
  "   one\n\
  \ \t    two\n\
  \         three\n\
  \"

resultI123E010 :: Layout
resultI123E010 = E 0

exampleI123E011 :: Text
exampleI123E011 =
  "   one\n\
  \ \t    two\n\
  \ \t       three\n\
  \"

resultI123E011 :: Layout
resultI123E011 = E 0

exampleI123E012 :: Text
exampleI123E012 =
  "   one\n\
  \ \t    two\n\
  \    \t    three\n\
  \"

resultI123E012 :: Layout
resultI123E012 = E 0

exampleI123E013 :: Text
exampleI123E013 =
  "   one\n\
  \ \t    two\n\
  \       \t three\n\
  \"

resultI123E013 :: Layout
resultI123E013 = E 0

exampleI123E020 :: Text
exampleI123E020 =
  "   one\n\
  \    \t two\n\
  \         three\n\
  \"

resultI123E020 :: Layout
resultI123E020 = E 0

exampleI123E021 :: Text
exampleI123E021 =
  "   one\n\
  \    \t two\n\
  \ \t       three\n\
  \"

resultI123E021 :: Layout
resultI123E021 = E 0

exampleI123E022 :: Text
exampleI123E022 =
  "   one\n\
  \    \t two\n\
  \    \t    three\n\
  \"

resultI123E022 :: Layout
resultI123E022 = E 0

exampleI123E023 :: Text
exampleI123E023 =
  "   one\n\
  \    \t two\n\
  \       \t three\n\
  \"

resultI123E023 :: Layout
resultI123E023 = E 0

exampleI123E100 :: Text
exampleI123E100 =
  " \t one\n\
  \      two\n\
  \         three\n\
  \"

resultI123E100 :: Layout
resultI123E100 = E 0

exampleI123E101 :: Text
exampleI123E101 =
  " \t one\n\
  \      two\n\
  \ \t       three\n\
  \"

resultI123E101 :: Layout
resultI123E101 = E 0

exampleI123E102 :: Text
exampleI123E102 =
  " \t one\n\
  \      two\n\
  \    \t    three\n\
  \"

resultI123E102 :: Layout
resultI123E102 = E 0

exampleI123E103 :: Text
exampleI123E103 =
  " \t one\n\
  \      two\n\
  \       \t three\n\
  \"

resultI123E103 :: Layout
resultI123E103 = E 0

exampleI123E110 :: Text
exampleI123E110 =
  " \t one\n\
  \ \t    two\n\
  \         three\n\
  \"

resultI123E110 :: Layout
resultI123E110 = E 0

exampleI123E111 :: Text
exampleI123E111 =
  " \t one\n\
  \ \t    two\n\
  \ \t       three\n\
  \"

resultI123E111 :: Layout
resultI123E111 = E 0

exampleI123E112 :: Text
exampleI123E112 =
  " \t one\n\
  \ \t    two\n\
  \    \t    three\n\
  \"

resultI123E112 :: Layout
resultI123E112 = E 0

exampleI123E113 :: Text
exampleI123E113 =
  " \t one\n\
  \ \t    two\n\
  \       \t three\n\
  \"

resultI123E113 :: Layout
resultI123E113 = E 0

exampleI123E120 :: Text
exampleI123E120 =
  " \t one\n\
  \    \t two\n\
  \         three\n\
  \"

resultI123E120 :: Layout
resultI123E120 = E 0

exampleI123E121 :: Text
exampleI123E121 =
  " \t one\n\
  \    \t two\n\
  \ \t       three\n\
  \"

resultI123E121 :: Layout
resultI123E121 = E 0

exampleI123E122 :: Text
exampleI123E122 =
  " \t one\n\
  \    \t two\n\
  \    \t    three\n\
  \"

resultI123E122 :: Layout
resultI123E122 = E 0

exampleI123E123 :: Text
exampleI123E123 =
  " \t one\n\
  \    \t two\n\
  \       \t three\n\
  \"

resultI123E123 :: Layout
resultI123E123 = E 0

exampleI131E000 :: Text
exampleI131E000 =
  "   one\n\
  \         two\n\
  \   three\n\
  \"

resultI131E000 :: Layout
resultI131E000 = E 0

exampleI131E001 :: Text
exampleI131E001 =
  "   one\n\
  \         two\n\
  \ \t three\n\
  \"

resultI131E001 :: Layout
resultI131E001 = E 0

exampleI131E010 :: Text
exampleI131E010 =
  "   one\n\
  \ \t       two\n\
  \   three\n\
  \"

resultI131E010 :: Layout
resultI131E010 = E 0

exampleI131E011 :: Text
exampleI131E011 =
  "   one\n\
  \ \t       two\n\
  \ \t three\n\
  \"

resultI131E011 :: Layout
resultI131E011 = E 0

exampleI131E020 :: Text
exampleI131E020 =
  "   one\n\
  \    \t    two\n\
  \   three\n\
  \"

resultI131E020 :: Layout
resultI131E020 = E 0

exampleI131E021 :: Text
exampleI131E021 =
  "   one\n\
  \    \t    two\n\
  \ \t three\n\
  \"

resultI131E021 :: Layout
resultI131E021 = E 0

exampleI131E030 :: Text
exampleI131E030 =
  "   one\n\
  \       \t two\n\
  \   three\n\
  \"

resultI131E030 :: Layout
resultI131E030 = E 0

exampleI131E031 :: Text
exampleI131E031 =
  "   one\n\
  \       \t two\n\
  \ \t three\n\
  \"

resultI131E031 :: Layout
resultI131E031 = E 0

exampleI131E100 :: Text
exampleI131E100 =
  " \t one\n\
  \         two\n\
  \   three\n\
  \"

resultI131E100 :: Layout
resultI131E100 = E 0

exampleI131E101 :: Text
exampleI131E101 =
  " \t one\n\
  \         two\n\
  \ \t three\n\
  \"

resultI131E101 :: Layout
resultI131E101 = E 0

exampleI131E110 :: Text
exampleI131E110 =
  " \t one\n\
  \ \t       two\n\
  \   three\n\
  \"

resultI131E110 :: Layout
resultI131E110 = E 0

exampleI131E111 :: Text
exampleI131E111 =
  " \t one\n\
  \ \t       two\n\
  \ \t three\n\
  \"

resultI131E111 :: Layout
resultI131E111 = E 0

exampleI131E120 :: Text
exampleI131E120 =
  " \t one\n\
  \    \t    two\n\
  \   three\n\
  \"

resultI131E120 :: Layout
resultI131E120 = E 0

exampleI131E121 :: Text
exampleI131E121 =
  " \t one\n\
  \    \t    two\n\
  \ \t three\n\
  \"

resultI131E121 :: Layout
resultI131E121 = E 0

exampleI131E130 :: Text
exampleI131E130 =
  " \t one\n\
  \       \t two\n\
  \   three\n\
  \"

resultI131E130 :: Layout
resultI131E130 = E 0

exampleI131E131 :: Text
exampleI131E131 =
  " \t one\n\
  \       \t two\n\
  \ \t three\n\
  \"
resultI131E131 :: Layout
resultI131E131 = E 0


exampleI132E000 :: Text
exampleI132E000 =
  "   one\n\
  \         two\n\
  \      three\n\
  \"

resultI132E000 :: Layout
resultI132E000 = E 0

exampleI132E001 :: Text
exampleI132E001 =
  "   one\n\
  \         two\n\
  \ \t    three\n\
  \"

resultI132E001 :: Layout
resultI132E001 = E 0

exampleI132E002 :: Text
exampleI132E002 =
  "   one\n\
  \         two\n\
  \    \t three\n\
  \"

resultI132E002 :: Layout
resultI132E002 = E 0

exampleI132E010 :: Text
exampleI132E010 =
  "   one\n\
  \ \t       two\n\
  \      three\n\
  \"

resultI132E010 :: Layout
resultI132E010 = E 0

exampleI132E011 :: Text
exampleI132E011 =
  "   one\n\
  \ \t       two\n\
  \ \t    three\n\
  \"

resultI132E011 :: Layout
resultI132E011 = E 0

exampleI132E012 :: Text
exampleI132E012 =
  "   one\n\
  \ \t       two\n\
  \    \t three\n\
  \"

resultI132E012 :: Layout
resultI132E012 = E 0

exampleI132E020 :: Text
exampleI132E020 =
  "   one\n\
  \    \t    two\n\
  \      three\n\
  \"

resultI132E020 :: Layout
resultI132E020 = E 0

exampleI132E021 :: Text
exampleI132E021 =
  "   one\n\
  \    \t    two\n\
  \ \t    three\n\
  \"

resultI132E021 :: Layout
resultI132E021 = E 0

exampleI132E022 :: Text
exampleI132E022 =
  "   one\n\
  \    \t    two\n\
  \    \t three\n\
  \"

resultI132E022 :: Layout
resultI132E022 = E 0

exampleI132E030 :: Text
exampleI132E030 =
  "   one\n\
  \       \t two\n\
  \      three\n\
  \"

resultI132E030 :: Layout
resultI132E030 = E 0

exampleI132E031 :: Text
exampleI132E031 =
  "   one\n\
  \       \t two\n\
  \ \t    three\n\
  \"

resultI132E031 :: Layout
resultI132E031 = E 0

exampleI132E032 :: Text
exampleI132E032 =
  "   one\n\
  \       \t two\n\
  \    \t three\n\
  \"

resultI132E032 :: Layout
resultI132E032 = E 0

exampleI132E100 :: Text
exampleI132E100 =
  " \t one\n\
  \         two\n\
  \      three\n\
  \"

resultI132E100 :: Layout
resultI132E100 = E 0

exampleI132E101 :: Text
exampleI132E101 =
  " \t one\n\
  \         two\n\
  \ \t    three\n\
  \"

resultI132E101 :: Layout
resultI132E101 = E 0

exampleI132E102 :: Text
exampleI132E102 =
  " \t one\n\
  \         two\n\
  \    \t three\n\
  \"

resultI132E102 :: Layout
resultI132E102 = E 0

exampleI132E110 :: Text
exampleI132E110 =
  " \t one\n\
  \ \t       two\n\
  \      three\n\
  \"

resultI132E110 :: Layout
resultI132E110 = E 0

exampleI132E111 :: Text
exampleI132E111 =
  " \t one\n\
  \ \t       two\n\
  \ \t    three\n\
  \"

resultI132E111 :: Layout
resultI132E111 = E 0

exampleI132E112 :: Text
exampleI132E112 =
  " \t one\n\
  \ \t       two\n\
  \    \t three\n\
  \"

resultI132E112 :: Layout
resultI132E112 = E 0

exampleI132E120 :: Text
exampleI132E120 =
  " \t one\n\
  \    \t    two\n\
  \      three\n\
  \"

resultI132E120 :: Layout
resultI132E120 = E 0

exampleI132E121 :: Text
exampleI132E121 =
  " \t one\n\
  \    \t    two\n\
  \ \t    three\n\
  \"

resultI132E121 :: Layout
resultI132E121 = E 0

exampleI132E122 :: Text
exampleI132E122 =
  " \t one\n\
  \    \t    two\n\
  \    \t three\n\
  \"

resultI132E122 :: Layout
resultI132E122 = E 0

exampleI132E130 :: Text
exampleI132E130 =
  " \t one\n\
  \       \t two\n\
  \      three\n\
  \"

resultI132E130 :: Layout
resultI132E130 = E 0

exampleI132E131 :: Text
exampleI132E131 =
  " \t one\n\
  \       \t two\n\
  \ \t    three\n\
  \"

resultI132E131 :: Layout
resultI132E131 = E 0

exampleI132E132 :: Text
exampleI132E132 =
  " \t one\n\
  \       \t two\n\
  \    \t three\n\
  \"

resultI132E132 :: Layout
resultI132E132 = E 0

exampleI133E000 :: Text
exampleI133E000 =
  "   one\n\
  \         two\n\
  \         three\n\
  \"

resultI133E000 :: Layout
resultI133E000 = E 0

exampleI133E001 :: Text
exampleI133E001 =
  "   one\n\
  \         two\n\
  \ \t       three\n\
  \"

resultI133E001 :: Layout
resultI133E001 = E 0

exampleI133E002 :: Text
exampleI133E002 =
  "   one\n\
  \         two\n\
  \    \t    three\n\
  \"

resultI133E002 :: Layout
resultI133E002 = E 0

exampleI133E003 :: Text
exampleI133E003 =
  "   one\n\
  \         two\n\
  \       \t three\n\
  \"

resultI133E003 :: Layout
resultI133E003 = E 0

exampleI133E010 :: Text
exampleI133E010 =
  "   one\n\
  \ \t       two\n\
  \         three\n\
  \"

resultI133E010 :: Layout
resultI133E010 = E 0

exampleI133E011 :: Text
exampleI133E011 =
  "   one\n\
  \ \t       two\n\
  \ \t       three\n\
  \"

resultI133E011 :: Layout
resultI133E011 = E 0

exampleI133E012 :: Text
exampleI133E012 =
  "   one\n\
  \ \t       two\n\
  \    \t    three\n\
  \"

resultI133E012 :: Layout
resultI133E012 = E 0

exampleI133E013 :: Text
exampleI133E013 =
  "   one\n\
  \ \t       two\n\
  \       \t three\n\
  \"

resultI133E013 :: Layout
resultI133E013 = E 0

exampleI133E020 :: Text
exampleI133E020 =
  "   one\n\
  \    \t    two\n\
  \         three\n\
  \"

resultI133E020 :: Layout
resultI133E020 = E 0

exampleI133E021 :: Text
exampleI133E021 =
  "   one\n\
  \    \t    two\n\
  \ \t       three\n\
  \"

resultI133E021 :: Layout
resultI133E021 = E 0

exampleI133E022 :: Text
exampleI133E022 =
  "   one\n\
  \    \t    two\n\
  \    \t    three\n\
  \"

resultI133E022 :: Layout
resultI133E022 = E 0

exampleI133E023 :: Text
exampleI133E023 =
  "   one\n\
  \    \t    two\n\
  \       \t three\n\
  \"

resultI133E023 :: Layout
resultI133E023 = E 0

exampleI133E030 :: Text
exampleI133E030 =
  "   one\n\
  \       \t two\n\
  \         three\n\
  \"

resultI133E030 :: Layout
resultI133E030 = E 0

exampleI133E031 :: Text
exampleI133E031 =
  "   one\n\
  \       \t two\n\
  \ \t       three\n\
  \"

resultI133E031 :: Layout
resultI133E031 = E 0

exampleI133E032 :: Text
exampleI133E032 =
  "   one\n\
  \       \t two\n\
  \    \t    three\n\
  \"

resultI133E032 :: Layout
resultI133E032 = E 0

exampleI133E033 :: Text
exampleI133E033 =
  "   one\n\
  \       \t two\n\
  \       \t three\n\
  \"

resultI133E033 :: Layout
resultI133E033 = E 0

exampleI133E100 :: Text
exampleI133E100 =
  " \t one\n\
  \         two\n\
  \         three\n\
  \"

resultI133E100 :: Layout
resultI133E100 = E 0

exampleI133E101 :: Text
exampleI133E101 =
  " \t one\n\
  \         two\n\
  \ \t       three\n\
  \"

resultI133E101 :: Layout
resultI133E101 = E 0

exampleI133E102 :: Text
exampleI133E102 =
  " \t one\n\
  \         two\n\
  \    \t    three\n\
  \"

resultI133E102 :: Layout
resultI133E102 = E 0

exampleI133E103 :: Text
exampleI133E103 =
  " \t one\n\
  \         two\n\
  \       \t three\n\
  \"

resultI133E103 :: Layout
resultI133E103 = E 0

exampleI133E110 :: Text
exampleI133E110 =
  " \t one\n\
  \ \t       two\n\
  \         three\n\
  \"

resultI133E110 :: Layout
resultI133E110 = E 0

exampleI133E111 :: Text
exampleI133E111 =
  " \t one\n\
  \ \t       two\n\
  \ \t       three\n\
  \"

resultI133E111 :: Layout
resultI133E111 = E 0

exampleI133E112 :: Text
exampleI133E112 =
  " \t one\n\
  \ \t       two\n\
  \    \t    three\n\
  \"

resultI133E112 :: Layout
resultI133E112 = E 0

exampleI133E113 :: Text
exampleI133E113 =
  " \t one\n\
  \ \t       two\n\
  \       \t three\n\
  \"

resultI133E113 :: Layout
resultI133E113 = E 0

exampleI133E120 :: Text
exampleI133E120 =
  " \t one\n\
  \    \t    two\n\
  \         three\n\
  \"

resultI133E120 :: Layout
resultI133E120 = E 0

exampleI133E121 :: Text
exampleI133E121 =
  " \t one\n\
  \    \t    two\n\
  \ \t       three\n\
  \"

resultI133E121 :: Layout
resultI133E121 = E 0

exampleI133E122 :: Text
exampleI133E122 =
  " \t one\n\
  \    \t    two\n\
  \    \t    three\n\
  \"

resultI133E122 :: Layout
resultI133E122 = E 0

exampleI133E123 :: Text
exampleI133E123 =
  " \t one\n\
  \    \t    two\n\
  \       \t three\n\
  \"

resultI133E123 :: Layout
resultI133E123 = E 0

exampleI133E130 :: Text
exampleI133E130 =
  " \t one\n\
  \       \t two\n\
  \         three\n\
  \"

resultI133E130 :: Layout
resultI133E130 = E 0

exampleI133E131 :: Text
exampleI133E131 =
  " \t one\n\
  \       \t two\n\
  \ \t       three\n\
  \"

resultI133E131 :: Layout
resultI133E131 = E 0

exampleI133E132 :: Text
exampleI133E132 =
  " \t one\n\
  \       \t two\n\
  \    \t    three\n\
  \"

resultI133E132 :: Layout
resultI133E132 = E 0

exampleI133E133 :: Text
exampleI133E133 =
  " \t one\n\
  \       \t two\n\
  \       \t three\n\
  \"

resultI133E133 :: Layout
resultI133E133 = E 0

exampleI211E000 :: Text
exampleI211E000 =
  "      one\n\
  \   two\n\
  \   three\n\
  \"

resultI211E000 :: Layout
resultI211E000 = E 0

exampleI211E001 :: Text
exampleI211E001 =
  "      one\n\
  \   two\n\
  \ \t three\n\
  \"

resultI211E001 :: Layout
resultI211E001 = E 0

exampleI211E010 :: Text
exampleI211E010 =
  "      one\n\
  \ \t two\n\
  \   three\n\
  \"

resultI211E010 :: Layout
resultI211E010 = E 0

exampleI211E011 :: Text
exampleI211E011 =
  "      one\n\
  \ \t two\n\
  \ \t three\n\
  \"

resultI211E011 :: Layout
resultI211E011 = E 0

exampleI211E100 :: Text
exampleI211E100 =
  " \t    one\n\
  \   two\n\
  \   three\n\
  \"

resultI211E100 :: Layout
resultI211E100 = E 0

exampleI211E101 :: Text
exampleI211E101 =
  " \t    one\n\
  \   two\n\
  \ \t three\n\
  \"

resultI211E101 :: Layout
resultI211E101 = E 0

exampleI211E110 :: Text
exampleI211E110 =
  " \t    one\n\
  \ \t two\n\
  \   three\n\
  \"

resultI211E110 :: Layout
resultI211E110 = E 0

exampleI211E111 :: Text
exampleI211E111 =
  " \t    one\n\
  \ \t two\n\
  \ \t three\n\
  \"

resultI211E111 :: Layout
resultI211E111 = E 0

exampleI211E200 :: Text
exampleI211E200 =
  "    \t one\n\
  \   two\n\
  \   three\n\
  \"

resultI211E200 :: Layout
resultI211E200 = E 0

exampleI211E201 :: Text
exampleI211E201 =
  "    \t one\n\
  \   two\n\
  \ \t three\n\
  \"

resultI211E201 :: Layout
resultI211E201 = E 0

exampleI211E210 :: Text
exampleI211E210 =
  "    \t one\n\
  \ \t two\n\
  \   three\n\
  \"

resultI211E210 :: Layout
resultI211E210 = E 0

exampleI211E211 :: Text
exampleI211E211 =
  "    \t one\n\
  \ \t two\n\
  \ \t three\n\
  \"

resultI211E211 :: Layout
resultI211E211 = E 0

exampleI212E000 :: Text
exampleI212E000 =
  "      one\n\
  \   two\n\
  \      three\n\
  \"

resultI212E000 :: Layout
resultI212E000 = E 0

exampleI212E001 :: Text
exampleI212E001 =
  "      one\n\
  \   two\n\
  \ \t    three\n\
  \"

resultI212E001 :: Layout
resultI212E001 = E 0

exampleI212E002 :: Text
exampleI212E002 =
  "      one\n\
  \   two\n\
  \    \t three\n\
  \"

resultI212E002 :: Layout
resultI212E002 = E 0

exampleI212E010 :: Text
exampleI212E010 =
  "      one\n\
  \ \t two\n\
  \      three\n\
  \"

resultI212E010 :: Layout
resultI212E010 = E 0

exampleI212E011 :: Text
exampleI212E011 =
  "      one\n\
  \ \t two\n\
  \ \t    three\n\
  \"

resultI212E011 :: Layout
resultI212E011 = E 0

exampleI212E012 :: Text
exampleI212E012 =
  "      one\n\
  \ \t two\n\
  \    \t three\n\
  \"

resultI212E012 :: Layout
resultI212E012 = E 0

exampleI212E100 :: Text
exampleI212E100 =
  " \t    one\n\
  \   two\n\
  \      three\n\
  \"

resultI212E100 :: Layout
resultI212E100 = E 0

exampleI212E101 :: Text
exampleI212E101 =
  " \t    one\n\
  \   two\n\
  \ \t    three\n\
  \"

resultI212E101 :: Layout
resultI212E101 = E 0

exampleI212E102 :: Text
exampleI212E102 =
  " \t    one\n\
  \   two\n\
  \    \t three\n\
  \"

resultI212E102 :: Layout
resultI212E102 = E 0

exampleI212E110 :: Text
exampleI212E110 =
  " \t    one\n\
  \ \t two\n\
  \      three\n\
  \"

resultI212E110 :: Layout
resultI212E110 = E 0

exampleI212E111 :: Text
exampleI212E111 =
  " \t    one\n\
  \ \t two\n\
  \ \t    three\n\
  \"

resultI212E111 :: Layout
resultI212E111 = E 0

exampleI212E112 :: Text
exampleI212E112 =
  " \t    one\n\
  \ \t two\n\
  \    \t three\n\
  \"

resultI212E112 :: Layout
resultI212E112 = E 0

exampleI212E200 :: Text
exampleI212E200 =
  "    \t one\n\
  \   two\n\
  \      three\n\
  \"

resultI212E200 :: Layout
resultI212E200 = E 0

exampleI212E201 :: Text
exampleI212E201 =
  "    \t one\n\
  \   two\n\
  \ \t    three\n\
  \"

resultI212E201 :: Layout
resultI212E201 = E 0

exampleI212E202 :: Text
exampleI212E202 =
  "    \t one\n\
  \   two\n\
  \    \t three\n\
  \"

resultI212E202 :: Layout
resultI212E202 = E 0

exampleI212E210 :: Text
exampleI212E210 =
  "    \t one\n\
  \ \t two\n\
  \      three\n\
  \"

resultI212E210 :: Layout
resultI212E210 = E 0

exampleI212E211 :: Text
exampleI212E211 =
  "    \t one\n\
  \ \t two\n\
  \ \t    three\n\
  \"

resultI212E211 :: Layout
resultI212E211 = E 0

exampleI212E212 :: Text
exampleI212E212 =
  "    \t one\n\
  \ \t two\n\
  \    \t three\n\
  \"

resultI212E212 :: Layout
resultI212E212 = E 0

exampleI213E000 :: Text
exampleI213E000 =
  "      one\n\
  \   two\n\
  \         three\n\
  \"

resultI213E000 :: Layout
resultI213E000 = E 0

exampleI213E001 :: Text
exampleI213E001 =
  "      one\n\
  \   two\n\
  \ \t       three\n\
  \"

resultI213E001 :: Layout
resultI213E001 = E 0

exampleI213E002 :: Text
exampleI213E002 =
  "      one\n\
  \   two\n\
  \    \t    three\n\
  \"

resultI213E002 :: Layout
resultI213E002 = E 0

exampleI213E003 :: Text
exampleI213E003 =
  "      one\n\
  \   two\n\
  \       \t three\n\
  \"

resultI213E003 :: Layout
resultI213E003 = E 0

exampleI213E010 :: Text
exampleI213E010 =
  "      one\n\
  \ \t two\n\
  \         three\n\
  \"

resultI213E010 :: Layout
resultI213E010 = E 0

exampleI213E011 :: Text
exampleI213E011 =
  "      one\n\
  \ \t two\n\
  \ \t       three\n\
  \"

resultI213E011 :: Layout
resultI213E011 = E 0

exampleI213E012 :: Text
exampleI213E012 =
  "      one\n\
  \ \t two\n\
  \    \t    three\n\
  \"

resultI213E012 :: Layout
resultI213E012 = E 0

exampleI213E013 :: Text
exampleI213E013 =
  "      one\n\
  \ \t two\n\
  \       \t three\n\
  \"

resultI213E013 :: Layout
resultI213E013 = E 0

exampleI213E100 :: Text
exampleI213E100 =
  " \t    one\n\
  \   two\n\
  \         three\n\
  \"

resultI213E100 :: Layout
resultI213E100 = E 0

exampleI213E101 :: Text
exampleI213E101 =
  " \t    one\n\
  \   two\n\
  \ \t       three\n\
  \"

resultI213E101 :: Layout
resultI213E101 = E 0

exampleI213E102 :: Text
exampleI213E102 =
  " \t    one\n\
  \   two\n\
  \    \t    three\n\
  \"

resultI213E102 :: Layout
resultI213E102 = E 0

exampleI213E103 :: Text
exampleI213E103 =
  " \t    one\n\
  \   two\n\
  \       \t three\n\
  \"

resultI213E103 :: Layout
resultI213E103 = E 0

exampleI213E110 :: Text
exampleI213E110 =
  " \t    one\n\
  \ \t two\n\
  \         three\n\
  \"

resultI213E110 :: Layout
resultI213E110 = E 0

exampleI213E111 :: Text
exampleI213E111 =
  " \t    one\n\
  \ \t two\n\
  \ \t       three\n\
  \"

resultI213E111 :: Layout
resultI213E111 = E 0

exampleI213E112 :: Text
exampleI213E112 =
  " \t    one\n\
  \ \t two\n\
  \    \t    three\n\
  \"

resultI213E112 :: Layout
resultI213E112 = E 0

exampleI213E113 :: Text
exampleI213E113 =
  " \t    one\n\
  \ \t two\n\
  \       \t three\n\
  \"

resultI213E113 :: Layout
resultI213E113 = E 0

exampleI213E200 :: Text
exampleI213E200 =
  "    \t one\n\
  \   two\n\
  \         three\n\
  \"

resultI213E200 :: Layout
resultI213E200 = E 0

exampleI213E201 :: Text
exampleI213E201 =
  "    \t one\n\
  \   two\n\
  \ \t       three\n\
  \"

resultI213E201 :: Layout
resultI213E201 = E 0

exampleI213E202 :: Text
exampleI213E202 =
  "    \t one\n\
  \   two\n\
  \    \t    three\n\
  \"

resultI213E202 :: Layout
resultI213E202 = E 0

exampleI213E203 :: Text
exampleI213E203 =
  "    \t one\n\
  \   two\n\
  \       \t three\n\
  \"

resultI213E203 :: Layout
resultI213E203 = E 0

exampleI213E210 :: Text
exampleI213E210 =
  "    \t one\n\
  \ \t two\n\
  \         three\n\
  \"

resultI213E210 :: Layout
resultI213E210 = E 0

exampleI213E211 :: Text
exampleI213E211 =
  "    \t one\n\
  \ \t two\n\
  \ \t       three\n\
  \"

resultI213E211 :: Layout
resultI213E211 = E 0

exampleI213E212 :: Text
exampleI213E212 =
  "    \t one\n\
  \ \t two\n\
  \    \t    three\n\
  \"

resultI213E212 :: Layout
resultI213E212 = E 0

exampleI213E213 :: Text
exampleI213E213 =
  "    \t one\n\
  \ \t two\n\
  \       \t three\n\
  \"

resultI213E213 :: Layout
resultI213E213 = E 0

exampleI221E000 :: Text
exampleI221E000 =
  "      one\n\
  \      two\n\
  \   three\n\
  \"

resultI221E000 :: Layout
resultI221E000 = E 0

exampleI221E001 :: Text
exampleI221E001 =
  "      one\n\
  \      two\n\
  \ \t three\n\
  \"

resultI221E001 :: Layout
resultI221E001 = E 0

exampleI221E010 :: Text
exampleI221E010 =
  "      one\n\
  \ \t    two\n\
  \   three\n\
  \"

resultI221E010 :: Layout
resultI221E010 = E 0

exampleI221E011 :: Text
exampleI221E011 =
  "      one\n\
  \ \t    two\n\
  \ \t three\n\
  \"

resultI221E011 :: Layout
resultI221E011 = E 0

exampleI221E020 :: Text
exampleI221E020 =
  "      one\n\
  \    \t two\n\
  \   three\n\
  \"

resultI221E020 :: Layout
resultI221E020 = E 0

exampleI221E021 :: Text
exampleI221E021 =
  "      one\n\
  \    \t two\n\
  \ \t three\n\
  \"

resultI221E021 :: Layout
resultI221E021 = E 0

exampleI221E100 :: Text
exampleI221E100 =
  " \t    one\n\
  \      two\n\
  \   three\n\
  \"

resultI221E100 :: Layout
resultI221E100 = E 0

exampleI221E101 :: Text
exampleI221E101 =
  " \t    one\n\
  \      two\n\
  \ \t three\n\
  \"

resultI221E101 :: Layout
resultI221E101 = E 0

exampleI221E110 :: Text
exampleI221E110 =
  " \t    one\n\
  \ \t    two\n\
  \   three\n\
  \"

resultI221E110 :: Layout
resultI221E110 = E 0

exampleI221E111 :: Text
exampleI221E111 =
  " \t    one\n\
  \ \t    two\n\
  \ \t three\n\
  \"

resultI221E111 :: Layout
resultI221E111 = E 0

exampleI221E120 :: Text
exampleI221E120 =
  " \t    one\n\
  \    \t two\n\
  \   three\n\
  \"

resultI221E120 :: Layout
resultI221E120 = E 0

exampleI221E121 :: Text
exampleI221E121 =
  " \t    one\n\
  \    \t two\n\
  \ \t three\n\
  \"

resultI221E121 :: Layout
resultI221E121 = E 0

exampleI221E200 :: Text
exampleI221E200 =
  "    \t one\n\
  \      two\n\
  \   three\n\
  \"

resultI221E200 :: Layout
resultI221E200 = E 0

exampleI221E201 :: Text
exampleI221E201 =
  "    \t one\n\
  \      two\n\
  \ \t three\n\
  \"

resultI221E201 :: Layout
resultI221E201 = E 0

exampleI221E210 :: Text
exampleI221E210 =
  "    \t one\n\
  \ \t    two\n\
  \   three\n\
  \"

resultI221E210 :: Layout
resultI221E210 = E 0

exampleI221E211 :: Text
exampleI221E211 =
  "    \t one\n\
  \ \t    two\n\
  \ \t three\n\
  \"

resultI221E211 :: Layout
resultI221E211 = E 0

exampleI221E220 :: Text
exampleI221E220 =
  "    \t one\n\
  \    \t two\n\
  \   three\n\
  \"

resultI221E220 :: Layout
resultI221E220 = E 0

exampleI221E221 :: Text
exampleI221E221 =
  "    \t one\n\
  \    \t two\n\
  \ \t three\n\
  \"

resultI221E221 :: Layout
resultI221E221 = E 0

exampleI222E000 :: Text
exampleI222E000 =
  "      one\n\
  \      two\n\
  \      three\n\
  \"

resultI222E000 :: Layout
resultI222E000 = E 0

exampleI222E001 :: Text
exampleI222E001 =
  "      one\n\
  \      two\n\
  \ \t    three\n\
  \"

resultI222E001 :: Layout
resultI222E001 = E 0

exampleI222E002 :: Text
exampleI222E002 =
  "      one\n\
  \      two\n\
  \    \t three\n\
  \"

resultI222E002 :: Layout
resultI222E002 = E 0

exampleI222E010 :: Text
exampleI222E010 =
  "      one\n\
  \ \t    two\n\
  \      three\n\
  \"

resultI222E010 :: Layout
resultI222E010 = E 0

exampleI222E011 :: Text
exampleI222E011 =
  "      one\n\
  \ \t    two\n\
  \ \t    three\n\
  \"

resultI222E011 :: Layout
resultI222E011 = E 0

exampleI222E012 :: Text
exampleI222E012 =
  "      one\n\
  \ \t    two\n\
  \    \t three\n\
  \"

resultI222E012 :: Layout
resultI222E012 = E 0

exampleI222E020 :: Text
exampleI222E020 =
  "      one\n\
  \    \t two\n\
  \      three\n\
  \"

resultI222E020 :: Layout
resultI222E020 = E 0

exampleI222E021 :: Text
exampleI222E021 =
  "      one\n\
  \    \t two\n\
  \ \t    three\n\
  \"

resultI222E021 :: Layout
resultI222E021 = E 0

exampleI222E022 :: Text
exampleI222E022 =
  "      one\n\
  \    \t two\n\
  \    \t three\n\
  \"

resultI222E022 :: Layout
resultI222E022 = E 0

exampleI222E100 :: Text
exampleI222E100 =
  " \t    one\n\
  \      two\n\
  \      three\n\
  \"

resultI222E100 :: Layout
resultI222E100 = E 0

exampleI222E101 :: Text
exampleI222E101 =
  " \t    one\n\
  \      two\n\
  \ \t    three\n\
  \"

resultI222E101 :: Layout
resultI222E101 = E 0

exampleI222E102 :: Text
exampleI222E102 =
  " \t    one\n\
  \      two\n\
  \    \t three\n\
  \"

resultI222E102 :: Layout
resultI222E102 = E 0

exampleI222E110 :: Text
exampleI222E110 =
  " \t    one\n\
  \ \t    two\n\
  \      three\n\
  \"

resultI222E110 :: Layout
resultI222E110 = E 0

exampleI222E111 :: Text
exampleI222E111 =
  " \t    one\n\
  \ \t    two\n\
  \ \t    three\n\
  \"

resultI222E111 :: Layout
resultI222E111 = E 0

exampleI222E112 :: Text
exampleI222E112 =
  " \t    one\n\
  \ \t    two\n\
  \    \t three\n\
  \"

resultI222E112 :: Layout
resultI222E112 = E 0

exampleI222E120 :: Text
exampleI222E120 =
  " \t    one\n\
  \    \t two\n\
  \      three\n\
  \"

resultI222E120 :: Layout
resultI222E120 = E 0

exampleI222E121 :: Text
exampleI222E121 =
  " \t    one\n\
  \    \t two\n\
  \ \t    three\n\
  \"

resultI222E121 :: Layout
resultI222E121 = E 0

exampleI222E122 :: Text
exampleI222E122 =
  " \t    one\n\
  \    \t two\n\
  \    \t three\n\
  \"

resultI222E122 :: Layout
resultI222E122 = E 0

exampleI222E200 :: Text
exampleI222E200 =
  "    \t one\n\
  \      two\n\
  \      three\n\
  \"

resultI222E200 :: Layout
resultI222E200 = E 0

exampleI222E201 :: Text
exampleI222E201 =
  "    \t one\n\
  \      two\n\
  \ \t    three\n\
  \"

resultI222E201 :: Layout
resultI222E201 = E 0

exampleI222E202 :: Text
exampleI222E202 =
  "    \t one\n\
  \      two\n\
  \    \t three\n\
  \"

resultI222E202 :: Layout
resultI222E202 = E 0

exampleI222E210 :: Text
exampleI222E210 =
  "    \t one\n\
  \ \t    two\n\
  \      three\n\
  \"

resultI222E210 :: Layout
resultI222E210 = E 0

exampleI222E211 :: Text
exampleI222E211 =
  "    \t one\n\
  \ \t    two\n\
  \ \t    three\n\
  \"

resultI222E211 :: Layout
resultI222E211 = E 0

exampleI222E212 :: Text
exampleI222E212 =
  "    \t one\n\
  \ \t    two\n\
  \    \t three\n\
  \"

resultI222E212 :: Layout
resultI222E212 = E 0

exampleI222E220 :: Text
exampleI222E220 =
  "    \t one\n\
  \    \t two\n\
  \      three\n\
  \"

resultI222E220 :: Layout
resultI222E220 = E 0

exampleI222E221 :: Text
exampleI222E221 =
  "    \t one\n\
  \    \t two\n\
  \ \t    three\n\
  \"

resultI222E221 :: Layout
resultI222E221 = E 0

exampleI222E222 :: Text
exampleI222E222 =
  "    \t one\n\
  \    \t two\n\
  \    \t three\n\
  \"

resultI222E222 :: Layout
resultI222E222 = E 0

exampleI223E000 :: Text
exampleI223E000 =
  "      one\n\
  \      two\n\
  \         three\n\
  \"

resultI223E000 :: Layout
resultI223E000 = E 0

exampleI223E001 :: Text
exampleI223E001 =
  "      one\n\
  \      two\n\
  \ \t       three\n\
  \"

resultI223E001 :: Layout
resultI223E001 = E 0

exampleI223E002 :: Text
exampleI223E002 =
  "      one\n\
  \      two\n\
  \    \t    three\n\
  \"

resultI223E002 :: Layout
resultI223E002 = E 0

exampleI223E003 :: Text
exampleI223E003 =
  "      one\n\
  \      two\n\
  \       \t three\n\
  \"
resultI223E003 :: Layout
resultI223E003 = E 0

exampleI223E010 :: Text
exampleI223E010 =
  "      one\n\
  \ \t    two\n\
  \         three\n\
  \"

resultI223E010 :: Layout
resultI223E010 = E 0

exampleI223E011 :: Text
exampleI223E011 =
  "      one\n\
  \ \t    two\n\
  \ \t       three\n\
  \"

resultI223E011 :: Layout
resultI223E011 = E 0

exampleI223E012 :: Text
exampleI223E012 =
  "      one\n\
  \ \t    two\n\
  \    \t    three\n\
  \"

resultI223E012 :: Layout
resultI223E012 = E 0

exampleI223E013 :: Text
exampleI223E013 =
  "      one\n\
  \ \t    two\n\
  \       \t three\n\
  \"

resultI223E013 :: Layout
resultI223E013 = E 0

exampleI223E020 :: Text
exampleI223E020 =
  "      one\n\
  \    \t two\n\
  \         three\n\
  \"

resultI223E020 :: Layout
resultI223E020 = E 0

exampleI223E021 :: Text
exampleI223E021 =
  "      one\n\
  \    \t two\n\
  \ \t       three\n\
  \"

resultI223E021 :: Layout
resultI223E021 = E 0

exampleI223E022 :: Text
exampleI223E022 =
  "      one\n\
  \    \t two\n\
  \    \t    three\n\
  \"

resultI223E022 :: Layout
resultI223E022 = E 0

exampleI223E023 :: Text
exampleI223E023 =
  "      one\n\
  \    \t two\n\
  \       \t three\n\
  \"

resultI223E023 :: Layout
resultI223E023 = E 0

exampleI223E100 :: Text
exampleI223E100 =
  " \t    one\n\
  \      two\n\
  \         three\n\
  \"

resultI223E100 :: Layout
resultI223E100 = E 0

exampleI223E101 :: Text
exampleI223E101 =
  " \t    one\n\
  \      two\n\
  \ \t       three\n\
  \"

resultI223E101 :: Layout
resultI223E101 = E 0

exampleI223E102 :: Text
exampleI223E102 =
  " \t    one\n\
  \      two\n\
  \    \t    three\n\
  \"

resultI223E102 :: Layout
resultI223E102 = E 0

exampleI223E103 :: Text
exampleI223E103 =
  " \t    one\n\
  \      two\n\
  \       \t three\n\
  \"

resultI223E103 :: Layout
resultI223E103 = E 0

exampleI223E110 :: Text
exampleI223E110 =
  " \t    one\n\
  \ \t    two\n\
  \         three\n\
  \"

resultI223E110 :: Layout
resultI223E110 = E 0

exampleI223E111 :: Text
exampleI223E111 =
  " \t    one\n\
  \ \t    two\n\
  \ \t       three\n\
  \"

resultI223E111 :: Layout
resultI223E111 = E 0

exampleI223E112 :: Text
exampleI223E112 =
  " \t    one\n\
  \ \t    two\n\
  \    \t    three\n\
  \"

resultI223E112 :: Layout
resultI223E112 = E 0

exampleI223E113 :: Text
exampleI223E113 =
  " \t    one\n\
  \ \t    two\n\
  \       \t three\n\
  \"

resultI223E113 :: Layout
resultI223E113 = E 0

exampleI223E120 :: Text
exampleI223E120 =
  " \t    one\n\
  \    \t two\n\
  \         three\n\
  \"

resultI223E120 :: Layout
resultI223E120 = E 0

exampleI223E121 :: Text
exampleI223E121 =
  " \t    one\n\
  \    \t two\n\
  \ \t       three\n\
  \"

resultI223E121 :: Layout
resultI223E121 = E 0

exampleI223E122 :: Text
exampleI223E122 =
  " \t    one\n\
  \    \t two\n\
  \    \t    three\n\
  \"

resultI223E122 :: Layout
resultI223E122 = E 0

exampleI223E123 :: Text
exampleI223E123 =
  " \t    one\n\
  \    \t two\n\
  \       \t three\n\
  \"

resultI223E123 :: Layout
resultI223E123 = E 0

exampleI223E200 :: Text
exampleI223E200 =
  "    \t one\n\
  \      two\n\
  \         three\n\
  \"

resultI223E200 :: Layout
resultI223E200 = E 0

exampleI223E201 :: Text
exampleI223E201 =
  "    \t one\n\
  \      two\n\
  \ \t       three\n\
  \"

resultI223E201 :: Layout
resultI223E201 = E 0

exampleI223E202 :: Text
exampleI223E202 =
  "    \t one\n\
  \      two\n\
  \    \t    three\n\
  \"

resultI223E202 :: Layout
resultI223E202 = E 0

exampleI223E203 :: Text
exampleI223E203 =
  "    \t one\n\
  \      two\n\
  \       \t three\n\
  \"

resultI223E203 :: Layout
resultI223E203 = E 0

exampleI223E210 :: Text
exampleI223E210 =
  "    \t one\n\
  \ \t    two\n\
  \         three\n\
  \"

resultI223E210 :: Layout
resultI223E210 = E 0

exampleI223E211 :: Text
exampleI223E211 =
  "    \t one\n\
  \ \t    two\n\
  \ \t       three\n\
  \"

resultI223E211 :: Layout
resultI223E211 = E 0

exampleI223E212 :: Text
exampleI223E212 =
  "    \t one\n\
  \ \t    two\n\
  \    \t    three\n\
  \"

resultI223E212 :: Layout
resultI223E212 = E 0

exampleI223E213 :: Text
exampleI223E213 =
  "    \t one\n\
  \ \t    two\n\
  \       \t three\n\
  \"

resultI223E213 :: Layout
resultI223E213 = E 0

exampleI223E220 :: Text
exampleI223E220 =
  "    \t one\n\
  \    \t two\n\
  \         three\n\
  \"

resultI223E220 :: Layout
resultI223E220 = E 0

exampleI223E221 :: Text
exampleI223E221 =
  "    \t one\n\
  \    \t two\n\
  \ \t       three\n\
  \"

resultI223E221 :: Layout
resultI223E221 = E 0

exampleI223E222 :: Text
exampleI223E222 =
  "    \t one\n\
  \    \t two\n\
  \    \t    three\n\
  \"

resultI223E222 :: Layout
resultI223E222 = E 0

exampleI223E223 :: Text
exampleI223E223 =
  "    \t one\n\
  \    \t two\n\
  \       \t three\n\
  \"

resultI223E223 :: Layout
resultI223E223 = E 0

exampleI231E000 :: Text
exampleI231E000 =
  "      one\n\
  \         two\n\
  \   three\n\
  \"

resultI231E000 :: Layout
resultI231E000 = E 0

exampleI231E001 :: Text
exampleI231E001 =
  "      one\n\
  \         two\n\
  \ \t three\n\
  \"

resultI231E001 :: Layout
resultI231E001 = E 0

exampleI231E010 :: Text
exampleI231E010 =
  "      one\n\
  \ \t       two\n\
  \   three\n\
  \"

resultI231E010 :: Layout
resultI231E010 = E 0

exampleI231E011 :: Text
exampleI231E011 =
  "      one\n\
  \ \t       two\n\
  \ \t three\n\
  \"

resultI231E011 :: Layout
resultI231E011 = E 0

exampleI231E020 :: Text
exampleI231E020 =
  "      one\n\
  \    \t    two\n\
  \   three\n\
  \"

resultI231E020 :: Layout
resultI231E020 = E 0

exampleI231E021 :: Text
exampleI231E021 =
  "      one\n\
  \    \t    two\n\
  \ \t three\n\
  \"

resultI231E021 :: Layout
resultI231E021 = E 0

exampleI231E030 :: Text
exampleI231E030 =
  "      one\n\
  \       \t two\n\
  \   three\n\
  \"

resultI231E030 :: Layout
resultI231E030 = E 0

exampleI231E031 :: Text
exampleI231E031 =
  "      one\n\
  \       \t two\n\
  \ \t three\n\
  \"
resultI231E031 :: Layout
resultI231E031 = E 0

exampleI231E100 :: Text
exampleI231E100 =
  " \t    one\n\
  \         two\n\
  \   three\n\
  \"

resultI231E100 :: Layout
resultI231E100 = E 0

exampleI231E101 :: Text
exampleI231E101 =
  " \t    one\n\
  \         two\n\
  \ \t three\n\
  \"

resultI231E101 :: Layout
resultI231E101 = E 0

exampleI231E110 :: Text
exampleI231E110 =
  " \t    one\n\
  \ \t       two\n\
  \   three\n\
  \"

resultI231E110 :: Layout
resultI231E110 = E 0

exampleI231E111 :: Text
exampleI231E111 =
  " \t    one\n\
  \ \t       two\n\
  \ \t three\n\
  \"

resultI231E111 :: Layout
resultI231E111 = E 0

exampleI231E120 :: Text
exampleI231E120 =
  " \t    one\n\
  \    \t    two\n\
  \   three\n\
  \"

resultI231E120 :: Layout
resultI231E120 = E 0

exampleI231E121 :: Text
exampleI231E121 =
  " \t    one\n\
  \    \t    two\n\
  \ \t three\n\
  \"

resultI231E121 :: Layout
resultI231E121 = E 0

exampleI231E130 :: Text
exampleI231E130 =
  " \t    one\n\
  \       \t two\n\
  \   three\n\
  \"

resultI231E130 :: Layout
resultI231E130 = E 0

exampleI231E131 :: Text
exampleI231E131 =
  " \t    one\n\
  \       \t two\n\
  \ \t three\n\
  \"

resultI231E131 :: Layout
resultI231E131 = E 0

exampleI231E200 :: Text
exampleI231E200 =
  "    \t one\n\
  \         two\n\
  \   three\n\
  \"

resultI231E200 :: Layout
resultI231E200 = E 0

exampleI231E201 :: Text
exampleI231E201 =
  "    \t one\n\
  \         two\n\
  \ \t three\n\
  \"

resultI231E201 :: Layout
resultI231E201 = E 0

exampleI231E210 :: Text
exampleI231E210 =
  "    \t one\n\
  \ \t       two\n\
  \   three\n\
  \"

resultI231E210 :: Layout
resultI231E210 = E 0

exampleI231E211 :: Text
exampleI231E211 =
  "    \t one\n\
  \ \t       two\n\
  \ \t three\n\
  \"

resultI231E211 :: Layout
resultI231E211 = E 0

exampleI231E220 :: Text
exampleI231E220 =
  "    \t one\n\
  \    \t    two\n\
  \   three\n\
  \"

resultI231E220 :: Layout
resultI231E220 = E 0

exampleI231E221 :: Text
exampleI231E221 =
  "    \t one\n\
  \    \t    two\n\
  \ \t three\n\
  \"

resultI231E221 :: Layout
resultI231E221 = E 0

exampleI231E230 :: Text
exampleI231E230 =
  "    \t one\n\
  \       \t two\n\
  \   three\n\
  \"

resultI231E230 :: Layout
resultI231E230 = E 0

exampleI231E231 :: Text
exampleI231E231 =
  "    \t one\n\
  \       \t two\n\
  \ \t three\n\
  \"

resultI231E231 :: Layout
resultI231E231 = E 0

exampleI232E000 :: Text
exampleI232E000 =
  "      one\n\
  \         two\n\
  \      three\n\
  \"

resultI232E000 :: Layout
resultI232E000 = E 0

exampleI232E001 :: Text
exampleI232E001 =
  "      one\n\
  \         two\n\
  \ \t    three\n\
  \"

resultI232E001 :: Layout
resultI232E001 = E 0

exampleI232E002 :: Text
exampleI232E002 =
  "      one\n\
  \         two\n\
  \    \t three\n\
  \"

resultI232E002 :: Layout
resultI232E002 = E 0

exampleI232E010 :: Text
exampleI232E010 =
  "      one\n\
  \ \t       two\n\
  \      three\n\
  \"

resultI232E010 :: Layout
resultI232E010 = E 0

exampleI232E011 :: Text
exampleI232E011 =
  "      one\n\
  \ \t       two\n\
  \ \t    three\n\
  \"

resultI232E011 :: Layout
resultI232E011 = E 0

exampleI232E012 :: Text
exampleI232E012 =
  "      one\n\
  \ \t       two\n\
  \    \t three\n\
  \"

resultI232E012 :: Layout
resultI232E012 = E 0

exampleI232E020 :: Text
exampleI232E020 =
  "      one\n\
  \    \t    two\n\
  \      three\n\
  \"

resultI232E020 :: Layout
resultI232E020 = E 0

exampleI232E021 :: Text
exampleI232E021 =
  "      one\n\
  \    \t    two\n\
  \ \t    three\n\
  \"

resultI232E021 :: Layout
resultI232E021 = E 0

exampleI232E022 :: Text
exampleI232E022 =
  "      one\n\
  \    \t    two\n\
  \    \t three\n\
  \"

resultI232E022 :: Layout
resultI232E022 = E 0

exampleI232E030 :: Text
exampleI232E030 =
  "      one\n\
  \       \t two\n\
  \      three\n\
  \"

resultI232E030 :: Layout
resultI232E030 = E 0

exampleI232E031 :: Text
exampleI232E031 =
  "      one\n\
  \       \t two\n\
  \ \t    three\n\
  \"

resultI232E031 :: Layout
resultI232E031 = E 0

exampleI232E032 :: Text
exampleI232E032 =
  "      one\n\
  \       \t two\n\
  \    \t three\n\
  \"

resultI232E032 :: Layout
resultI232E032 = E 0

exampleI232E100 :: Text
exampleI232E100 =
  " \t    one\n\
  \         two\n\
  \      three\n\
  \"

resultI232E100 :: Layout
resultI232E100 = E 0

exampleI232E101 :: Text
exampleI232E101 =
  " \t    one\n\
  \         two\n\
  \ \t    three\n\
  \"

resultI232E101 :: Layout
resultI232E101 = E 0

exampleI232E102 :: Text
exampleI232E102 =
  " \t    one\n\
  \         two\n\
  \    \t three\n\
  \"

resultI232E102 :: Layout
resultI232E102 = E 0

exampleI232E110 :: Text
exampleI232E110 =
  " \t    one\n\
  \ \t       two\n\
  \      three\n\
  \"

resultI232E110 :: Layout
resultI232E110 = E 0

exampleI232E111 :: Text
exampleI232E111 =
  " \t    one\n\
  \ \t       two\n\
  \ \t    three\n\
  \"

resultI232E111 :: Layout
resultI232E111 = E 0

exampleI232E112 :: Text
exampleI232E112 =
  " \t    one\n\
  \ \t       two\n\
  \    \t three\n\
  \"

resultI232E112 :: Layout
resultI232E112 = E 0

exampleI232E120 :: Text
exampleI232E120 =
  " \t    one\n\
  \    \t    two\n\
  \      three\n\
  \"

resultI232E120 :: Layout
resultI232E120 = E 0

exampleI232E121 :: Text
exampleI232E121 =
  " \t    one\n\
  \    \t    two\n\
  \ \t    three\n\
  \"

resultI232E121 :: Layout
resultI232E121 = E 0

exampleI232E122 :: Text
exampleI232E122 =
  " \t    one\n\
  \    \t    two\n\
  \    \t three\n\
  \"

resultI232E122 :: Layout
resultI232E122 = E 0

exampleI232E130 :: Text
exampleI232E130 =
  " \t    one\n\
  \       \t two\n\
  \      three\n\
  \"

resultI232E130 :: Layout
resultI232E130 = E 0

exampleI232E131 :: Text
exampleI232E131 =
  " \t    one\n\
  \       \t two\n\
  \ \t    three\n\
  \"

resultI232E131 :: Layout
resultI232E131 = E 0

exampleI232E132 :: Text
exampleI232E132 =
  " \t    one\n\
  \       \t two\n\
  \    \t three\n\
  \"

resultI232E132 :: Layout
resultI232E132 = E 0

exampleI232E200 :: Text
exampleI232E200 =
  "    \t one\n\
  \         two\n\
  \      three\n\
  \"

resultI232E200 :: Layout
resultI232E200 = E 0

exampleI232E201 :: Text
exampleI232E201 =
  "    \t one\n\
  \         two\n\
  \ \t    three\n\
  \"

resultI232E201 :: Layout
resultI232E201 = E 0

exampleI232E202 :: Text
exampleI232E202 =
  "    \t one\n\
  \         two\n\
  \    \t three\n\
  \"

resultI232E202 :: Layout
resultI232E202 = E 0

exampleI232E210 :: Text
exampleI232E210 =
  "    \t one\n\
  \ \t       two\n\
  \      three\n\
  \"

resultI232E210 :: Layout
resultI232E210 = E 0

exampleI232E211 :: Text
exampleI232E211 =
  "    \t one\n\
  \ \t       two\n\
  \ \t    three\n\
  \"

resultI232E211 :: Layout
resultI232E211 = E 0

exampleI232E212 :: Text
exampleI232E212 =
  "    \t one\n\
  \ \t       two\n\
  \    \t three\n\
  \"

resultI232E212 :: Layout
resultI232E212 = E 0

exampleI232E220 :: Text
exampleI232E220 =
  "    \t one\n\
  \    \t    two\n\
  \      three\n\
  \"

resultI232E220 :: Layout
resultI232E220 = E 0

exampleI232E221 :: Text
exampleI232E221 =
  "    \t one\n\
  \    \t    two\n\
  \ \t    three\n\
  \"

resultI232E221 :: Layout
resultI232E221 = E 0

exampleI232E222 :: Text
exampleI232E222 =
  "    \t one\n\
  \    \t    two\n\
  \    \t three\n\
  \"

resultI232E222 :: Layout
resultI232E222 = E 0

exampleI232E230 :: Text
exampleI232E230 =
  "    \t one\n\
  \       \t two\n\
  \      three\n\
  \"

resultI232E230 :: Layout
resultI232E230 = E 0

exampleI232E231 :: Text
exampleI232E231 =
  "    \t one\n\
  \       \t two\n\
  \ \t    three\n\
  \"

resultI232E231 :: Layout
resultI232E231 = E 0

exampleI232E232 :: Text
exampleI232E232 =
  "    \t one\n\
  \       \t two\n\
  \    \t three\n\
  \"

resultI232E232 :: Layout
resultI232E232 = E 0

exampleI233E000 :: Text
exampleI233E000 =
  "      one\n\
  \         two\n\
  \         three\n\
  \"

resultI233E000 :: Layout
resultI233E000 = E 0

exampleI233E001 :: Text
exampleI233E001 =
  "      one\n\
  \         two\n\
  \ \t       three\n\
  \"

resultI233E001 :: Layout
resultI233E001 = E 0

exampleI233E002 :: Text
exampleI233E002 =
  "      one\n\
  \         two\n\
  \    \t    three\n\
  \"

resultI233E002 :: Layout
resultI233E002 = E 0

exampleI233E003 :: Text
exampleI233E003 =
  "      one\n\
  \         two\n\
  \       \t three\n\
  \"

resultI233E003 :: Layout
resultI233E003 = E 0

exampleI233E010 :: Text
exampleI233E010 =
  "      one\n\
  \ \t       two\n\
  \         three\n\
  \"

resultI233E010 :: Layout
resultI233E010 = E 0

exampleI233E011 :: Text
exampleI233E011 =
  "      one\n\
  \ \t       two\n\
  \ \t       three\n\
  \"

resultI233E011 :: Layout
resultI233E011 = E 0

exampleI233E012 :: Text
exampleI233E012 =
  "      one\n\
  \ \t       two\n\
  \    \t    three\n\
  \"

resultI233E012 :: Layout
resultI233E012 = E 0

exampleI233E013 :: Text
exampleI233E013 =
  "      one\n\
  \ \t       two\n\
  \       \t three\n\
  \"

resultI233E013 :: Layout
resultI233E013 = E 0

exampleI233E020 :: Text
exampleI233E020 =
  "      one\n\
  \    \t    two\n\
  \         three\n\
  \"

resultI233E020 :: Layout
resultI233E020 = E 0

exampleI233E021 :: Text
exampleI233E021 =
  "      one\n\
  \    \t    two\n\
  \ \t       three\n\
  \"

resultI233E021 :: Layout
resultI233E021 = E 0

exampleI233E022 :: Text
exampleI233E022 =
  "      one\n\
  \    \t    two\n\
  \    \t    three\n\
  \"

resultI233E022 :: Layout
resultI233E022 = E 0

exampleI233E023 :: Text
exampleI233E023 =
  "      one\n\
  \    \t    two\n\
  \       \t three\n\
  \"

resultI233E023 :: Layout
resultI233E023 = E 0

exampleI233E030 :: Text
exampleI233E030 =
  "      one\n\
  \       \t two\n\
  \         three\n\
  \"

resultI233E030 :: Layout
resultI233E030 = E 0

exampleI233E031 :: Text
exampleI233E031 =
  "      one\n\
  \       \t two\n\
  \ \t       three\n\
  \"

resultI233E031 :: Layout
resultI233E031 = E 0

exampleI233E032 :: Text
exampleI233E032 =
  "      one\n\
  \       \t two\n\
  \    \t    three\n\
  \"

resultI233E032 :: Layout
resultI233E032 = E 0

exampleI233E033 :: Text
exampleI233E033 =
  "      one\n\
  \       \t two\n\
  \       \t three\n\
  \"

resultI233E033 :: Layout
resultI233E033 = E 0

exampleI233E100 :: Text
exampleI233E100 =
  " \t    one\n\
  \         two\n\
  \         three\n\
  \"

resultI233E100 :: Layout
resultI233E100 = E 0

exampleI233E101 :: Text
exampleI233E101 =
  " \t    one\n\
  \         two\n\
  \ \t       three\n\
  \"

resultI233E101 :: Layout
resultI233E101 = E 0

exampleI233E102 :: Text
exampleI233E102 =
  " \t    one\n\
  \         two\n\
  \    \t    three\n\
  \"

resultI233E102 :: Layout
resultI233E102 = E 0

exampleI233E103 :: Text
exampleI233E103 =
  " \t    one\n\
  \         two\n\
  \       \t three\n\
  \"

resultI233E103 :: Layout
resultI233E103 = E 0

exampleI233E110 :: Text
exampleI233E110 =
  " \t    one\n\
  \ \t       two\n\
  \         three\n\
  \"

resultI233E110 :: Layout
resultI233E110 = E 0

exampleI233E111 :: Text
exampleI233E111 =
  " \t    one\n\
  \ \t       two\n\
  \ \t       three\n\
  \"

resultI233E111 :: Layout
resultI233E111 = E 0

exampleI233E112 :: Text
exampleI233E112 =
  " \t    one\n\
  \ \t       two\n\
  \    \t    three\n\
  \"

resultI233E112 :: Layout
resultI233E112 = E 0

exampleI233E113 :: Text
exampleI233E113 =
  " \t    one\n\
  \ \t       two\n\
  \       \t three\n\
  \"

resultI233E113 :: Layout
resultI233E113 = E 0

exampleI233E120 :: Text
exampleI233E120 =
  " \t    one\n\
  \    \t    two\n\
  \         three\n\
  \"

resultI233E120 :: Layout
resultI233E120 = E 0

exampleI233E121 :: Text
exampleI233E121 =
  " \t    one\n\
  \    \t    two\n\
  \ \t       three\n\
  \"

resultI233E121 :: Layout
resultI233E121 = E 0

exampleI233E122 :: Text
exampleI233E122 =
  " \t    one\n\
  \    \t    two\n\
  \    \t    three\n\
  \"

resultI233E122 :: Layout
resultI233E122 = E 0

exampleI233E123 :: Text
exampleI233E123 =
  " \t    one\n\
  \    \t    two\n\
  \       \t three\n\
  \"

resultI233E123 :: Layout
resultI233E123 = E 0

exampleI233E130 :: Text
exampleI233E130 =
  " \t    one\n\
  \       \t two\n\
  \         three\n\
  \"

resultI233E130 :: Layout
resultI233E130 = E 0

exampleI233E131 :: Text
exampleI233E131 =
  " \t    one\n\
  \       \t two\n\
  \ \t       three\n\
  \"

resultI233E131 :: Layout
resultI233E131 = E 0

exampleI233E132 :: Text
exampleI233E132 =
  " \t    one\n\
  \       \t two\n\
  \    \t    three\n\
  \"

resultI233E132 :: Layout
resultI233E132 = E 0

exampleI233E133 :: Text
exampleI233E133 =
  " \t    one\n\
  \       \t two\n\
  \       \t three\n\
  \"

resultI233E133 :: Layout
resultI233E133 = E 0

exampleI233E200 :: Text
exampleI233E200 =
  "    \t one\n\
  \         two\n\
  \         three\n\
  \"

resultI233E200 :: Layout
resultI233E200 = E 0

exampleI233E201 :: Text
exampleI233E201 =
  "    \t one\n\
  \         two\n\
  \ \t       three\n\
  \"

resultI233E201 :: Layout
resultI233E201 = E 0

exampleI233E202 :: Text
exampleI233E202 =
  "    \t one\n\
  \         two\n\
  \    \t    three\n\
  \"

resultI233E202 :: Layout
resultI233E202 = E 0

exampleI233E203 :: Text
exampleI233E203 =
  "    \t one\n\
  \         two\n\
  \       \t three\n\
  \"

resultI233E203 :: Layout
resultI233E203 = E 0

exampleI233E210 :: Text
exampleI233E210 =
  "    \t one\n\
  \ \t       two\n\
  \         three\n\
  \"

resultI233E210 :: Layout
resultI233E210 = E 0

exampleI233E211 :: Text
exampleI233E211 =
  "    \t one\n\
  \ \t       two\n\
  \ \t       three\n\
  \"

resultI233E211 :: Layout
resultI233E211 = E 0

exampleI233E212 :: Text
exampleI233E212 =
  "    \t one\n\
  \ \t       two\n\
  \    \t    three\n\
  \"

resultI233E212 :: Layout
resultI233E212 = E 0

exampleI233E213 :: Text
exampleI233E213 =
  "    \t one\n\
  \ \t       two\n\
  \       \t three\n\
  \"

resultI233E213 :: Layout
resultI233E213 = E 0

exampleI233E220 :: Text
exampleI233E220 =
  "    \t one\n\
  \    \t    two\n\
  \         three\n\
  \"

resultI233E220 :: Layout
resultI233E220 = E 0

exampleI233E221 :: Text
exampleI233E221 =
  "    \t one\n\
  \    \t    two\n\
  \ \t       three\n\
  \"

resultI233E221 :: Layout
resultI233E221 = E 0

exampleI233E222 :: Text
exampleI233E222 =
  "    \t one\n\
  \    \t    two\n\
  \    \t    three\n\
  \"

resultI233E222 :: Layout
resultI233E222 = E 0

exampleI233E223 :: Text
exampleI233E223 =
  "    \t one\n\
  \    \t    two\n\
  \       \t three\n\
  \"

resultI233E223 :: Layout
resultI233E223 = E 0

exampleI233E230 :: Text
exampleI233E230 =
  "    \t one\n\
  \       \t two\n\
  \         three\n\
  \"

resultI233E230 :: Layout
resultI233E230 = E 0

exampleI233E231 :: Text
exampleI233E231 =
  "    \t one\n\
  \       \t two\n\
  \ \t       three\n\
  \"

resultI233E231 :: Layout
resultI233E231 = E 0

exampleI233E232 :: Text
exampleI233E232 =
  "    \t one\n\
  \       \t two\n\
  \    \t    three\n\
  \"

resultI233E232 :: Layout
resultI233E232 = E 0

exampleI233E233 :: Text
exampleI233E233 =
  "    \t one\n\
  \       \t two\n\
  \       \t three\n\
  \"

resultI233E233 :: Layout
resultI233E233 = E 0

exampleI311E000 :: Text
exampleI311E000 =
  "         one\n\
  \   two\n\
  \   three\n\
  \"

resultI311E000 :: Layout
resultI311E000 = E 0

exampleI311E001 :: Text
exampleI311E001 =
  "         one\n\
  \   two\n\
  \ \t three\n\
  \"

resultI311E001 :: Layout
resultI311E001 = E 0

exampleI311E010 :: Text
exampleI311E010 =
  "         one\n\
  \ \t two\n\
  \   three\n\
  \"

resultI311E010 :: Layout
resultI311E010 = E 0

exampleI311E011 :: Text
exampleI311E011 =
  "         one\n\
  \ \t two\n\
  \ \t three\n\
  \"

resultI311E011 :: Layout
resultI311E011 = E 0

exampleI311E100 :: Text
exampleI311E100 =
  " \t       one\n\
  \   two\n\
  \   three\n\
  \"

resultI311E100 :: Layout
resultI311E100 = E 0

exampleI311E101 :: Text
exampleI311E101 =
  " \t       one\n\
  \   two\n\
  \ \t three\n\
  \"

resultI311E101 :: Layout
resultI311E101 = E 0

exampleI311E110 :: Text
exampleI311E110 =
  " \t       one\n\
  \ \t two\n\
  \   three\n\
  \"

resultI311E110 :: Layout
resultI311E110 = E 0

exampleI311E111 :: Text
exampleI311E111 =
  " \t       one\n\
  \ \t two\n\
  \ \t three\n\
  \"

resultI311E111 :: Layout
resultI311E111 = E 0

exampleI311E200 :: Text
exampleI311E200 =
  "    \t    one\n\
  \   two\n\
  \   three\n\
  \"

resultI311E200 :: Layout
resultI311E200 = E 0

exampleI311E201 :: Text
exampleI311E201 =
  "    \t    one\n\
  \   two\n\
  \ \t three\n\
  \"

resultI311E201 :: Layout
resultI311E201 = E 0

exampleI311E210 :: Text
exampleI311E210 =
  "    \t    one\n\
  \ \t two\n\
  \   three\n\
  \"

resultI311E210 :: Layout
resultI311E210 = E 0

exampleI311E211 :: Text
exampleI311E211 =
  "    \t    one\n\
  \ \t two\n\
  \ \t three\n\
  \"

resultI311E211 :: Layout
resultI311E211 = E 0

exampleI311E300 :: Text
exampleI311E300 =
  "       \t one\n\
  \   two\n\
  \   three\n\
  \"

resultI311E300 :: Layout
resultI311E300 = E 0

exampleI311E301 :: Text
exampleI311E301 =
  "       \t one\n\
  \   two\n\
  \ \t three\n\
  \"

resultI311E301 :: Layout
resultI311E301 = E 0

exampleI311E310 :: Text
exampleI311E310 =
  "       \t one\n\
  \ \t two\n\
  \   three\n\
  \"

resultI311E310 :: Layout
resultI311E310 = E 0

exampleI311E311 :: Text
exampleI311E311 =
  "       \t one\n\
  \ \t two\n\
  \ \t three\n\
  \"

resultI311E311 :: Layout
resultI311E311 = E 0

exampleI312E000 :: Text
exampleI312E000 =
  "         one\n\
  \   two\n\
  \      three\n\
  \"

resultI312E000 :: Layout
resultI312E000 = E 0

exampleI312E001 :: Text
exampleI312E001 =
  "         one\n\
  \   two\n\
  \ \t    three\n\
  \"

resultI312E001 :: Layout
resultI312E001 = E 0

exampleI312E002 :: Text
exampleI312E002 =
  "         one\n\
  \   two\n\
  \    \t three\n\
  \"

resultI312E002 :: Layout
resultI312E002 = E 0

exampleI312E010 :: Text
exampleI312E010 =
  "         one\n\
  \ \t two\n\
  \      three\n\
  \"

resultI312E010 :: Layout
resultI312E010 = E 0

exampleI312E011 :: Text
exampleI312E011 =
  "         one\n\
  \ \t two\n\
  \ \t    three\n\
  \"

resultI312E011 :: Layout
resultI312E011 = E 0

exampleI312E012 :: Text
exampleI312E012 =
  "         one\n\
  \ \t two\n\
  \    \t three\n\
  \"

resultI312E012 :: Layout
resultI312E012 = E 0

exampleI312E100 :: Text
exampleI312E100 =
  " \t       one\n\
  \   two\n\
  \      three\n\
  \"

resultI312E100 :: Layout
resultI312E100 = E 0

exampleI312E101 :: Text
exampleI312E101 =
  " \t       one\n\
  \   two\n\
  \ \t    three\n\
  \"

resultI312E101 :: Layout
resultI312E101 = E 0

exampleI312E102 :: Text
exampleI312E102 =
  " \t       one\n\
  \   two\n\
  \    \t three\n\
  \"

resultI312E102 :: Layout
resultI312E102 = E 0

exampleI312E110 :: Text
exampleI312E110 =
  " \t       one\n\
  \ \t two\n\
  \      three\n\
  \"

resultI312E110 :: Layout
resultI312E110 = E 0

exampleI312E111 :: Text
exampleI312E111 =
  " \t       one\n\
  \ \t two\n\
  \ \t    three\n\
  \"

resultI312E111 :: Layout
resultI312E111 = E 0

exampleI312E112 :: Text
exampleI312E112 =
  " \t       one\n\
  \ \t two\n\
  \    \t three\n\
  \"

resultI312E112 :: Layout
resultI312E112 = E 0

exampleI312E200 :: Text
exampleI312E200 =
  "    \t    one\n\
  \   two\n\
  \      three\n\
  \"

resultI312E200 :: Layout
resultI312E200 = E 0

exampleI312E201 :: Text
exampleI312E201 =
  "    \t    one\n\
  \   two\n\
  \ \t    three\n\
  \"

resultI312E201 :: Layout
resultI312E201 = E 0

exampleI312E202 :: Text
exampleI312E202 =
  "    \t    one\n\
  \   two\n\
  \    \t three\n\
  \"

resultI312E202 :: Layout
resultI312E202 = E 0

exampleI312E210 :: Text
exampleI312E210 =
  "    \t    one\n\
  \ \t two\n\
  \      three\n\
  \"

resultI312E210 :: Layout
resultI312E210 = E 0

exampleI312E211 :: Text
exampleI312E211 =
  "    \t    one\n\
  \ \t two\n\
  \ \t    three\n\
  \"

resultI312E211 :: Layout
resultI312E211 = E 0

exampleI312E212 :: Text
exampleI312E212 =
  "    \t    one\n\
  \ \t two\n\
  \    \t three\n\
  \"

resultI312E212 :: Layout
resultI312E212 = E 0

exampleI312E300 :: Text
exampleI312E300 =
  "       \t one\n\
  \   two\n\
  \      three\n\
  \"

resultI312E300 :: Layout
resultI312E300 = E 0

exampleI312E301 :: Text
exampleI312E301 =
  "       \t one\n\
  \   two\n\
  \ \t    three\n\
  \"

resultI312E301 :: Layout
resultI312E301 = E 0

exampleI312E302 :: Text
exampleI312E302 =
  "       \t one\n\
  \   two\n\
  \    \t three\n\
  \"

resultI312E302 :: Layout
resultI312E302 = E 0

exampleI312E310 :: Text
exampleI312E310 =
  "       \t one\n\
  \ \t two\n\
  \      three\n\
  \"

resultI312E310 :: Layout
resultI312E310 = E 0

exampleI312E311 :: Text
exampleI312E311 =
  "       \t one\n\
  \ \t two\n\
  \ \t    three\n\
  \"

resultI312E311 :: Layout
resultI312E311 = E 0

exampleI312E312 :: Text
exampleI312E312 =
  "       \t one\n\
  \ \t two\n\
  \    \t three\n\
  \"

resultI312E312 :: Layout
resultI312E312 = E 0

exampleI313E000 :: Text
exampleI313E000 =
  "         one\n\
  \   two\n\
  \         three\n\
  \"

resultI313E000 :: Layout
resultI313E000 = E 0

exampleI313E001 :: Text
exampleI313E001 =
  "         one\n\
  \   two\n\
  \ \t       three\n\
  \"

resultI313E001 :: Layout
resultI313E001 = E 0

exampleI313E002 :: Text
exampleI313E002 =
  "         one\n\
  \   two\n\
  \    \t    three\n\
  \"

resultI313E002 :: Layout
resultI313E002 = E 0

exampleI313E003 :: Text
exampleI313E003 =
  "         one\n\
  \   two\n\
  \       \t three\n\
  \"

resultI313E003 :: Layout
resultI313E003 = E 0

exampleI313E010 :: Text
exampleI313E010 =
  "         one\n\
  \ \t two\n\
  \         three\n\
  \"

resultI313E010 :: Layout
resultI313E010 = E 0

exampleI313E011 :: Text
exampleI313E011 =
  "         one\n\
  \ \t two\n\
  \ \t       three\n\
  \"

resultI313E011 :: Layout
resultI313E011 = E 0

exampleI313E012 :: Text
exampleI313E012 =
  "         one\n\
  \ \t two\n\
  \    \t    three\n\
  \"

resultI313E012 :: Layout
resultI313E012 = E 0

exampleI313E013 :: Text
exampleI313E013 =
  "         one\n\
  \ \t two\n\
  \       \t three\n\
  \"

resultI313E013 :: Layout
resultI313E013 = E 0

exampleI313E100 :: Text
exampleI313E100 =
  " \t       one\n\
  \   two\n\
  \         three\n\
  \"

resultI313E100 :: Layout
resultI313E100 = E 0

exampleI313E101 :: Text
exampleI313E101 =
  " \t       one\n\
  \   two\n\
  \ \t       three\n\
  \"

resultI313E101 :: Layout
resultI313E101 = E 0

exampleI313E102 :: Text
exampleI313E102 =
  " \t       one\n\
  \   two\n\
  \    \t    three\n\
  \"

resultI313E102 :: Layout
resultI313E102 = E 0

exampleI313E103 :: Text
exampleI313E103 =
  " \t       one\n\
  \   two\n\
  \       \t three\n\
  \"

resultI313E103 :: Layout
resultI313E103 = E 0

exampleI313E110 :: Text
exampleI313E110 =
  " \t       one\n\
  \ \t two\n\
  \         three\n\
  \"

resultI313E110 :: Layout
resultI313E110 = E 0

exampleI313E111 :: Text
exampleI313E111 =
  " \t       one\n\
  \ \t two\n\
  \ \t       three\n\
  \"

resultI313E111 :: Layout
resultI313E111 = E 0

exampleI313E112 :: Text
exampleI313E112 =
  " \t       one\n\
  \ \t two\n\
  \    \t    three\n\
  \"

resultI313E112 :: Layout
resultI313E112 = E 0

exampleI313E113 :: Text
exampleI313E113 =
  " \t       one\n\
  \ \t two\n\
  \       \t three\n\
  \"

resultI313E113 :: Layout
resultI313E113 = E 0

exampleI313E200 :: Text
exampleI313E200 =
  "    \t    one\n\
  \   two\n\
  \         three\n\
  \"

resultI313E200 :: Layout
resultI313E200 = E 0

exampleI313E201 :: Text
exampleI313E201 =
  "    \t    one\n\
  \   two\n\
  \ \t       three\n\
  \"

resultI313E201 :: Layout
resultI313E201 = E 0

exampleI313E202 :: Text
exampleI313E202 =
  "    \t    one\n\
  \   two\n\
  \    \t    three\n\
  \"

resultI313E202 :: Layout
resultI313E202 = E 0

exampleI313E203 :: Text
exampleI313E203 =
  "    \t    one\n\
  \   two\n\
  \       \t three\n\
  \"

resultI313E203 :: Layout
resultI313E203 = E 0

exampleI313E210 :: Text
exampleI313E210 =
  "    \t    one\n\
  \ \t two\n\
  \         three\n\
  \"

resultI313E210 :: Layout
resultI313E210 = E 0

exampleI313E211 :: Text
exampleI313E211 =
  "    \t    one\n\
  \ \t two\n\
  \ \t       three\n\
  \"

resultI313E211 :: Layout
resultI313E211 = E 0

exampleI313E212 :: Text
exampleI313E212 =
  "    \t    one\n\
  \ \t two\n\
  \    \t    three\n\
  \"

resultI313E212 :: Layout
resultI313E212 = E 0

exampleI313E213 :: Text
exampleI313E213 =
  "    \t    one\n\
  \ \t two\n\
  \       \t three\n\
  \"

resultI313E213 :: Layout
resultI313E213 = E 0

exampleI313E300 :: Text
exampleI313E300 =
  "       \t one\n\
  \   two\n\
  \         three\n\
  \"

resultI313E300 :: Layout
resultI313E300 = E 0

exampleI313E301 :: Text
exampleI313E301 =
  "       \t one\n\
  \   two\n\
  \ \t       three\n\
  \"

resultI313E301 :: Layout
resultI313E301 = E 0

exampleI313E302 :: Text
exampleI313E302 =
  "       \t one\n\
  \   two\n\
  \    \t    three\n\
  \"

resultI313E302 :: Layout
resultI313E302 = E 0

exampleI313E303 :: Text
exampleI313E303 =
  "       \t one\n\
  \   two\n\
  \       \t three\n\
  \"

resultI313E303 :: Layout
resultI313E303 = E 0

exampleI313E310 :: Text
exampleI313E310 =
  "       \t one\n\
  \ \t two\n\
  \         three\n\
  \"

resultI313E310 :: Layout
resultI313E310 = E 0

exampleI313E311 :: Text
exampleI313E311 =
  "       \t one\n\
  \ \t two\n\
  \ \t       three\n\
  \"

resultI313E311 :: Layout
resultI313E311 = E 0

exampleI313E312 :: Text
exampleI313E312 =
  "       \t one\n\
  \ \t two\n\
  \    \t    three\n\
  \"

resultI313E312 :: Layout
resultI313E312 = E 0

exampleI313E313 :: Text
exampleI313E313 =
  "       \t one\n\
  \ \t two\n\
  \       \t three\n\
  \"

resultI313E313 :: Layout
resultI313E313 = E 0

exampleI321E000 :: Text
exampleI321E000 =
  "         one\n\
  \      two\n\
  \   three\n\
  \"

resultI321E000 :: Layout
resultI321E000 = E 0

exampleI321E001 :: Text
exampleI321E001 =
  "         one\n\
  \      two\n\
  \ \t three\n\
  \"

resultI321E001 :: Layout
resultI321E001 = E 0

exampleI321E010 :: Text
exampleI321E010 =
  "         one\n\
  \ \t    two\n\
  \   three\n\
  \"

resultI321E010 :: Layout
resultI321E010 = E 0

exampleI321E011 :: Text
exampleI321E011 =
  "         one\n\
  \ \t    two\n\
  \ \t three\n\
  \"

resultI321E011 :: Layout
resultI321E011 = E 0

exampleI321E020 :: Text
exampleI321E020 =
  "         one\n\
  \    \t two\n\
  \   three\n\
  \"

resultI321E020 :: Layout
resultI321E020 = E 0

exampleI321E021 :: Text
exampleI321E021 =
  "         one\n\
  \    \t two\n\
  \ \t three\n\
  \"

resultI321E021 :: Layout
resultI321E021 = E 0

exampleI321E100 :: Text
exampleI321E100 =
  " \t       one\n\
  \      two\n\
  \   three\n\
  \"

resultI321E100 :: Layout
resultI321E100 = E 0

exampleI321E101 :: Text
exampleI321E101 =
  " \t       one\n\
  \      two\n\
  \ \t three\n\
  \"

resultI321E101 :: Layout
resultI321E101 = E 0

exampleI321E110 :: Text
exampleI321E110 =
  " \t       one\n\
  \ \t    two\n\
  \   three\n\
  \"

resultI321E110 :: Layout
resultI321E110 = E 0

exampleI321E111 :: Text
exampleI321E111 =
  " \t       one\n\
  \ \t    two\n\
  \ \t three\n\
  \"

resultI321E111 :: Layout
resultI321E111 = E 0

exampleI321E120 :: Text
exampleI321E120 =
  " \t       one\n\
  \    \t two\n\
  \   three\n\
  \"

resultI321E120 :: Layout
resultI321E120 = E 0

exampleI321E121 :: Text
exampleI321E121 =
  " \t       one\n\
  \    \t two\n\
  \ \t three\n\
  \"

resultI321E121 :: Layout
resultI321E121 = E 0

exampleI321E200 :: Text
exampleI321E200 =
  "    \t    one\n\
  \      two\n\
  \   three\n\
  \"

resultI321E200 :: Layout
resultI321E200 =
  let
    pt1 = "    \t    "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = "      "
    p2 = Prefix pt2
    l2 = rel 13 $ Lex.lex $ pt2 <> "two\n"
    pt3 = "   "
    p3 = Prefix pt3
    l3 = rel 23 $ Lex.lex $ pt3 <> "three\n"
  in
    V 31
      ((Cat.singleton $ Run p1 (Cat.singleton l1) l1 Empty p1) <>
       (Cat.singleton $ Run p2 (Cat.singleton l2) l2 (Cat.singleton $ LayoutMismatch 13 p1 p2) p2))
      (Run p3 (Cat.singleton l3) l3 Empty p3)
      Empty

exampleI321E201 :: Text
exampleI321E201 =
  "    \t    one\n\
  \      two\n\
  \ \t three\n\
  \"

resultI321E201 :: Layout
resultI321E201 =
  let
    pt1 = "    \t    "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = "      "
    p2 = Prefix pt2
    l2 = rel 13 $ Lex.lex $ pt2 <> "two\n"
    pt3 = " \t "
    p3 = Prefix pt3
    l3 = rel 23 $ Lex.lex $ pt3 <> "three\n"
  in
    V 31
      Empty
      (Run p1 (Cat.singleton l1) l1 Empty p1)
      ((Rev . Cat.singleton $ Run p2 (Cat.singleton l2) l2 (Cat.singleton $ LayoutMismatch 13 p1 p2) p2) <>
       (Rev . Cat.singleton $ Run p3 (Cat.singleton l3) l3 (Cat.singleton $ LayoutMismatch 23 p2 p3 ) p3))

exampleI321E210 :: Text
exampleI321E210 =
  "    \t    one\n\
  \ \t    two\n\
  \   three\n\
  \"

resultI321E210 :: Layout
resultI321E210 =
  let
    pt1 = "    \t    "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = " \t    "
    p2 = Prefix pt2
    l2 = rel 13 $ Lex.lex $ pt2 <> "two\n"
    pt3 = "   "
    p3 = Prefix pt3
    l3 = rel 23 $ Lex.lex $ pt3 <> "three\n"
  in
    V 31
      Empty
      (Run p1 (Cat.singleton l1) l1 Empty p1)
      ((Rev . Cat.singleton $ Run p2 (Cat.singleton l2) l2 (Cat.singleton $ LayoutMismatch 13 p1 p2) p2) <>
       (Rev . Cat.singleton $ Run p3 (Cat.singleton l3) l3 (Cat.singleton $ LayoutMismatch 23 p2 p3 ) p3))


exampleI321E211 :: Text
exampleI321E211 =
  "    \t    one\n\
  \ \t    two\n\
  \ \t three\n\
  \"

resultI321E211 :: Layout
resultI321E211 =
  let
    pt1 = "    \t    "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = " \t    "
    p2 = Prefix pt2
    l2 = rel 13 $ Lex.lex $ pt2 <> "two\n"
    pt3 = " \t "
    p3 = Prefix pt3
    l3 = rel 23 $ Lex.lex $ pt3 <> "three\n"
  in
    V 31
      Empty
      (Run p1 (Cat.singleton l1) l1 Empty p1)
      ((Rev . Cat.singleton $ Run p2 (Cat.singleton l2) l2 (Cat.singleton $ LayoutMismatch 13 p1 p2) p2) <>
       (Rev . Cat.singleton $ Run p3 (Cat.singleton l3) l3 Empty p3))

exampleI321E220 :: Text
exampleI321E220 =
  "    \t    one\n\
  \    \t two\n\
  \   three\n\
  \"

resultI321E220 :: Layout
resultI321E220 =
  let
    pt1 = "    \t    "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = "    \t "
    p2 = Prefix pt2
    l2 = rel 13 $ Lex.lex $ pt2 <> "two\n"
    pt3 = "   "
    p3 = Prefix pt3
    l3 = rel 23 $ Lex.lex $ pt3 <> "three\n"
  in
    V 31
      ((Cat.singleton $ Run p1 (Cat.singleton l1) l1 Empty p1) <>
       (Cat.singleton $ Run p2 (Cat.singleton l2) l2 Empty p2))
      (Run p3 (Cat.singleton l3) l3 Empty p3)
      Empty

exampleI321E221 :: Text
exampleI321E221 =
  "    \t    one\n\
  \    \t two\n\
  \ \t three\n\
  \"

resultI321E221 :: Layout
resultI321E221 =
  let
    pt1 = "    \t    "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = "    \t "
    p2 = Prefix pt2
    l2 = rel 13 $ Lex.lex $ pt2 <> "two\n"
    pt3 = " \t "
    p3 = Prefix pt3
    l3 = rel 23 $ Lex.lex $ pt3 <> "three\n"
  in
    V 31
      (Cat.singleton $ Run p1 (Cat.singleton l1) l1 Empty p1)
      (Run p2 (Cat.singleton l2) l2 Empty p2)
      (Rev . Cat.singleton $ Run p3 (Cat.singleton l3) l3 (Cat.singleton $ LayoutMismatch 23 p2 p3) p3)

exampleI321E300 :: Text
exampleI321E300 =
  "       \t one\n\
  \      two\n\
  \   three\n\
  \"

resultI321E300 :: Layout
resultI321E300 =
  let
    pt1 = "       \t "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = "      "
    p2 = Prefix pt2
    l2 = rel 13 $ Lex.lex $ pt2 <> "two\n"
    pt3 = "   "
    p3 = Prefix pt3
    l3 = rel 23 $ Lex.lex $ pt3 <> "three\n"
  in
    V 31
      ((Cat.singleton $ Run p1 (Cat.singleton l1) l1 Empty p1) <>
       (Cat.singleton $ Run p2 (Cat.singleton l2) l2 Empty p2))
      (Run p3 (Cat.singleton l3) l3 Empty p3)
      Empty

exampleI321E301 :: Text
exampleI321E301 =
  "       \t one\n\
  \      two\n\
  \ \t three\n\
  \"

resultI321E301 :: Layout
resultI321E301 =
  let
    pt1 = "       \t "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = "      "
    p2 = Prefix pt2
    l2 = rel 13 $ Lex.lex $ pt2 <> "two\n"
    pt3 = " \t "
    p3 = Prefix pt3
    l3 = rel 23 $ Lex.lex $ pt3 <> "three\n"
  in
    V 31
      (Cat.singleton $ Run p1 (Cat.singleton l1) l1 Empty p1)
      (Run p2 (Cat.singleton l2) l2 Empty p2)
      (Rev . Cat.singleton $ Run p3 (Cat.singleton l3) l3 (Cat.singleton $ LayoutMismatch 23 p2 p3) p3)

exampleI321E310 :: Text
exampleI321E310 =
  "       \t one\n\
  \ \t    two\n\
  \   three\n\
  \"

resultI321E310 :: Layout
resultI321E310 =
  let
    pt1 = "       \t "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = " \t    "
    p2 = Prefix pt2
    l2 = rel 13 $ Lex.lex $ pt2 <> "two\n"
    pt3 = "   "
    p3 = Prefix pt3
    l3 = rel 23 $ Lex.lex $ pt3 <> "three\n"
  in
    V 31
      Empty
      (Run p1 (Cat.singleton l1) l1 Empty p1)
      ((Rev . Cat.singleton $ Run p2 (Cat.singleton l2) l2 (Cat.singleton $ LayoutMismatch 13 p1 p2) p2) <>
       (Rev . Cat.singleton $ Run p3 (Cat.singleton l3) l3 (Cat.singleton $ LayoutMismatch 23 p2 p3) p3))

exampleI321E311 :: Text
exampleI321E311 =
  "       \t one\n\
  \ \t    two\n\
  \ \t three\n\
  \"

resultI321E311 :: Layout
resultI321E311 =
  let
    pt1 = "       \t "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = " \t    "
    p2 = Prefix pt2
    l2 = rel 13 $ Lex.lex $ pt2 <> "two\n"
    pt3 = " \t "
    p3 = Prefix pt3
    l3 = rel 23 $ Lex.lex $ pt3 <> "three\n"
  in
    V 31
      Empty
      (Run p1 (Cat.singleton l1) l1 Empty p1)
      ((Rev . Cat.singleton $ Run p2 (Cat.singleton l2) l2 (Cat.singleton $ LayoutMismatch 13 p1 p2) p2) <>
       (Rev . Cat.singleton $ Run p3 (Cat.singleton l3) l3 Empty p3))

exampleI321E320 :: Text
exampleI321E320 =
  "       \t one\n\
  \    \t two\n\
  \   three\n\
  \"

resultI321E320 :: Layout
resultI321E320 =
  let
    pt1 = "       \t "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = "    \t "
    p2 = Prefix pt2
    l2 = rel 13 $ Lex.lex $ pt2 <> "two\n"
    pt3 = "   "
    p3 = Prefix pt3
    l3 = rel 23 $ Lex.lex $ pt3 <> "three\n"
  in
    V 31
      ((Cat.singleton $ Run p1 (Cat.singleton l1) l1 Empty p1) <>
       (Cat.singleton $ Run p2 (Cat.singleton l2) l2 (Cat.singleton $ LayoutMismatch 13 p1 p2) p2))
      (Run p3 (Cat.singleton l3) l3 Empty p3)
      Empty

exampleI321E321 :: Text
exampleI321E321 =
  "       \t one\n\
  \    \t two\n\
  \ \t three\n\
  \"

resultI321E321 :: Layout
resultI321E321 =
  let
    pt1 = "       \t "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = "    \t "
    p2 = Prefix pt2
    l2 = rel 13 $ Lex.lex $ pt2 <> "two\n"
    pt3 = " \t "
    p3 = Prefix pt3
    l3 = rel 23 $ Lex.lex $ pt3 <> "three\n"
  in
    V 31
      Empty
      (Run p1 (Cat.singleton l1) l1 Empty p1)
      ((Rev . Cat.singleton $ Run p2 (Cat.singleton l2) l2 (Cat.singleton $ LayoutMismatch 13 p1 p2) p2) <>
       (Rev . Cat.singleton $ Run p3 (Cat.singleton l3) l3 (Cat.singleton $ LayoutMismatch 23 p2 p3) p3))

exampleI322E000 :: Text
exampleI322E000 =
  "         one\n\
  \      two\n\
  \      three\n\
  \"

resultI322E000 :: Layout
resultI322E000 =
  let
    pt1 = "         "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = "      "
    p2 = Prefix pt2
    l2 = rel 13 $ Lex.lex $ pt2 <> "two\n"
    pt3 = "      "
    p3 = Prefix pt3
    l3 = rel 23 $ Lex.lex $ pt3 <> "three\n"
  in
    V 34
      (Cat.singleton $ Run p1 (Cat.singleton l1) l1 Empty p1)
      (Run p2 (Cat.singleton l2) l2 Empty p2)
      (Rev . Cat.singleton $ Run p3 (Cat.singleton l3) l3 Empty p3)

exampleI322E001 :: Text
exampleI322E001 =
  "         one\n\
  \      two\n\
  \ \t    three\n\
  \"

resultI322E001 :: Layout
resultI322E001 =
  let
    pt1 = "         "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = "      "
    p2 = Prefix pt2
    l2 = rel 13 $ Lex.lex $ pt2 <> "two\n"
    pt3 = " \t    "
    p3 = Prefix pt3
    l3 = rel 23 $ Lex.lex $ pt3 <> "three\n"
  in
    V 34
      (Cat.singleton $ Run p1 (Cat.singleton l1) l1 Empty p1)
      (Run p2 (Cat.singleton l2) l2 Empty p2)
      (Rev . Cat.singleton $ Run p3 (Cat.singleton l3) l3 (Cat.singleton $ LayoutMismatch 23 p2 p3) p3)

exampleI322E002 :: Text
exampleI322E002 =
  "         one\n\
  \      two\n\
  \    \t three\n\
  \"

resultI322E002 :: Layout
resultI322E002 =
  let
    pt1 = "         "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = "      "
    p2 = Prefix pt2
    l2 = rel 13 $ Lex.lex $ pt2 <> "two\n"
    pt3 = "    \t "
    p3 = Prefix pt3
    l3 = rel 23 $ Lex.lex $ pt3 <> "three\n"
  in
    V 34
      (Cat.singleton $ Run p1 (Cat.singleton l1) l1 Empty p1)
      (Run p2 (Cat.singleton l2) l2 Empty p2)
      (Rev . Cat.singleton $ Run p3 (Cat.singleton l3) l3 (Cat.singleton $ LayoutMismatch 23 p2 p3) p3)

exampleI322E010 :: Text
exampleI322E010 =
  "         one\n\
  \ \t    two\n\
  \      three\n\
  \"

resultI322E010 :: Layout
resultI322E010 =
  let
    pt1 = "         "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = " \t    "
    p2 = Prefix pt2
    l2 = rel 13 $ Lex.lex $ pt2 <> "two\n"
    pt3 = "      "
    p3 = Prefix pt3
    l3 = rel 23 $ Lex.lex $ pt3 <> "three\n"
  in
    V 34
      Empty
      (Run p1 (Cat.singleton l1) l1 Empty p1)
      ((Rev . Cat.singleton $ Run p2 (Cat.singleton l2) l2 (Cat.singleton $ LayoutMismatch 13 p1 p2) p2) <>
       (Rev . Cat.singleton $ Run p3 (Cat.singleton l3) l3 (Cat.singleton $ LayoutMismatch 23 p2 p3) p3))

exampleI322E011 :: Text
exampleI322E011 =
  "         one\n\
  \ \t    two\n\
  \ \t    three\n\
  \"

resultI322E011 :: Layout
resultI322E011 =
  let
    pt1 = "         "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = " \t    "
    p2 = Prefix pt2
    l2 = rel 13 $ Lex.lex $ pt2 <> "two\n"
    pt3 = " \t    "
    p3 = Prefix pt3
    l3 = rel 23 $ Lex.lex $ pt3 <> "three\n"
  in
    V 34
      Empty
      (Run p1 (Cat.singleton l1) l1 Empty p1)
      ((Rev . Cat.singleton $ Run p2 (Cat.singleton l2) l2 (Cat.singleton $ LayoutMismatch 13 p1 p2) p2) <>
       (Rev . Cat.singleton $ Run p3 (Cat.singleton l3) l3 Empty p3))

exampleI322E012 :: Text
exampleI322E012 =
  "         one\n\
  \ \t    two\n\
  \    \t three\n\
  \"

resultI322E012 :: Layout
resultI322E012 =
  let
    pt1 = "         "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = " \t    "
    p2 = Prefix pt2
    l2 = rel 13 $ Lex.lex $ pt2 <> "two\n"
    pt3 = "    \t "
    p3 = Prefix pt3
    l3 = rel 23 $ Lex.lex $ pt3 <> "three\n"
  in
    V 34
      Empty
      (Run p1 (Cat.singleton l1) l1 Empty p1)
      ((Rev . Cat.singleton $ Run p2 (Cat.singleton l2) l2 (Cat.singleton $ LayoutMismatch 13 p1 p2) p2) <>
       (Rev . Cat.singleton $ Run p3 (Cat.singleton l3) l3 (Cat.singleton $ LayoutMismatch 23 p2 p3) p3))

exampleI322E020 :: Text
exampleI322E020 =
  "         one\n\
  \    \t two\n\
  \      three\n\
  \"

resultI322E020 :: Layout
resultI322E020 =
  let
    pt1 = "         "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = "    \t "
    p2 = Prefix pt2
    l2 = rel 13 $ Lex.lex $ pt2 <> "two\n"
    pt3 = "      "
    p3 = Prefix pt3
    l3 = rel 23 $ Lex.lex $ pt3 <> "three\n"
  in
    V 34
      Empty
      (Run p1 (Cat.singleton l1) l1 Empty p1)
      ((Rev . Cat.singleton $ Run p2 (Cat.singleton l2) l2 (Cat.singleton $ LayoutMismatch 13 p1 p2) p2) <>
       (Rev . Cat.singleton $ Run p3 (Cat.singleton l3) l3 (Cat.singleton $ LayoutMismatch 23 p2 p3) p3))

exampleI322E021 :: Text
exampleI322E021 =
  "         one\n\
  \    \t two\n\
  \ \t    three\n\
  \"

resultI322E021 :: Layout
resultI322E021 =
  let
    pt1 = "         "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = "    \t "
    p2 = Prefix pt2
    l2 = rel 13 $ Lex.lex $ pt2 <> "two\n"
    pt3 = " \t    "
    p3 = Prefix pt3
    l3 = rel 23 $ Lex.lex $ pt3 <> "three\n"
  in
    V 34
      Empty
      (Run p1 (Cat.singleton l1) l1 Empty p1)
      ((Rev . Cat.singleton $ Run p2 (Cat.singleton l2) l2 (Cat.singleton $ LayoutMismatch 13 p1 p2) p2) <>
       (Rev . Cat.singleton $ Run p3 (Cat.singleton l3) l3 (Cat.singleton $ LayoutMismatch 23 p2 p3) p3))

exampleI322E022 :: Text
exampleI322E022 =
  "         one\n\
  \    \t two\n\
  \    \t three\n\
  \"

resultI322E022 :: Layout
resultI322E022 =
  let
    pt1 = "         "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = "    \t "
    p2 = Prefix pt2
    l2 = rel 13 $ Lex.lex $ pt2 <> "two\n"
    pt3 = "    \t "
    p3 = Prefix pt3
    l3 = rel 23 $ Lex.lex $ pt3 <> "three\n"
  in
    V 34
      Empty
      (Run p1 (Cat.singleton l1) l1 Empty p1)
      ((Rev . Cat.singleton $ Run p2 (Cat.singleton l2) l2 (Cat.singleton $ LayoutMismatch 13 p1 p2) p2) <>
       (Rev . Cat.singleton $ Run p3 (Cat.singleton l3) l3 Empty p3))

exampleI322E100 :: Text
exampleI322E100 =
  " \t       one\n\
  \      two\n\
  \      three\n\
  \"

resultI322E100 :: Layout
resultI322E100 =
  let
    pt1 = " \t       "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = "      "
    p2 = Prefix pt2
    l2 = rel 13 $ Lex.lex $ pt2 <> "two\n"
    pt3 = "      "
    p3 = Prefix pt3
    l3 = rel 23 $ Lex.lex $ pt3 <> "three\n"
  in
    V 34
      Empty
      (Run p1 (Cat.singleton l1) l1 Empty p1)
      ((Rev . Cat.singleton $ Run p2 (Cat.singleton l2) l2 (Cat.singleton $ LayoutMismatch 13 p1 p2) p2) <>
       (Rev . Cat.singleton $ Run p3 (Cat.singleton l3) l3 Empty p3))

exampleI322E101 :: Text
exampleI322E101 =
  " \t       one\n\
  \      two\n\
  \ \t    three\n\
  \"

resultI322E101 :: Layout
resultI322E101 =
  let
    pt1 = " \t       "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = "      "
    p2 = Prefix pt2
    l2 = rel 13 $ Lex.lex $ pt2 <> "two\n"
    pt3 = " \t    "
    p3 = Prefix pt3
    l3 = rel 23 $ Lex.lex $ pt3 <> "three\n"
  in
    V 34
      Empty
      (Run p1 (Cat.singleton l1) l1 Empty p1)
      ((Rev . Cat.singleton $ Run p2 (Cat.singleton l2) l2 (Cat.singleton $ LayoutMismatch 13 p1 p2) p2) <>
       (Rev . Cat.singleton $ Run p3 (Cat.singleton l3) l3 (Cat.singleton $ LayoutMismatch 23 p2 p3) p3))

exampleI322E102 :: Text
exampleI322E102 =
  " \t       one\n\
  \      two\n\
  \    \t three\n\
  \"

resultI322E102 :: Layout
resultI322E102 =
  let
    pt1 = " \t       "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = "      "
    p2 = Prefix pt2
    l2 = rel 13 $ Lex.lex $ pt2 <> "two\n"
    pt3 = "    \t "
    p3 = Prefix pt3
    l3 = rel 23 $ Lex.lex $ pt3 <> "three\n"
  in
    V 34
      Empty
      (Run p1 (Cat.singleton l1) l1 Empty p1)
      ((Rev . Cat.singleton $ Run p2 (Cat.singleton l2) l2 (Cat.singleton $ LayoutMismatch 13 p1 p2) p2) <>
       (Rev . Cat.singleton $ Run p3 (Cat.singleton l3) l3 (Cat.singleton $ LayoutMismatch 23 p2 p3) p3))

exampleI322E110 :: Text
exampleI322E110 =
  " \t       one\n\
  \ \t    two\n\
  \      three\n\
  \"

resultI322E110 :: Layout
resultI322E110 =
  let
    pt1 = " \t       "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = " \t    "
    p2 = Prefix pt2
    l2 = rel 13 $ Lex.lex $ pt2 <> "two\n"
    pt3 = "      "
    p3 = Prefix pt3
    l3 = rel 23 $ Lex.lex $ pt3 <> "three\n"
  in
    V 34
      (Cat.singleton $ Run p1 (Cat.singleton l1) l1 Empty p1)
      (Run p2 (Cat.singleton l2) l2 Empty p2)
      (Rev . Cat.singleton $ Run p3 (Cat.singleton l3) l3 (Cat.singleton $ LayoutMismatch 23 p2 p3) p3)

exampleI322E111 :: Text
exampleI322E111 =
  " \t       one\n\
  \ \t    two\n\
  \ \t    three\n\
  \"

resultI322E111 :: Layout
resultI322E111 =
  let
    pt1 = " \t       "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = " \t    "
    p2 = Prefix pt2
    l2 = rel 13 $ Lex.lex $ pt2 <> "two\n"
    pt3 = " \t    "
    p3 = Prefix pt3
    l3 = rel 23 $ Lex.lex $ pt3 <> "three\n"
  in
    V 34
      (Cat.singleton $ Run p1 (Cat.singleton l1) l1 Empty p1)
      (Run p2 (Cat.singleton l2) l2 Empty p2)
      (Rev . Cat.singleton $ Run p3 (Cat.singleton l3) l3 Empty p3)

exampleI322E112 :: Text
exampleI322E112 =
  " \t       one\n\
  \ \t    two\n\
  \    \t three\n\
  \"

resultI322E112 :: Layout
resultI322E112 =
  let
    pt1 = " \t       "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = " \t    "
    p2 = Prefix pt2
    l2 = rel 13 $ Lex.lex $ pt2 <> "two\n"
    pt3 = "    \t "
    p3 = Prefix pt3
    l3 = rel 23 $ Lex.lex $ pt3 <> "three\n"
  in
    V 34
      (Cat.singleton $ Run p1 (Cat.singleton l1) l1 Empty p1)
      (Run p2 (Cat.singleton l2) l2 Empty p2)
      (Rev . Cat.singleton $ Run p3 (Cat.singleton l3) l3 (Cat.singleton $ LayoutMismatch 23 p2 p3) p3)

exampleI322E120 :: Text
exampleI322E120 =
  " \t       one\n\
  \    \t two\n\
  \      three\n\
  \"

resultI322E120 :: Layout
resultI322E120 =
  let
    pt1 = " \t       "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = "    \t "
    p2 = Prefix pt2
    l2 = rel 13 $ Lex.lex $ pt2 <> "two\n"
    pt3 = "      "
    p3 = Prefix pt3
    l3 = rel 23 $ Lex.lex $ pt3 <> "three\n"
  in
    V 34
      Empty
      (Run p1 (Cat.singleton l1) l1 Empty p1)
      ((Rev . Cat.singleton $ Run p2 (Cat.singleton l2) l2 (Cat.singleton $ LayoutMismatch 13 p1 p2) p2) <>
       (Rev . Cat.singleton $ Run p3 (Cat.singleton l3) l3 (Cat.singleton $ LayoutMismatch 23 p2 p3) p3))

exampleI322E121 :: Text
exampleI322E121 =
  " \t       one\n\
  \    \t two\n\
  \ \t    three\n\
  \"

resultI322E121 :: Layout
resultI322E121 =
  let
    pt1 = " \t       "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = "    \t "
    p2 = Prefix pt2
    l2 = rel 13 $ Lex.lex $ pt2 <> "two\n"
    pt3 = " \t    "
    p3 = Prefix pt3
    l3 = rel 23 $ Lex.lex $ pt3 <> "three\n"
  in
    V 34
      Empty
      (Run p1 (Cat.singleton l1) l1 Empty p1)
      ((Rev . Cat.singleton $ Run p2 (Cat.singleton l2) l2 (Cat.singleton $ LayoutMismatch 13 p1 p2) p2) <>
       (Rev . Cat.singleton $ Run p3 (Cat.singleton l3) l3 (Cat.singleton $ LayoutMismatch 23 p2 p3) p3))

exampleI322E122 :: Text
exampleI322E122 =
  " \t       one\n\
  \    \t two\n\
  \    \t three\n\
  \"

resultI322E122 :: Layout
resultI322E122 =
  let
    pt1 = " \t       "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = "    \t "
    p2 = Prefix pt2
    l2 = rel 13 $ Lex.lex $ pt2 <> "two\n"
    pt3 = "    \t "
    p3 = Prefix pt3
    l3 = rel 23 $ Lex.lex $ pt3 <> "three\n"
  in
    V 34
      Empty
      (Run p1 (Cat.singleton l1) l1 Empty p1)
      ((Rev . Cat.singleton $ Run p2 (Cat.singleton l2) l2 (Cat.singleton $ LayoutMismatch 13 p1 p2) p2) <>
       (Rev . Cat.singleton $ Run p3 (Cat.singleton l3) l3 Empty p3))

exampleI322E200 :: Text
exampleI322E200 =
  "    \t    one\n\
  \      two\n\
  \      three\n\
  \"

resultI322E200 :: Layout
resultI322E200 =
  let
    pt1 = "    \t    "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = "      "
    p2 = Prefix pt2
    l2 = rel 13 $ Lex.lex $ pt2 <> "two\n"
    pt3 = "      "
    p3 = Prefix pt3
    l3 = rel 23 $ Lex.lex $ pt3 <> "three\n"
  in
    V 34
      Empty
      (Run p1 (Cat.singleton l1) l1 Empty p1)
      ((Rev . Cat.singleton $ Run p2 (Cat.singleton l2) l2 (Cat.singleton $ LayoutMismatch 13 p1 p2) p2) <>
       (Rev . Cat.singleton $ Run p3 (Cat.singleton l3) l3 Empty p3))

exampleI322E201 :: Text
exampleI322E201 =
  "    \t    one\n\
  \      two\n\
  \ \t    three\n\
  \"

resultI322E201 :: Layout
resultI322E201 =
  let
    pt1 = "    \t    "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = "      "
    p2 = Prefix pt2
    l2 = rel 13 $ Lex.lex $ pt2 <> "two\n"
    pt3 = " \t    "
    p3 = Prefix pt3
    l3 = rel 23 $ Lex.lex $ pt3 <> "three\n"
  in
    V 34
      Empty
      (Run p1 (Cat.singleton l1) l1 Empty p1)
      ((Rev . Cat.singleton $ Run p2 (Cat.singleton l2) l2 (Cat.singleton $ LayoutMismatch 13 p1 p2) p2) <>
       (Rev . Cat.singleton $ Run p3 (Cat.singleton l3) l3 (Cat.singleton $ LayoutMismatch 23 p2 p3) p3))

exampleI322E202 :: Text
exampleI322E202 =
  "    \t    one\n\
  \      two\n\
  \    \t three\n\
  \"

resultI322E202 :: Layout
resultI322E202 =
  let
    pt1 = "    \t    "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = "      "
    p2 = Prefix pt2
    l2 = rel 13 $ Lex.lex $ pt2 <> "two\n"
    pt3 = "    \t "
    p3 = Prefix pt3
    l3 = rel 23 $ Lex.lex $ pt3 <> "three\n"
  in
    V 34
      Empty
      (Run p1 (Cat.singleton l1) l1 Empty p1)
      ((Rev . Cat.singleton $ Run p2 (Cat.singleton l2) l2 (Cat.singleton $ LayoutMismatch 13 p1 p2) p2) <>
       (Rev . Cat.singleton $ Run p3 (Cat.singleton l3) l3 (Cat.singleton $ LayoutMismatch 23 p2 p3) p3))

exampleI322E210 :: Text
exampleI322E210 =
  "    \t    one\n\
  \ \t    two\n\
  \      three\n\
  \"

resultI322E210 :: Layout
resultI322E210 =
  let
    pt1 = "    \t    "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = " \t    "
    p2 = Prefix pt2
    l2 = rel 13 $ Lex.lex $ pt2 <> "two\n"
    pt3 = "      "
    p3 = Prefix pt3
    l3 = rel 23 $ Lex.lex $ pt3 <> "three\n"
  in
    V 34
      Empty
      (Run p1 (Cat.singleton l1) l1 Empty p1)
      ((Rev . Cat.singleton $ Run p2 (Cat.singleton l2) l2 (Cat.singleton $ LayoutMismatch 13 p1 p2) p2) <>
       (Rev . Cat.singleton $ Run p3 (Cat.singleton l3) l3 (Cat.singleton $ LayoutMismatch 23 p2 p3) p3))

exampleI322E211 :: Text
exampleI322E211 =
  "    \t    one\n\
  \ \t    two\n\
  \ \t    three\n\
  \"

resultI322E211 :: Layout
resultI322E211 =
  let
    pt1 = "    \t    "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = " \t    "
    p2 = Prefix pt2
    l2 = rel 13 $ Lex.lex $ pt2 <> "two\n"
    pt3 = " \t    "
    p3 = Prefix pt3
    l3 = rel 23 $ Lex.lex $ pt3 <> "three\n"
  in
    V 34
      Empty
      (Run p1 (Cat.singleton l1) l1 Empty p1)
      ((Rev . Cat.singleton $ Run p2 (Cat.singleton l2) l2 (Cat.singleton $ LayoutMismatch 13 p1 p2) p2) <>
       (Rev . Cat.singleton $ Run p3 (Cat.singleton l3) l3 Empty p3))

exampleI322E212 :: Text
exampleI322E212 =
  "    \t    one\n\
  \ \t    two\n\
  \    \t three\n\
  \"

resultI322E212 :: Layout
resultI322E212 =
  let
    pt1 = "    \t    "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = " \t    "
    p2 = Prefix pt2
    l2 = rel 13 $ Lex.lex $ pt2 <> "two\n"
    pt3 = "    \t "
    p3 = Prefix pt3
    l3 = rel 23 $ Lex.lex $ pt3 <> "three\n"
  in
    V 34
      Empty
      (Run p1 (Cat.singleton l1) l1 Empty p1)
      ((Rev . Cat.singleton $ Run p2 (Cat.singleton l2) l2 (Cat.singleton $ LayoutMismatch 13 p1 p2) p2) <>
       (Rev . Cat.singleton $ Run p3 (Cat.singleton l3) l3 (Cat.singleton $ LayoutMismatch 23 p2 p3) p3))

exampleI322E220 :: Text
exampleI322E220 =
  "    \t    one\n\
  \    \t two\n\
  \      three\n\
  \"

resultI322E220 :: Layout
resultI322E220 =
  let
    pt1 = "    \t    "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = "    \t "
    p2 = Prefix pt2
    l2 = rel 13 $ Lex.lex $ pt2 <> "two\n"
    pt3 = "      "
    p3 = Prefix pt3
    l3 = rel 23 $ Lex.lex $ pt3 <> "three\n"
  in
    V 34
      (Cat.singleton $ Run p1 (Cat.singleton l1) l1 Empty p1)
      (Run p2 (Cat.singleton l2) l2 Empty p2)
      (Rev . Cat.singleton $ Run p3 (Cat.singleton l3) l3 (Cat.singleton $ LayoutMismatch 23 p2 p3) p3)

exampleI322E221 :: Text
exampleI322E221 =
  "    \t    one\n\
  \    \t two\n\
  \ \t    three\n\
  \"

resultI322E221 :: Layout
resultI322E221 =
  let
    pt1 = "    \t    "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = "    \t "
    p2 = Prefix pt2
    l2 = rel 13 $ Lex.lex $ pt2 <> "two\n"
    pt3 = " \t    "
    p3 = Prefix pt3
    l3 = rel 23 $ Lex.lex $ pt3 <> "three\n"
  in
    V 34
      (Cat.singleton $ Run p1 (Cat.singleton l1) l1 Empty p1)
      (Run p2 (Cat.singleton l2) l2 Empty p2)
      (Rev . Cat.singleton $ Run p3 (Cat.singleton l3) l3 (Cat.singleton $ LayoutMismatch 23 p2 p3) p3)

exampleI322E222 :: Text
exampleI322E222 =
  "    \t    one\n\
  \    \t two\n\
  \    \t three\n\
  \"

resultI322E222 :: Layout
resultI322E222 =
  let
    pt1 = "    \t    "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = "    \t "
    p2 = Prefix pt2
    l2 = rel 13 $ Lex.lex $ pt2 <> "two\n"
    pt3 = "    \t "
    p3 = Prefix pt3
    l3 = rel 23 $ Lex.lex $ pt3 <> "three\n"
  in
    V 34
      (Cat.singleton $ Run p1 (Cat.singleton l1) l1 Empty p1)
      (Run p2 (Cat.singleton l2) l2 Empty p2)
      (Rev . Cat.singleton $ Run p3 (Cat.singleton l3) l3 Empty p3)

exampleI322E300 :: Text
exampleI322E300 =
  "       \t one\n\
  \      two\n\
  \      three\n\
  \"

resultI322E300 :: Layout
resultI322E300 =
  let
    pt1 = "       \t "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = "      "
    p2 = Prefix pt2
    l2 = rel 13 $ Lex.lex $ pt2 <> "two\n"
    pt3 = "      "
    p3 = Prefix pt3
    l3 = rel 23 $ Lex.lex $ pt3 <> "three\n"
  in
    V 34
      (Cat.singleton $ Run p1 (Cat.singleton l1) l1 Empty p1)
      (Run p2 (Cat.singleton l2) l2 Empty p2)
      (Rev . Cat.singleton $ Run p3 (Cat.singleton l3) l3 Empty p3)

exampleI322E301 :: Text
exampleI322E301 =
  "       \t one\n\
  \      two\n\
  \ \t    three\n\
  \"

resultI322E301 :: Layout
resultI322E301 =
  let
    pt1 = "       \t "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = "      "
    p2 = Prefix pt2
    l2 = rel 13 $ Lex.lex $ pt2 <> "two\n"
    pt3 = " \t    "
    p3 = Prefix pt3
    l3 = rel 23 $ Lex.lex $ pt3 <> "three\n"
  in
    V 34
      (Cat.singleton $ Run p1 (Cat.singleton l1) l1 Empty p1)
      (Run p2 (Cat.singleton l2) l2 Empty p2)
      (Rev . Cat.singleton $ Run p3 (Cat.singleton l3) l3 (Cat.singleton $ LayoutMismatch 23 p2 p3) p3)

exampleI322E302 :: Text
exampleI322E302 =
  "       \t one\n\
  \      two\n\
  \    \t three\n\
  \"

resultI322E302 :: Layout
resultI322E302 =
  let
    pt1 = "       \t "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = "      "
    p2 = Prefix pt2
    l2 = rel 13 $ Lex.lex $ pt2 <> "two\n"
    pt3 = "    \t "
    p3 = Prefix pt3
    l3 = rel 23 $ Lex.lex $ pt3 <> "three\n"
  in
    V 34
      (Cat.singleton $ Run p1 (Cat.singleton l1) l1 Empty p1)
      (Run p2 (Cat.singleton l2) l2 Empty p2)
      (Rev . Cat.singleton $ Run p3 (Cat.singleton l3) l3 (Cat.singleton $ LayoutMismatch 23 p2 p3) p3)

exampleI322E310 :: Text
exampleI322E310 =
  "       \t one\n\
  \ \t    two\n\
  \      three\n\
  \"

resultI322E310 :: Layout
resultI322E310 =
  let
    pt1 = "       \t "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = " \t    "
    p2 = Prefix pt2
    l2 = rel 13 $ Lex.lex $ pt2 <> "two\n"
    pt3 = "      "
    p3 = Prefix pt3
    l3 = rel 23 $ Lex.lex $ pt3 <> "three\n"
  in
    V 34
      Empty
      (Run p1 (Cat.singleton l1) l1 Empty p1)
      ((Rev . Cat.singleton $ Run p2 (Cat.singleton l2) l2 (Cat.singleton $ LayoutMismatch 13 p1 p2) p2) <>
       (Rev . Cat.singleton $ Run p3 (Cat.singleton l3) l3 (Cat.singleton $ LayoutMismatch 23 p2 p3) p3))

exampleI322E311 :: Text
exampleI322E311 =
  "       \t one\n\
  \ \t    two\n\
  \ \t    three\n\
  \"

resultI322E311 :: Layout
resultI322E311 =
  let
    pt1 = "       \t "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = " \t    "
    p2 = Prefix pt2
    l2 = rel 13 $ Lex.lex $ pt2 <> "two\n"
    pt3 = " \t    "
    p3 = Prefix pt3
    l3 = rel 23 $ Lex.lex $ pt3 <> "three\n"
  in
    V 34
      Empty
      (Run p1 (Cat.singleton l1) l1 Empty p1)
      ((Rev . Cat.singleton $ Run p2 (Cat.singleton l2) l2 (Cat.singleton $ LayoutMismatch 13 p1 p2) p2) <>
       (Rev . Cat.singleton $ Run p3 (Cat.singleton l3) l3 Empty p3))

exampleI322E312 :: Text
exampleI322E312 =
  "       \t one\n\
  \ \t    two\n\
  \    \t three\n\
  \"

resultI322E312 :: Layout
resultI322E312 =
  let
    pt1 = "       \t "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = " \t    "
    p2 = Prefix pt2
    l2 = rel 13 $ Lex.lex $ pt2 <> "two\n"
    pt3 = "    \t "
    p3 = Prefix pt3
    l3 = rel 23 $ Lex.lex $ pt3 <> "three\n"
  in
    V 34
      Empty
      (Run p1 (Cat.singleton l1) l1 Empty p1)
      ((Rev . Cat.singleton $ Run p2 (Cat.singleton l2) l2 (Cat.singleton $ LayoutMismatch 13 p1 p2) p2) <>
       (Rev . Cat.singleton $ Run p3 (Cat.singleton l3) l3 (Cat.singleton $ LayoutMismatch 23 p2 p3) p3))

exampleI322E320 :: Text
exampleI322E320 =
  "       \t one\n\
  \    \t two\n\
  \      three\n\
  \"

resultI322E320 :: Layout
resultI322E320 =
  let
    pt1 = "       \t "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = "    \t "
    p2 = Prefix pt2
    l2 = rel 13 $ Lex.lex $ pt2 <> "two\n"
    pt3 = "      "
    p3 = Prefix pt3
    l3 = rel 23 $ Lex.lex $ pt3 <> "three\n"
  in
    V 34
      Empty
      (Run p1 (Cat.singleton l1) l1 Empty p1)
      ((Rev . Cat.singleton $ Run p2 (Cat.singleton l2) l2 (Cat.singleton $ LayoutMismatch 13 p1 p2) p2) <>
       (Rev . Cat.singleton $ Run p3 (Cat.singleton l3) l3 (Cat.singleton $ LayoutMismatch 23 p2 p3) p3))

exampleI322E321 :: Text
exampleI322E321 =
  "       \t one\n\
  \    \t two\n\
  \ \t    three\n\
  \"

resultI322E321 :: Layout
resultI322E321 =
  let
    pt1 = "       \t "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = "    \t "
    p2 = Prefix pt2
    l2 = rel 13 $ Lex.lex $ pt2 <> "two\n"
    pt3 = " \t    "
    p3 = Prefix pt3
    l3 = rel 23 $ Lex.lex $ pt3 <> "three\n"
  in
    V 34
      Empty
      (Run p1 (Cat.singleton l1) l1 Empty p1)
      ((Rev . Cat.singleton $ Run p2 (Cat.singleton l2) l2 (Cat.singleton $ LayoutMismatch 13 p1 p2) p2) <>
       (Rev . Cat.singleton $ Run p3 (Cat.singleton l3) l3 (Cat.singleton $ LayoutMismatch 23 p2 p3) p3))

exampleI322E322 :: Text
exampleI322E322 =
  "       \t one\n\
  \    \t two\n\
  \    \t three\n\
  \"

resultI322E322 :: Layout
resultI322E322 =
  let
    pt1 = "       \t "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = "    \t "
    p2 = Prefix pt2
    l2 = rel 13 $ Lex.lex $ pt2 <> "two\n"
    pt3 = "    \t "
    p3 = Prefix pt3
    l3 = rel 23 $ Lex.lex $ pt3 <> "three\n"
  in
    V 34
      Empty
      (Run p1 (Cat.singleton l1) l1 Empty p1)
      ((Rev . Cat.singleton $ Run p2 (Cat.singleton l2) l2 (Cat.singleton $ LayoutMismatch 13 p1 p2) p2) <>
       (Rev . Cat.singleton $ Run p3 (Cat.singleton l3) l3 Empty p3))

exampleI323E000 :: Text
exampleI323E000 =
  "         one\n\
  \      two\n\
  \         three\n\
  \"

resultI323E000 :: Layout
resultI323E000 =
  let
    pt1 = "         "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = "      "
    p2 = Prefix pt2
    l2 = rel 13 $ Lex.lex $ pt2 <> "two\n"
    pt3 = "         "
    p3 = Prefix pt3
    l3 = rel 23 $ Lex.lex $ pt3 <> "three\n"
  in
    V 37
      (Cat.singleton $ Run p1 (Cat.singleton l1) l1 Empty p1)
      (Run p2 (Cat.singleton l2 <> Cat.singleton l3) (l2 <> l3) Empty p3)
      Empty

exampleI323E001 :: Text
exampleI323E001 =
  "         one\n\
  \      two\n\
  \ \t       three\n\
  \"

resultI323E001 :: Layout
resultI323E001 =
  let
    pt1 = "         "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = "      "
    p2 = Prefix pt2
    l2 = rel 13 $ Lex.lex $ pt2 <> "two\n"
    pt3 = " \t       "
    p3 = Prefix pt3
    l3 = rel 23 $ Lex.lex $ pt3 <> "three\n"
  in
    V 37
      (Cat.singleton $ Run p1 (Cat.singleton l1) l1 Empty p1)
      (Run p2 (Cat.singleton l2) l2 Empty p2)
      (Rev . Cat.singleton $ Run p3 (Cat.singleton l3) l3 (Cat.singleton $ LayoutMismatch 23 p2 p3) p3)

exampleI323E002 :: Text
exampleI323E002 =
  "         one\n\
  \      two\n\
  \    \t    three\n\
  \"

resultI323E002 :: Layout
resultI323E002 =
  let
    pt1 = "         "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = "      "
    p2 = Prefix pt2
    l2 = rel 13 $ Lex.lex $ pt2 <> "two\n"
    pt3 = "    \t    "
    p3 = Prefix pt3
    l3 = rel 23 $ Lex.lex $ pt3 <> "three\n"
  in
    V 37
      (Cat.singleton $ Run p1 (Cat.singleton l1) l1 Empty p1)
      (Run p2 (Cat.singleton l2) l2 Empty p2)
      (Rev . Cat.singleton $ Run p3 (Cat.singleton l3) l3 (Cat.singleton $ LayoutMismatch 23 p2 p3) p3)

exampleI323E003 :: Text
exampleI323E003 =
  "         one\n\
  \      two\n\
  \       \t three\n\
  \"

resultI323E003 :: Layout
resultI323E003 =
  let
    pt1 = "         "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = "      "
    p2 = Prefix pt2
    l2 = rel 13 $ Lex.lex $ pt2 <> "two\n"
    pt3 = "       \t "
    p3 = Prefix pt3
    l3 = rel 23 $ Lex.lex $ pt3 <> "three\n"
  in
    V 37
      (Cat.singleton $ Run p1 (Cat.singleton l1) l1 Empty p1)
      (Run p2 (Cat.singleton l2 <> Cat.singleton l3) (l2 <> l3) Empty p3)
      Empty

exampleI323E010 :: Text
exampleI323E010 =
  "         one\n\
  \ \t    two\n\
  \         three\n\
  \"

resultI323E010 :: Layout
resultI323E010 =
  let
    pt1 = "         "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = " \t    "
    p2 = Prefix pt2
    l2 = rel 13 $ Lex.lex $ pt2 <> "two\n"
    pt3 = "         "
    p3 = Prefix pt3
    l3 = rel 23 $ Lex.lex $ pt3 <> "three\n"
  in
    V 37
      Empty
      (Run p1 (Cat.singleton l1) l1 Empty p1)
      ((Rev . Cat.singleton $ Run p2 (Cat.singleton l2) l2 (Cat.singleton $ LayoutMismatch 13 p1 p2) p2) <>
       (Rev . Cat.singleton $ Run p3 (Cat.singleton l3) l3 (Cat.singleton $ LayoutMismatch 23 p2 p3) p3))

exampleI323E011 :: Text
exampleI323E011 =
  "         one\n\
  \ \t    two\n\
  \ \t       three\n\
  \"

resultI323E011 :: Layout
resultI323E011 =
  let
    pt1 = "         "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = " \t    "
    p2 = Prefix pt2
    l2 = rel 13 $ Lex.lex $ pt2 <> "two\n"
    pt3 = " \t       "
    p3 = Prefix pt3
    l3 = rel 23 $ Lex.lex $ pt3 <> "three\n"
  in
    V 37
      Empty
      (Run p1 (Cat.singleton l1) l1 Empty p1)
      (Rev . Cat.singleton $ Run p2 (Cat.singleton l2 <> Cat.singleton l3) (l2 <> l3) (Cat.singleton $ LayoutMismatch 13 p1 p2) p3)

exampleI323E012 :: Text
exampleI323E012 =
  "         one\n\
  \ \t    two\n\
  \    \t    three\n\
  \"

resultI323E012 :: Layout
resultI323E012 =
  let
    pt1 = "         "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = " \t    "
    p2 = Prefix pt2
    l2 = rel 13 $ Lex.lex $ pt2 <> "two\n"
    pt3 = "    \t    "
    p3 = Prefix pt3
    l3 = rel 23 $ Lex.lex $ pt3 <> "three\n"
  in
    V 37
      Empty
      (Run p1 (Cat.singleton l1) l1 Empty p1)
      ((Rev . Cat.singleton $ Run p2 (Cat.singleton l2) l2 (Cat.singleton $ LayoutMismatch 13 p1 p2) p2) <>
       (Rev . Cat.singleton $ Run p3 (Cat.singleton l3) l3 (Cat.singleton $ LayoutMismatch 23 p2 p3) p3))

exampleI323E013 :: Text
exampleI323E013 =
  "         one\n\
  \ \t    two\n\
  \       \t three\n\
  \"

resultI323E013 :: Layout
resultI323E013 =
  let
    pt1 = "         "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = " \t    "
    p2 = Prefix pt2
    l2 = rel 13 $ Lex.lex $ pt2 <> "two\n"
    pt3 = "       \t "
    p3 = Prefix pt3
    l3 = rel 23 $ Lex.lex $ pt3 <> "three\n"
  in
    V 37
      Empty
      (Run p1 (Cat.singleton l1) l1 Empty p1)
      ((Rev . Cat.singleton $ Run p2 (Cat.singleton l2) l2 (Cat.singleton $ LayoutMismatch 13 p1 p2) p2) <>
       (Rev . Cat.singleton $ Run p3 (Cat.singleton l3) l3 (Cat.singleton $ LayoutMismatch 23 p2 p3) p3))

exampleI323E020 :: Text
exampleI323E020 =
  "         one\n\
  \    \t two\n\
  \         three\n\
  \"

resultI323E020 :: Layout
resultI323E020 =
  let
    pt1 = "         "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = "    \t "
    p2 = Prefix pt2
    l2 = rel 13 $ Lex.lex $ pt2 <> "two\n"
    pt3 = "         "
    p3 = Prefix pt3
    l3 = rel 23 $ Lex.lex $ pt3 <> "three\n"
  in
    V 37
      Empty
      (Run p1 (Cat.singleton l1) l1 Empty p1)
      ((Rev . Cat.singleton $ Run p2 (Cat.singleton l2) l2 (Cat.singleton $ LayoutMismatch 13 p1 p2) p2) <>
       (Rev . Cat.singleton $ Run p3 (Cat.singleton l3) l3 (Cat.singleton $ LayoutMismatch 23 p2 p3) p3))

exampleI323E021 :: Text
exampleI323E021 =
  "         one\n\
  \    \t two\n\
  \ \t       three\n\
  \"

resultI323E021 :: Layout
resultI323E021 =
  let
    pt1 = "         "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = "    \t "
    p2 = Prefix pt2
    l2 = rel 13 $ Lex.lex $ pt2 <> "two\n"
    pt3 = " \t       "
    p3 = Prefix pt3
    l3 = rel 23 $ Lex.lex $ pt3 <> "three\n"
  in
    V 37
      Empty
      (Run p1 (Cat.singleton l1) l1 Empty p1)
      ((Rev . Cat.singleton $ Run p2 (Cat.singleton l2) l2 (Cat.singleton $ LayoutMismatch 13 p1 p2) p2) <>
       (Rev . Cat.singleton $ Run p3 (Cat.singleton l3) l3 (Cat.singleton $ LayoutMismatch 23 p2 p3) p3))

exampleI323E022 :: Text
exampleI323E022 =
  "         one\n\
  \    \t two\n\
  \    \t    three\n\
  \"

resultI323E022 :: Layout
resultI323E022 =
  let
    pt1 = "         "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = "    \t "
    p2 = Prefix pt2
    l2 = rel 13 $ Lex.lex $ pt2 <> "two\n"
    pt3 = "    \t    "
    p3 = Prefix pt3
    l3 = rel 23 $ Lex.lex $ pt3 <> "three\n"
  in
    V 37
      Empty
      (Run p1 (Cat.singleton l1) l1 Empty p1)
      (Rev . Cat.singleton $ Run p2 (Cat.singleton l2 <> Cat.singleton l3) (l2 <> l3) (Cat.singleton $ LayoutMismatch 13 p1 p2) p3)

exampleI323E023 :: Text
exampleI323E023 =
  "         one\n\
  \    \t two\n\
  \       \t three\n\
  \"

resultI323E023 :: Layout
resultI323E023 =
  let
    pt1 = "         "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = "    \t "
    p2 = Prefix pt2
    l2 = rel 13 $ Lex.lex $ pt2 <> "two\n"
    pt3 = "       \t "
    p3 = Prefix pt3
    l3 = rel 23 $ Lex.lex $ pt3 <> "three\n"
  in
    V 37
      Empty
      (Run p1 (Cat.singleton l1) l1 Empty p1)
      ((Rev . Cat.singleton $ Run p2 (Cat.singleton l2) l2 (Cat.singleton $ LayoutMismatch 13 p1 p2) p2) <>
       (Rev . Cat.singleton $ Run p3 (Cat.singleton l3) l3 (Cat.singleton $ LayoutMismatch 23 p2 p3) p3))

exampleI323E100 :: Text
exampleI323E100 =
  " \t       one\n\
  \      two\n\
  \         three\n\
  \"

resultI323E100 :: Layout
resultI323E100 =
  let
    pt1 = " \t       "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = "      "
    p2 = Prefix pt2
    l2 = rel 13 $ Lex.lex $ pt2 <> "two\n"
    pt3 = "         "
    p3 = Prefix pt3
    l3 = rel 23 $ Lex.lex $ pt3 <> "three\n"
  in
    V 37
      Empty
      (Run p1 (Cat.singleton l1) l1 Empty p1)
      (Rev . Cat.singleton $ Run p2 (Cat.singleton l2 <> Cat.singleton l3) (l2 <> l3) (Cat.singleton $ LayoutMismatch 13 p1 p2) p3)

exampleI323E101 :: Text
exampleI323E101 =
  " \t       one\n\
  \      two\n\
  \ \t       three\n\
  \"

resultI323E101 :: Layout
resultI323E101 =
  let
    pt1 = " \t       "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = "      "
    p2 = Prefix pt2
    l2 = rel 13 $ Lex.lex $ pt2 <> "two\n"
    pt3 = " \t       "
    p3 = Prefix pt3
    l3 = rel 23 $ Lex.lex $ pt3 <> "three\n"
  in
    V 37
      Empty
      (Run p1 (Cat.singleton l1) l1 Empty p1)
      ((Rev . Cat.singleton $ Run p2 (Cat.singleton l2) l2 (Cat.singleton $ LayoutMismatch 13 p1 p2) p2) <>
       (Rev . Cat.singleton $ Run p3 (Cat.singleton l3) l3 (Cat.singleton $ LayoutMismatch 23 p2 p3) p3))

exampleI323E102 :: Text
exampleI323E102 =
  " \t       one\n\
  \      two\n\
  \    \t    three\n\
  \"

resultI323E102 :: Layout
resultI323E102 =
  let
    pt1 = " \t       "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = "      "
    p2 = Prefix pt2
    l2 = rel 13 $ Lex.lex $ pt2 <> "two\n"
    pt3 = "    \t    "
    p3 = Prefix pt3
    l3 = rel 23 $ Lex.lex $ pt3 <> "three\n"
  in
    V 37
      Empty
      (Run p1 (Cat.singleton l1) l1 Empty p1)
      ((Rev . Cat.singleton $ Run p2 (Cat.singleton l2) l2 (Cat.singleton $ LayoutMismatch 13 p1 p2) p2) <>
       (Rev . Cat.singleton $ Run p3 (Cat.singleton l3) l3 (Cat.singleton $ LayoutMismatch 23 p2 p3) p3))

exampleI323E103 :: Text
exampleI323E103 =
  " \t       one\n\
  \      two\n\
  \       \t three\n\
  \"

resultI323E103 :: Layout
resultI323E103 =
  let
    pt1 = " \t       "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = "      "
    p2 = Prefix pt2
    l2 = rel 13 $ Lex.lex $ pt2 <> "two\n"
    pt3 = "       \t "
    p3 = Prefix pt3
    l3 = rel 23 $ Lex.lex $ pt3 <> "three\n"
  in
    V 37
      Empty
      (Run p1 (Cat.singleton l1) l1 Empty p1)
      (Rev . Cat.singleton $ Run p2 (Cat.singleton l2 <> Cat.singleton l3) (l2 <> l3) (Cat.singleton $ LayoutMismatch 13 p1 p2) p3)

exampleI323E110 :: Text
exampleI323E110 =
  " \t       one\n\
  \ \t    two\n\
  \         three\n\
  \"

resultI323E110 :: Layout
resultI323E110 =
  let
    pt1 = " \t       "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = " \t    "
    p2 = Prefix pt2
    l2 = rel 13 $ Lex.lex $ pt2 <> "two\n"
    pt3 = "         "
    p3 = Prefix pt3
    l3 = rel 23 $ Lex.lex $ pt3 <> "three\n"
  in
    V 37
      (Cat.singleton $ Run p1 (Cat.singleton l1) l1 Empty p1)
      (Run p2 (Cat.singleton l2) l2 Empty p2)
      (Rev . Cat.singleton $ Run p3 (Cat.singleton l3) l3 (Cat.singleton $ LayoutMismatch 23 p2 p3) p3)

exampleI323E111 :: Text
exampleI323E111 =
  " \t       one\n\
  \ \t    two\n\
  \ \t       three\n\
  \"

resultI323E111 :: Layout
resultI323E111 =
  let
    pt1 = " \t       "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = " \t    "
    p2 = Prefix pt2
    l2 = rel 13 $ Lex.lex $ pt2 <> "two\n"
    pt3 = " \t       "
    p3 = Prefix pt3
    l3 = rel 23 $ Lex.lex $ pt3 <> "three\n"
  in
    V 37
      (Cat.singleton $ Run p1 (Cat.singleton l1) l1 Empty p1)
      (Run p2 (Cat.singleton l2 <> Cat.singleton l3) (l2 <> l3) Empty p3)
      Empty

exampleI323E112 :: Text
exampleI323E112 =
  " \t       one\n\
  \ \t    two\n\
  \    \t    three\n\
  \"

resultI323E112 :: Layout
resultI323E112 =
  let
    pt1 = " \t       "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = " \t    "
    p2 = Prefix pt2
    l2 = rel 13 $ Lex.lex $ pt2 <> "two\n"
    pt3 = "    \t    "
    p3 = Prefix pt3
    l3 = rel 23 $ Lex.lex $ pt3 <> "three\n"
  in
    V 37
      (Cat.singleton $ Run p1 (Cat.singleton l1) l1 Empty p1)
      (Run p2 (Cat.singleton l2) l2 Empty p2)
      (Rev . Cat.singleton $ Run p3 (Cat.singleton l3) l3 (Cat.singleton $ LayoutMismatch 23 p2 p3) p3)

exampleI323E113 :: Text
exampleI323E113 =
  " \t       one\n\
  \ \t    two\n\
  \       \t three\n\
  \"

resultI323E113 :: Layout
resultI323E113 =
  let
    pt1 = " \t       "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = " \t    "
    p2 = Prefix pt2
    l2 = rel 13 $ Lex.lex $ pt2 <> "two\n"
    pt3 = "       \t "
    p3 = Prefix pt3
    l3 = rel 23 $ Lex.lex $ pt3 <> "three\n"
  in
    V 37
      (Cat.singleton $ Run p1 (Cat.singleton l1) l1 Empty p1)
      (Run p2 (Cat.singleton l2) l2 Empty p2)
      (Rev . Cat.singleton $ Run p3 (Cat.singleton l3) l3 (Cat.singleton $ LayoutMismatch 23 p2 p3) p3)

exampleI323E120 :: Text
exampleI323E120 =
  " \t       one\n\
  \    \t two\n\
  \         three\n\
  \"

resultI323E120 :: Layout
resultI323E120 =
  let
    pt1 = " \t       "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = "    \t "
    p2 = Prefix pt2
    l2 = rel 13 $ Lex.lex $ pt2 <> "two\n"
    pt3 = "         "
    p3 = Prefix pt3
    l3 = rel 23 $ Lex.lex $ pt3 <> "three\n"
  in
    V 37
      Empty
      (Run p1 (Cat.singleton l1) l1 Empty p1)
      ((Rev . Cat.singleton $ Run p2 (Cat.singleton l2) l2 (Cat.singleton $ LayoutMismatch 13 p1 p2) p2) <>
       (Rev . Cat.singleton $ Run p3 (Cat.singleton l3) l3 (Cat.singleton $ LayoutMismatch 23 p2 p3) p3))

exampleI323E121 :: Text
exampleI323E121 =
  " \t       one\n\
  \    \t two\n\
  \ \t       three\n\
  \"

resultI323E121 :: Layout
resultI323E121 =
  let
    pt1 = " \t       "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = "    \t "
    p2 = Prefix pt2
    l2 = rel 13 $ Lex.lex $ pt2 <> "two\n"
    pt3 = " \t       "
    p3 = Prefix pt3
    l3 = rel 23 $ Lex.lex $ pt3 <> "three\n"
  in
    V 37
      Empty
      (Run p1 (Cat.singleton l1) l1 Empty p1)
      ((Rev . Cat.singleton $ Run p2 (Cat.singleton l2) l2 (Cat.singleton $ LayoutMismatch 13 p1 p2) p2) <>
       (Rev . Cat.singleton $ Run p3 (Cat.singleton l3) l3 (Cat.singleton $ LayoutMismatch 23 p2 p3) p3))

exampleI323E122 :: Text
exampleI323E122 =
  " \t       one\n\
  \    \t two\n\
  \    \t    three\n\
  \"

resultI323E122 :: Layout
resultI323E122 =
  let
    pt1 = " \t       "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = "    \t "
    p2 = Prefix pt2
    l2 = rel 13 $ Lex.lex $ pt2 <> "two\n"
    pt3 = "    \t    "
    p3 = Prefix pt3
    l3 = rel 23 $ Lex.lex $ pt3 <> "three\n"
  in
    V 37
      Empty
      (Run p1 (Cat.singleton l1) l1 Empty p1)
      (Rev . Cat.singleton $ Run p2 (Cat.singleton l2 <> Cat.singleton l3) (l2 <> l3) (Cat.singleton $ LayoutMismatch 13 p1 p2) p3)

exampleI323E123 :: Text
exampleI323E123 =
  " \t       one\n\
  \    \t two\n\
  \       \t three\n\
  \"

resultI323E123 :: Layout
resultI323E123 =
  let
    pt1 = " \t       "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = "    \t "
    p2 = Prefix pt2
    l2 = rel 13 $ Lex.lex $ pt2 <> "two\n"
    pt3 = "       \t "
    p3 = Prefix pt3
    l3 = rel 23 $ Lex.lex $ pt3 <> "three\n"
  in
    V 37
      Empty
      (Run p1 (Cat.singleton l1) l1 Empty p1)
      ((Rev . Cat.singleton $ Run p2 (Cat.singleton l2) l2 (Cat.singleton $ LayoutMismatch 13 p1 p2) p2) <>
       (Rev . Cat.singleton $ Run p3 (Cat.singleton l3) l3 (Cat.singleton $ LayoutMismatch 23 p2 p3) p3))

exampleI323E200 :: Text
exampleI323E200 =
  "    \t    one\n\
  \      two\n\
  \         three\n\
  \"

resultI323E200 :: Layout
resultI323E200 =
  let
    pt1 = "    \t    "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = "      "
    p2 = Prefix pt2
    l2 = rel 13 $ Lex.lex $ pt2 <> "two\n"
    pt3 = "         "
    p3 = Prefix pt3
    l3 = rel 23 $ Lex.lex $ pt3 <> "three\n"
  in
    V 37
      Empty
      (Run p1 (Cat.singleton l1) l1 Empty p1)
      (Rev . Cat.singleton $ Run p2 (Cat.singleton l2 <> Cat.singleton l3) (l2 <> l3) (Cat.singleton $ LayoutMismatch 13 p1 p2) p3)

exampleI323E201 :: Text
exampleI323E201 =
  "    \t    one\n\
  \      two\n\
  \ \t       three\n\
  \"

resultI323E201 :: Layout
resultI323E201 =
  let
    pt1 = "    \t    "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = "      "
    p2 = Prefix pt2
    l2 = rel 13 $ Lex.lex $ pt2 <> "two\n"
    pt3 = " \t       "
    p3 = Prefix pt3
    l3 = rel 23 $ Lex.lex $ pt3 <> "three\n"
  in
    V 37
      Empty
      (Run p1 (Cat.singleton l1) l1 Empty p1)
      ((Rev . Cat.singleton $ Run p2 (Cat.singleton l2) l2 (Cat.singleton $ LayoutMismatch 13 p1 p2) p2) <>
       (Rev . Cat.singleton $ Run p3 (Cat.singleton l3) l3 (Cat.singleton $ LayoutMismatch 23 p2 p3) p3))

exampleI323E202 :: Text
exampleI323E202 =
  "    \t    one\n\
  \      two\n\
  \    \t    three\n\
  \"

resultI323E202 :: Layout
resultI323E202 =
  let
    pt1 = "    \t    "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = "      "
    p2 = Prefix pt2
    l2 = rel 13 $ Lex.lex $ pt2 <> "two\n"
    pt3 = "    \t    "
    p3 = Prefix pt3
    l3 = rel 23 $ Lex.lex $ pt3 <> "three\n"
  in
    V 37
      Empty
      (Run p1 (Cat.singleton l1) l1 Empty p1)
      ((Rev . Cat.singleton $ Run p2 (Cat.singleton l2) l2 (Cat.singleton $ LayoutMismatch 13 p1 p2) p2) <>
       (Rev . Cat.singleton $ Run p3 (Cat.singleton l3) l3 (Cat.singleton $ LayoutMismatch 23 p2 p3) p3))

exampleI323E203 :: Text
exampleI323E203 =
  "    \t    one\n\
  \      two\n\
  \       \t three\n\
  \"

resultI323E203 :: Layout
resultI323E203 =
  let
    pt1 = "    \t    "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = "      "
    p2 = Prefix pt2
    l2 = rel 13 $ Lex.lex $ pt2 <> "two\n"
    pt3 = "       \t "
    p3 = Prefix pt3
    l3 = rel 23 $ Lex.lex $ pt3 <> "three\n"
  in
    V 37
      Empty
      (Run p1 (Cat.singleton l1) l1 Empty p1)
      (Rev . Cat.singleton $ Run p2 (Cat.singleton l2 <> Cat.singleton l3) (l2 <> l3) (Cat.singleton $ LayoutMismatch 13 p1 p2) p3)

exampleI323E210 :: Text
exampleI323E210 =
  "    \t    one\n\
  \ \t    two\n\
  \         three\n\
  \"

resultI323E210 :: Layout
resultI323E210 =
  let
    pt1 = "    \t    "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = " \t    "
    p2 = Prefix pt2
    l2 = rel 13 $ Lex.lex $ pt2 <> "two\n"
    pt3 = "         "
    p3 = Prefix pt3
    l3 = rel 23 $ Lex.lex $ pt3 <> "three\n"
  in
    V 37
      Empty
      (Run p1 (Cat.singleton l1) l1 Empty p1)
      ((Rev . Cat.singleton $ Run p2 (Cat.singleton l2) l2 (Cat.singleton $ LayoutMismatch 13 p1 p2) p2) <>
       (Rev . Cat.singleton $ Run p3 (Cat.singleton l3) l3 (Cat.singleton $ LayoutMismatch 23 p2 p3) p3))

exampleI323E211 :: Text
exampleI323E211 =
  "    \t    one\n\
  \ \t    two\n\
  \ \t       three\n\
  \"

resultI323E211 :: Layout
resultI323E211 =
  let
    pt1 = "    \t    "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = " \t    "
    p2 = Prefix pt2
    l2 = rel 13 $ Lex.lex $ pt2 <> "two\n"
    pt3 = " \t       "
    p3 = Prefix pt3
    l3 = rel 23 $ Lex.lex $ pt3 <> "three\n"
  in
    V 37
      Empty
      (Run p1 (Cat.singleton l1) l1 Empty p1)
      (Rev . Cat.singleton $ Run p2 (Cat.singleton l2 <> Cat.singleton l3) (l2 <> l3) (Cat.singleton $ LayoutMismatch 13 p1 p2) p3)

exampleI323E212 :: Text
exampleI323E212 =
  "    \t    one\n\
  \ \t    two\n\
  \    \t    three\n\
  \"

resultI323E212 :: Layout
resultI323E212 =
  let
    pt1 = "    \t    "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = " \t    "
    p2 = Prefix pt2
    l2 = rel 13 $ Lex.lex $ pt2 <> "two\n"
    pt3 = "    \t    "
    p3 = Prefix pt3
    l3 = rel 23 $ Lex.lex $ pt3 <> "three\n"
  in
    V 37
      Empty
      (Run p1 (Cat.singleton l1) l1 Empty p1)
      ((Rev . Cat.singleton $ Run p2 (Cat.singleton l2) l2 (Cat.singleton $ LayoutMismatch 13 p1 p2) p2) <>
       (Rev . Cat.singleton $ Run p3 (Cat.singleton l3) l3 (Cat.singleton $ LayoutMismatch 23 p2 p3) p3))

exampleI323E213 :: Text
exampleI323E213 =
  "    \t    one\n\
  \ \t    two\n\
  \       \t three\n\
  \"

resultI323E213 :: Layout
resultI323E213 =
  let
    pt1 = "    \t    "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = " \t    "
    p2 = Prefix pt2
    l2 = rel 13 $ Lex.lex $ pt2 <> "two\n"
    pt3 = "       \t "
    p3 = Prefix pt3
    l3 = rel 23 $ Lex.lex $ pt3 <> "three\n"
  in
    V 37
      Empty
      (Run p1 (Cat.singleton l1) l1 Empty p1)
      ((Rev . Cat.singleton $ Run p2 (Cat.singleton l2) l2 (Cat.singleton $ LayoutMismatch 13 p1 p2) p2) <>
       (Rev . Cat.singleton $ Run p3 (Cat.singleton l3) l3 (Cat.singleton $ LayoutMismatch 23 p2 p3) p3))

exampleI323E220 :: Text
exampleI323E220 =
  "    \t    one\n\
  \    \t two\n\
  \         three\n\
  \"

resultI323E220 :: Layout
resultI323E220 =
  let
    pt1 = "    \t    "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = "    \t "
    p2 = Prefix pt2
    l2 = rel 13 $ Lex.lex $ pt2 <> "two\n"
    pt3 = "         "
    p3 = Prefix pt3
    l3 = rel 23 $ Lex.lex $ pt3 <> "three\n"
  in
    V 37
      (Cat.singleton $ Run p1 (Cat.singleton l1) l1 Empty p1)
      (Run p2 (Cat.singleton l2) l2 Empty p2)
      (Rev . Cat.singleton $ Run p3 (Cat.singleton l3) l3 (Cat.singleton $ LayoutMismatch 23 p2 p3) p3)

exampleI323E221 :: Text
exampleI323E221 =
  "    \t    one\n\
  \    \t two\n\
  \ \t       three\n\
  \"

resultI323E221 :: Layout
resultI323E221 =
  let
    pt1 = "    \t    "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = "    \t "
    p2 = Prefix pt2
    l2 = rel 13 $ Lex.lex $ pt2 <> "two\n"
    pt3 = " \t       "
    p3 = Prefix pt3
    l3 = rel 23 $ Lex.lex $ pt3 <> "three\n"
  in
    V 37
      (Cat.singleton $ Run p1 (Cat.singleton l1) l1 Empty p1)
      (Run p2 (Cat.singleton l2) l2 Empty p2)
      (Rev . Cat.singleton $ Run p3 (Cat.singleton l3) l3 (Cat.singleton $ LayoutMismatch 23 p2 p3) p3)

exampleI323E222 :: Text
exampleI323E222 =
  "    \t    one\n\
  \    \t two\n\
  \    \t    three\n\
  \"

resultI323E222 :: Layout
resultI323E222 =
  let
    pt1 = "    \t    "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = "    \t "
    p2 = Prefix pt2
    l2 = rel 13 $ Lex.lex $ pt2 <> "two\n"
    pt3 = "    \t    "
    p3 = Prefix pt3
    l3 = rel 23 $ Lex.lex $ pt3 <> "three\n"
  in
    V 37
      (Cat.singleton $ Run p1 (Cat.singleton l1) l1 Empty p1)
      (Run p2 (Cat.singleton l2 <> Cat.singleton l3) (l2 <> l3) Empty p3)
      Empty

exampleI323E223 :: Text
exampleI323E223 =
  "    \t    one\n\
  \    \t two\n\
  \       \t three\n\
  \"

resultI323E223 :: Layout
resultI323E223 =
  let
    pt1 = "    \t    "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = "    \t "
    p2 = Prefix pt2
    l2 = rel 13 $ Lex.lex $ pt2 <> "two\n"
    pt3 = "       \t "
    p3 = Prefix pt3
    l3 = rel 23 $ Lex.lex $ pt3 <> "three\n"
  in
    V 37
      (Cat.singleton $ Run p1 (Cat.singleton l1) l1 Empty p1)
      (Run p2 (Cat.singleton l2) l2 Empty p2)
      (Rev . Cat.singleton $ Run p3 (Cat.singleton l3) l3 (Cat.singleton $ LayoutMismatch 23 p2 p3) p3)

exampleI323E300 :: Text
exampleI323E300 =
  "       \t one\n\
  \      two\n\
  \         three\n\
  \"

resultI323E300 :: Layout
resultI323E300 =
  let
    pt1 = "       \t "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = "      "
    p2 = Prefix pt2
    l2 = rel 13 $ Lex.lex $ pt2 <> "two\n"
    pt3 = "         "
    p3 = Prefix pt3
    l3 = rel 23 $ Lex.lex $ pt3 <> "three\n"
  in
    V 37
      (Cat.singleton $ Run p1 (Cat.singleton l1) l1 Empty p1)
      (Run p2 (Cat.singleton l2 <> Cat.singleton l3) (l2 <> l3) Empty p3)
       Empty

exampleI323E301 :: Text
exampleI323E301 =
  "       \t one\n\
  \      two\n\
  \ \t       three\n\
  \"

resultI323E301 :: Layout
resultI323E301 =
  let
    pt1 = "       \t "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = "      "
    p2 = Prefix pt2
    l2 = rel 13 $ Lex.lex $ pt2 <> "two\n"
    pt3 = " \t       "
    p3 = Prefix pt3
    l3 = rel 23 $ Lex.lex $ pt3 <> "three\n"
  in
    V 37
      (Cat.singleton $ Run p1 (Cat.singleton l1) l1 Empty p1)
      (Run p2 (Cat.singleton l2) l2 Empty p2)
      (Rev . Cat.singleton $ Run p3 (Cat.singleton l3) l3 (Cat.singleton $ LayoutMismatch 23 p2 p3) p3)

exampleI323E302 :: Text
exampleI323E302 =
  "       \t one\n\
  \      two\n\
  \    \t    three\n\
  \"

resultI323E302 :: Layout
resultI323E302 =
  let
    pt1 = "       \t "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = "      "
    p2 = Prefix pt2
    l2 = rel 13 $ Lex.lex $ pt2 <> "two\n"
    pt3 = "    \t    "
    p3 = Prefix pt3
    l3 = rel 23 $ Lex.lex $ pt3 <> "three\n"
  in
    V 37
      (Cat.singleton $ Run p1 (Cat.singleton l1) l1 Empty p1)
      (Run p2 (Cat.singleton l2) l2 Empty p2)
      (Rev . Cat.singleton $ Run p3 (Cat.singleton l3) l3 (Cat.singleton $ LayoutMismatch 23 p2 p3) p3)

exampleI323E303 :: Text
exampleI323E303 =
  "       \t one\n\
  \      two\n\
  \       \t three\n\
  \"

resultI323E303 :: Layout
resultI323E303 =
  let
    pt1 = "       \t "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = "      "
    p2 = Prefix pt2
    l2 = rel 13 $ Lex.lex $ pt2 <> "two\n"
    pt3 = "       \t "
    p3 = Prefix pt3
    l3 = rel 23 $ Lex.lex $ pt3 <> "three\n"
  in
    V 37
      (Cat.singleton $ Run p1 (Cat.singleton l1) l1 Empty p1)
      (Run p2 (Cat.singleton l2 <> Cat.singleton l3) (l2 <> l3) Empty p3)
       Empty

exampleI323E310 :: Text
exampleI323E310 =
  "       \t one\n\
  \ \t    two\n\
  \         three\n\
  \"

resultI323E310 :: Layout
resultI323E310 =
  let
    pt1 = "       \t "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = " \t    "
    p2 = Prefix pt2
    l2 = rel 13 $ Lex.lex $ pt2 <> "two\n"
    pt3 = "         "
    p3 = Prefix pt3
    l3 = rel 23 $ Lex.lex $ pt3 <> "three\n"
  in
    V 37
       Empty
      (Run p1 (Cat.singleton l1) l1 Empty p1)
      ((Rev . Cat.singleton $ Run p2 (Cat.singleton l2) l2 (Cat.singleton $ LayoutMismatch 13 p1 p2) p2) <>
       (Rev . Cat.singleton $ Run p3 (Cat.singleton l3) l3 (Cat.singleton $ LayoutMismatch 23 p2 p3) p3))

exampleI323E311 :: Text
exampleI323E311 =
  "       \t one\n\
  \ \t    two\n\
  \ \t       three\n\
  \"

resultI323E311 :: Layout
resultI323E311 =
  let
    pt1 = "       \t "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = " \t    "
    p2 = Prefix pt2
    l2 = rel 13 $ Lex.lex $ pt2 <> "two\n"
    pt3 = " \t       "
    p3 = Prefix pt3
    l3 = rel 23 $ Lex.lex $ pt3 <> "three\n"
  in
    V 37
       Empty
      (Run p1 (Cat.singleton l1) l1 Empty p1)
      (Rev . Cat.singleton $ Run p2 (Cat.singleton l2 <> Cat.singleton l3) (l2 <> l3) (Cat.singleton $ LayoutMismatch 13 p1 p2) p3)

exampleI323E312 :: Text
exampleI323E312 =
  "       \t one\n\
  \ \t    two\n\
  \    \t    three\n\
  \"

resultI323E312 :: Layout
resultI323E312 =
  let
    pt1 = "       \t "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = " \t    "
    p2 = Prefix pt2
    l2 = rel 13 $ Lex.lex $ pt2 <> "two\n"
    pt3 = "    \t    "
    p3 = Prefix pt3
    l3 = rel 23 $ Lex.lex $ pt3 <> "three\n"
  in
    V 37
       Empty
      (Run p1 (Cat.singleton l1) l1 Empty p1)
      ((Rev . Cat.singleton $ Run p2 (Cat.singleton l2) l2 (Cat.singleton $ LayoutMismatch 13 p1 p2) p2) <>
       (Rev . Cat.singleton $ Run p3 (Cat.singleton l3) l3 (Cat.singleton $ LayoutMismatch 23 p2 p3) p3))

exampleI323E313 :: Text
exampleI323E313 =
  "       \t one\n\
  \ \t    two\n\
  \       \t three\n\
  \"

resultI323E313 :: Layout
resultI323E313 =
  let
    pt1 = "       \t "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = " \t    "
    p2 = Prefix pt2
    l2 = rel 13 $ Lex.lex $ pt2 <> "two\n"
    pt3 = "       \t "
    p3 = Prefix pt3
    l3 = rel 23 $ Lex.lex $ pt3 <> "three\n"
  in
    V 37
       Empty
      (Run p1 (Cat.singleton l1) l1 Empty p1)
      ((Rev . Cat.singleton $ Run p2 (Cat.singleton l2) l2 (Cat.singleton $ LayoutMismatch 13 p1 p2) p2) <>
       (Rev . Cat.singleton $ Run p3 (Cat.singleton l3) l3 (Cat.singleton $ LayoutMismatch 23 p2 p3) p3))

exampleI323E320 :: Text
exampleI323E320 =
  "       \t one\n\
  \    \t two\n\
  \         three\n\
  \"

resultI323E320 :: Layout
resultI323E320 =
  let
    pt1 = "       \t "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = "    \t "
    p2 = Prefix pt2
    l2 = rel 13 $ Lex.lex $ pt2 <> "two\n"
    pt3 = "         "
    p3 = Prefix pt3
    l3 = rel 23 $ Lex.lex $ pt3 <> "three\n"
  in
    V 37
       Empty
      (Run p1 (Cat.singleton l1) l1 Empty p1)
      ((Rev . Cat.singleton $ Run p2 (Cat.singleton l2) l2 (Cat.singleton $ LayoutMismatch 13 p1 p2) p2) <>
       (Rev . Cat.singleton $ Run p3 (Cat.singleton l3) l3 (Cat.singleton $ LayoutMismatch 23 p2 p3) p3))

exampleI323E321 :: Text
exampleI323E321 =
  "       \t one\n\
  \    \t two\n\
  \ \t       three\n\
  \"

resultI323E321 :: Layout
resultI323E321 =
  let
    pt1 = "       \t "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = "    \t "
    p2 = Prefix pt2
    l2 = rel 13 $ Lex.lex $ pt2 <> "two\n"
    pt3 = " \t       "
    p3 = Prefix pt3
    l3 = rel 23 $ Lex.lex $ pt3 <> "three\n"
  in
    V 37
       Empty
      (Run p1 (Cat.singleton l1) l1 Empty p1)
      ((Rev . Cat.singleton $ Run p2 (Cat.singleton l2) l2 (Cat.singleton $ LayoutMismatch 13 p1 p2) p2) <>
       (Rev . Cat.singleton $ Run p3 (Cat.singleton l3) l3 (Cat.singleton $ LayoutMismatch 23 p2 p3) p3))

exampleI323E322 :: Text
exampleI323E322 =
  "       \t one\n\
  \    \t two\n\
  \    \t    three\n\
  \"

resultI323E322 :: Layout
resultI323E322 =
  let
    pt1 = "       \t "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = "    \t "
    p2 = Prefix pt2
    l2 = rel 13 $ Lex.lex $ pt2 <> "two\n"
    pt3 = "    \t    "
    p3 = Prefix pt3
    l3 = rel 23 $ Lex.lex $ pt3 <> "three\n"
  in
    V 37
       Empty
      (Run p1 (Cat.singleton l1) l1 Empty p1)
      (Rev . Cat.singleton $ Run p2 (Cat.singleton l2 <> Cat.singleton l3) (l2 <> l3) (Cat.singleton $ LayoutMismatch 13 p1 p2) p3)

exampleI323E323 :: Text
exampleI323E323 =
  "       \t one\n\
  \    \t two\n\
  \       \t three\n\
  \"

resultI323E323 :: Layout
resultI323E323 =
  let
    pt1 = "       \t "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = "    \t "
    p2 = Prefix pt2
    l2 = rel 13 $ Lex.lex $ pt2 <> "two\n"
    pt3 = "       \t "
    p3 = Prefix pt3
    l3 = rel 23 $ Lex.lex $ pt3 <> "three\n"
  in
    V 37
       Empty
      (Run p1 (Cat.singleton l1) l1 Empty p1)
      ((Rev . Cat.singleton $ Run p2 (Cat.singleton l2) l2 (Cat.singleton $ LayoutMismatch 13 p1 p2) p2) <>
       (Rev . Cat.singleton $ Run p3 (Cat.singleton l3) l3 (Cat.singleton $ LayoutMismatch 23 p2 p3) p3))

exampleI331E000 :: Text
exampleI331E000 =
  "         one\n\
  \         two\n\
  \   three\n\
  \"

resultI331E000 :: Layout
resultI331E000 =
  let
    pt1 = "         "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = "         "
    p2 = Prefix pt2
    l2 = rel 13 $ Lex.lex $ pt2 <> "two\n"
    pt3 = "   "
    p3 = Prefix pt3
    l3 = rel 26 $ Lex.lex $ pt3 <> "three\n"
  in
    V 34
      ((Cat.singleton $ Run p1 (Cat.singleton l1) l1 Empty p1) <>
       (Cat.singleton $ Run p2 (Cat.singleton l2) l2 Empty p2))
      (Run p3 (Cat.singleton l3) l3 Empty p3)
       Empty

exampleI331E001 :: Text
exampleI331E001 =
  "         one\n\
  \         two\n\
  \ \t three\n\
  \"

resultI331E001 :: Layout
resultI331E001 =
  let
    pt1 = "         "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = "         "
    p2 = Prefix pt2
    l2 = rel 13 $ Lex.lex $ pt2 <> "two\n"
    pt3 = " \t "
    p3 = Prefix pt3
    l3 = rel 26 $ Lex.lex $ pt3 <> "three\n"
  in
    V 34
       Empty
      (Run p1 (Cat.singleton l1) l1 Empty p1)
      ((Rev . Cat.singleton $ Run p2 (Cat.singleton l2) l2 Empty p2) <>
       (Rev . Cat.singleton $ Run p3 (Cat.singleton l3) l3 (Cat.singleton $ LayoutMismatch 26 p2 p3) p3))

exampleI331E010 :: Text
exampleI331E010 =
  "         one\n\
  \ \t       two\n\
  \   three\n\
  \"

resultI331E010 :: Layout
resultI331E010 =
  let
    pt1 = "         "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = " \t       "
    p2 = Prefix pt2
    l2 = rel 13 $ Lex.lex $ pt2 <> "two\n"
    pt3 = "   "
    p3 = Prefix pt3
    l3 = rel 26 $ Lex.lex $ pt3 <> "three\n"
  in
    V 34
       Empty
      (Run p1 (Cat.singleton l1) l1 Empty p1)
      ((Rev . Cat.singleton $ Run p2 (Cat.singleton l2) l2 (Cat.singleton $ LayoutMismatch 13 p1 p2) p2) <>
       (Rev . Cat.singleton $ Run p3 (Cat.singleton l3) l3 (Cat.singleton $ LayoutMismatch 26 p2 p3) p3))

exampleI331E011 :: Text
exampleI331E011 =
  "         one\n\
  \ \t       two\n\
  \ \t three\n\
  \"

resultI331E011 :: Layout
resultI331E011 =
  let
    pt1 = "         "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = " \t       "
    p2 = Prefix pt2
    l2 = rel 13 $ Lex.lex $ pt2 <> "two\n"
    pt3 = " \t "
    p3 = Prefix pt3
    l3 = rel 26 $ Lex.lex $ pt3 <> "three\n"
  in
    V 34
       Empty
      (Run p1 (Cat.singleton l1) l1 Empty p1)
      ((Rev . Cat.singleton $ Run p2 (Cat.singleton l2) l2 (Cat.singleton $ LayoutMismatch 13 p1 p2) p2) <>
       (Rev . Cat.singleton $ Run p3 (Cat.singleton l3) l3 Empty p3))

exampleI331E020 :: Text
exampleI331E020 =
  "         one\n\
  \    \t    two\n\
  \   three\n\
  \"

resultI331E020 :: Layout
resultI331E020 =
  let
    pt1 = "         "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = "    \t    "
    p2 = Prefix pt2
    l2 = rel 13 $ Lex.lex $ pt2 <> "two\n"
    pt3 = "   "
    p3 = Prefix pt3
    l3 = rel 26 $ Lex.lex $ pt3 <> "three\n"
  in
    V 34
      ((Cat.singleton $ Run p1 (Cat.singleton l1) l1 Empty p1) <>
       (Cat.singleton $ Run p2 (Cat.singleton l2) l2 (Cat.singleton $ LayoutMismatch 13 p1 p2) p2))
      (Run p3 (Cat.singleton l3) l3 Empty p3)
       Empty

exampleI331E021 :: Text
exampleI331E021 =
  "         one\n\
  \    \t    two\n\
  \ \t three\n\
  \"

resultI331E021 :: Layout
resultI331E021 =
  let
    pt1 = "         "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = "    \t    "
    p2 = Prefix pt2
    l2 = rel 13 $ Lex.lex $ pt2 <> "two\n"
    pt3 = " \t "
    p3 = Prefix pt3
    l3 = rel 26 $ Lex.lex $ pt3 <> "three\n"
  in
    V 34
       Empty
      (Run p1 (Cat.singleton l1) l1 Empty p1)
      ((Rev . Cat.singleton $ Run p2 (Cat.singleton l2) l2 (Cat.singleton $ LayoutMismatch 13 p1 p2) p2) <>
       (Rev . Cat.singleton $ Run p3 (Cat.singleton l3) l3 (Cat.singleton $ LayoutMismatch 26 p2 p3) p3))

exampleI331E030 :: Text
exampleI331E030 =
  "         one\n\
  \       \t two\n\
  \   three\n\
  \"

resultI331E030 :: Layout
resultI331E030 =
  let
    pt1 = "         "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = "       \t "
    p2 = Prefix pt2
    l2 = rel 13 $ Lex.lex $ pt2 <> "two\n"
    pt3 = "   "
    p3 = Prefix pt3
    l3 = rel 26 $ Lex.lex $ pt3 <> "three\n"
  in
    V 34
      ((Cat.singleton $ Run p1 (Cat.singleton l1) l1 Empty p1) <>
       (Cat.singleton $ Run p2 (Cat.singleton l2) l2 (Cat.singleton $ LayoutMismatch 13 p1 p2) p2))
      (Run p3 (Cat.singleton l3) l3 Empty p3)
       Empty

exampleI331E031 :: Text
exampleI331E031 =
  "         one\n\
  \       \t two\n\
  \ \t three\n\
  \"

resultI331E031 :: Layout
resultI331E031 =
  let
    pt1 = "         "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = "       \t "
    p2 = Prefix pt2
    l2 = rel 13 $ Lex.lex $ pt2 <> "two\n"
    pt3 = " \t "
    p3 = Prefix pt3
    l3 = rel 26 $ Lex.lex $ pt3 <> "three\n"
  in
    V 34
       Empty
      (Run p1 (Cat.singleton l1) l1 Empty p1)
      ((Rev . Cat.singleton $ Run p2 (Cat.singleton l2) l2 (Cat.singleton $ LayoutMismatch 13 p1 p2) p2) <>
       (Rev . Cat.singleton $ Run p3 (Cat.singleton l3) l3 (Cat.singleton $ LayoutMismatch 26 p2 p3) p3))

exampleI331E100 :: Text
exampleI331E100 =
  " \t       one\n\
  \         two\n\
  \   three\n\
  \"

resultI331E100 :: Layout
resultI331E100 =
  let
    pt1 = " \t       "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = "         "
    p2 = Prefix pt2
    l2 = rel 13 $ Lex.lex $ pt2 <> "two\n"
    pt3 = "   "
    p3 = Prefix pt3
    l3 = rel 26 $ Lex.lex $ pt3 <> "three\n"
  in
    V 34
       Empty
      (Run p1 (Cat.singleton l1) l1 Empty p1)
      ((Rev . Cat.singleton $ Run p2 (Cat.singleton l2) l2 (Cat.singleton $ LayoutMismatch 13 p1 p2) p2) <>
       (Rev . Cat.singleton $ Run p3 (Cat.singleton l3) l3 Empty p3))

exampleI331E101 :: Text
exampleI331E101 =
  " \t       one\n\
  \         two\n\
  \ \t three\n\
  \"

resultI331E101 :: Layout
resultI331E101 =
  let
    pt1 = " \t       "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = "         "
    p2 = Prefix pt2
    l2 = rel 13 $ Lex.lex $ pt2 <> "two\n"
    pt3 = " \t "
    p3 = Prefix pt3
    l3 = rel 26 $ Lex.lex $ pt3 <> "three\n"
  in
    V 34
       Empty
      (Run p1 (Cat.singleton l1) l1 Empty p1)
      ((Rev . Cat.singleton $ Run p2 (Cat.singleton l2) l2 (Cat.singleton $ LayoutMismatch 13 p1 p2) p2) <>
       (Rev . Cat.singleton $ Run p3 (Cat.singleton l3) l3 (Cat.singleton $ LayoutMismatch 26 p2 p3) p3))

exampleI331E110 :: Text
exampleI331E110 =
  " \t       one\n\
  \ \t       two\n\
  \   three\n\
  \"

resultI331E110 :: Layout
resultI331E110 =
  let
    pt1 = " \t       "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = " \t       "
    p2 = Prefix pt2
    l2 = rel 13 $ Lex.lex $ pt2 <> "two\n"
    pt3 = "   "
    p3 = Prefix pt3
    l3 = rel 26 $ Lex.lex $ pt3 <> "three\n"
  in
    V 34
       Empty
      (Run p1 (Cat.singleton l1) l1 Empty p1)
      ((Rev . Cat.singleton $ Run p2 (Cat.singleton l2) l2 Empty p2) <>
       (Rev . Cat.singleton $ Run p3 (Cat.singleton l3) l3 (Cat.singleton $ LayoutMismatch 26 p2 p3) p3))

exampleI331E111 :: Text
exampleI331E111 =
  " \t       one\n\
  \ \t       two\n\
  \ \t three\n\
  \"

resultI331E111 :: Layout
resultI331E111 =
  let
    pt1 = " \t       "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = " \t       "
    p2 = Prefix pt2
    l2 = rel 13 $ Lex.lex $ pt2 <> "two\n"
    pt3 = " \t "
    p3 = Prefix pt3
    l3 = rel 26 $ Lex.lex $ pt3 <> "three\n"
  in
    V 34
      ((Cat.singleton $ Run p1 (Cat.singleton l1) l1 Empty p1) <>
       (Cat.singleton $ Run p2 (Cat.singleton l2) l2 Empty p2))
      (Run p3 (Cat.singleton l3) l3 Empty p3)
       Empty

exampleI331E120 :: Text
exampleI331E120 =
  " \t       one\n\
  \    \t    two\n\
  \   three\n\
  \"

resultI331E120 :: Layout
resultI331E120 =
  let
    pt1 = " \t       "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = "    \t    "
    p2 = Prefix pt2
    l2 = rel 13 $ Lex.lex $ pt2 <> "two\n"
    pt3 = "   "
    p3 = Prefix pt3
    l3 = rel 26 $ Lex.lex $ pt3 <> "three\n"
  in
    V 34
       Empty
      (Run p1 (Cat.singleton l1) l1 Empty p1)
      ((Rev . Cat.singleton $ Run p2 (Cat.singleton l2) l2 (Cat.singleton $ LayoutMismatch 13 p1 p2) p2) <>
       (Rev . Cat.singleton $ Run p3 (Cat.singleton l3) l3 Empty p3))

exampleI331E121 :: Text
exampleI331E121 =
  " \t       one\n\
  \    \t    two\n\
  \ \t three\n\
  \"

resultI331E121 :: Layout
resultI331E121 =
  let
    pt1 = " \t       "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = "    \t    "
    p2 = Prefix pt2
    l2 = rel 13 $ Lex.lex $ pt2 <> "two\n"
    pt3 = " \t "
    p3 = Prefix pt3
    l3 = rel 26 $ Lex.lex $ pt3 <> "three\n"
  in
    V 34
       Empty
      (Run p1 (Cat.singleton l1) l1 Empty p1)
      ((Rev . Cat.singleton $ Run p2 (Cat.singleton l2) l2 (Cat.singleton $ LayoutMismatch 13 p1 p2) p2) <>
       (Rev . Cat.singleton $ Run p3 (Cat.singleton l3) l3 (Cat.singleton $ LayoutMismatch 26 p2 p3) p3))

exampleI331E130 :: Text
exampleI331E130 =
  " \t       one\n\
  \       \t two\n\
  \   three\n\
  \"

resultI331E130 :: Layout
resultI331E130 =
  let
    pt1 = " \t       "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = "       \t "
    p2 = Prefix pt2
    l2 = rel 13 $ Lex.lex $ pt2 <> "two\n"
    pt3 = "   "
    p3 = Prefix pt3
    l3 = rel 26 $ Lex.lex $ pt3 <> "three\n"
  in
    V 34
       Empty
      (Run p1 (Cat.singleton l1) l1 Empty p1)
      ((Rev . Cat.singleton $ Run p2 (Cat.singleton l2) l2 (Cat.singleton $ LayoutMismatch 13 p1 p2) p2) <>
       (Rev . Cat.singleton $ Run p3 (Cat.singleton l3) l3 Empty p3))

exampleI331E131 :: Text
exampleI331E131 =
  " \t       one\n\
  \       \t two\n\
  \ \t three\n\
  \"

resultI331E131 :: Layout
resultI331E131 =
  let
    pt1 = " \t       "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = "       \t "
    p2 = Prefix pt2
    l2 = rel 13 $ Lex.lex $ pt2 <> "two\n"
    pt3 = " \t "
    p3 = Prefix pt3
    l3 = rel 26 $ Lex.lex $ pt3 <> "three\n"
  in
    V 34
       Empty
      (Run p1 (Cat.singleton l1) l1 Empty p1)
      ((Rev . Cat.singleton $ Run p2 (Cat.singleton l2) l2 (Cat.singleton $ LayoutMismatch 13 p1 p2) p2) <>
       (Rev . Cat.singleton $ Run p3 (Cat.singleton l3) l3 (Cat.singleton $ LayoutMismatch 26 p2 p3) p3))

exampleI331E200 :: Text
exampleI331E200 =
  "    \t    one\n\
  \         two\n\
  \   three\n\
  \"

resultI331E200 :: Layout
resultI331E200 =
  let
    pt1 = "    \t    "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = "         "
    p2 = Prefix pt2
    l2 = rel 13 $ Lex.lex $ pt2 <> "two\n"
    pt3 = "   "
    p3 = Prefix pt3
    l3 = rel 26 $ Lex.lex $ pt3 <> "three\n"
  in
    V 34
      ((Cat.singleton $ Run p1 (Cat.singleton l1) l1 Empty p1) <>
       (Cat.singleton $ Run p2 (Cat.singleton l2) l2 (Cat.singleton $ LayoutMismatch 13 p1 p2) p2))
      (Run p3 (Cat.singleton l3) l3 Empty p3)
       Empty

exampleI331E201 :: Text
exampleI331E201 =
  "    \t    one\n\
  \         two\n\
  \ \t three\n\
  \"

resultI331E201 :: Layout
resultI331E201 =
  let
    pt1 = "    \t    "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = "         "
    p2 = Prefix pt2
    l2 = rel 13 $ Lex.lex $ pt2 <> "two\n"
    pt3 = " \t "
    p3 = Prefix pt3
    l3 = rel 26 $ Lex.lex $ pt3 <> "three\n"
  in
    V 34
       Empty
      (Run p1 (Cat.singleton l1) l1 Empty p1)
      ((Rev . Cat.singleton $ Run p2 (Cat.singleton l2) l2 (Cat.singleton $ LayoutMismatch 13 p1 p2) p2) <>
       (Rev . Cat.singleton $ Run p3 (Cat.singleton l3) l3 (Cat.singleton $ LayoutMismatch 26 p2 p3) p3))

exampleI331E210 :: Text
exampleI331E210 =
  "    \t    one\n\
  \ \t       two\n\
  \   three\n\
  \"

resultI331E210 :: Layout
resultI331E210 =
  let
    pt1 = "    \t    "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = " \t       "
    p2 = Prefix pt2
    l2 = rel 13 $ Lex.lex $ pt2 <> "two\n"
    pt3 = "   "
    p3 = Prefix pt3
    l3 = rel 26 $ Lex.lex $ pt3 <> "three\n"
  in
    V 34
       Empty
      (Run p1 (Cat.singleton l1) l1 Empty p1)
      ((Rev . Cat.singleton $ Run p2 (Cat.singleton l2) l2 (Cat.singleton $ LayoutMismatch 13 p1 p2) p2) <>
       (Rev . Cat.singleton $ Run p3 (Cat.singleton l3) l3 (Cat.singleton $ LayoutMismatch 26 p2 p3) p3))

exampleI331E211 :: Text
exampleI331E211 =
  "    \t    one\n\
  \ \t       two\n\
  \ \t three\n\
  \"

resultI331E211 :: Layout
resultI331E211 =
  let
    pt1 = "    \t    "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = " \t       "
    p2 = Prefix pt2
    l2 = rel 13 $ Lex.lex $ pt2 <> "two\n"
    pt3 = " \t "
    p3 = Prefix pt3
    l3 = rel 26 $ Lex.lex $ pt3 <> "three\n"
  in
    V 34
       Empty
      (Run p1 (Cat.singleton l1) l1 Empty p1)
      ((Rev . Cat.singleton $ Run p2 (Cat.singleton l2) l2 (Cat.singleton $ LayoutMismatch 13 p1 p2) p2) <>
       (Rev . Cat.singleton $ Run p3 (Cat.singleton l3) l3 Empty p3))

exampleI331E220 :: Text
exampleI331E220 =
  "    \t    one\n\
  \    \t    two\n\
  \   three\n\
  \"

resultI331E220 :: Layout
resultI331E220 =
  let
    pt1 = "    \t    "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = "    \t    "
    p2 = Prefix pt2
    l2 = rel 13 $ Lex.lex $ pt2 <> "two\n"
    pt3 = "   "
    p3 = Prefix pt3
    l3 = rel 26 $ Lex.lex $ pt3 <> "three\n"
  in
    V 34
      ((Cat.singleton $ Run p1 (Cat.singleton l1) l1 Empty p1) <>
       (Cat.singleton $ Run p2 (Cat.singleton l2) l2 Empty p2))
      (Run p3 (Cat.singleton l3) l3 Empty p3)
       Empty

exampleI331E221 :: Text
exampleI331E221 =
  "    \t    one\n\
  \    \t    two\n\
  \ \t three\n\
  \"

resultI331E221 :: Layout
resultI331E221 =
  let
    pt1 = "    \t    "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = "    \t    "
    p2 = Prefix pt2
    l2 = rel 13 $ Lex.lex $ pt2 <> "two\n"
    pt3 = " \t "
    p3 = Prefix pt3
    l3 = rel 26 $ Lex.lex $ pt3 <> "three\n"
  in
    V 34
       Empty
      (Run p1 (Cat.singleton l1) l1 Empty p1)
      ((Rev . Cat.singleton $ Run p2 (Cat.singleton l2) l2 Empty p2) <>
       (Rev . Cat.singleton $ Run p3 (Cat.singleton l3) l3 (Cat.singleton $ LayoutMismatch 26 p2 p3) p3))

exampleI331E230 :: Text
exampleI331E230 =
  "    \t    one\n\
  \       \t two\n\
  \   three\n\
  \"

resultI331E230 :: Layout
resultI331E230 =
  let
    pt1 = "    \t    "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = "       \t "
    p2 = Prefix pt2
    l2 = rel 13 $ Lex.lex $ pt2 <> "two\n"
    pt3 = "   "
    p3 = Prefix pt3
    l3 = rel 26 $ Lex.lex $ pt3 <> "three\n"
  in
    V 34
      ((Cat.singleton $ Run p1 (Cat.singleton l1) l1 Empty p1) <>
       (Cat.singleton $ Run p2 (Cat.singleton l2) l2 (Cat.singleton $ LayoutMismatch 13 p1 p2) p2))
      (Run p3 (Cat.singleton l3) l3 Empty p3)
       Empty


exampleI331E231 :: Text
exampleI331E231 =
  "    \t    one\n\
  \       \t two\n\
  \ \t three\n\
  \"

resultI331E231 :: Layout
resultI331E231 =
  let
    pt1 = "    \t    "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = "       \t "
    p2 = Prefix pt2
    l2 = rel 13 $ Lex.lex $ pt2 <> "two\n"
    pt3 = " \t "
    p3 = Prefix pt3
    l3 = rel 26 $ Lex.lex $ pt3 <> "three\n"
  in
    V 34
       Empty
      (Run p1 (Cat.singleton l1) l1 Empty p1)
      ((Rev . Cat.singleton $ Run p2 (Cat.singleton l2) l2 (Cat.singleton $ LayoutMismatch 13 p1 p2) p2) <>
       (Rev . Cat.singleton $ Run p3 (Cat.singleton l3) l3 (Cat.singleton $ LayoutMismatch 26 p2 p3) p3))

exampleI331E300 :: Text
exampleI331E300 =
  "       \t one\n\
  \         two\n\
  \   three\n\
  \"

resultI331E300 :: Layout
resultI331E300 =
  let
    pt1 = "       \t "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = "         "
    p2 = Prefix pt2
    l2 = rel 13 $ Lex.lex $ pt2 <> "two\n"
    pt3 = "   "
    p3 = Prefix pt3
    l3 = rel 26 $ Lex.lex $ pt3 <> "three\n"
  in
    V 34
      ((Cat.singleton $ Run p1 (Cat.singleton l1) l1 Empty p1) <>
       (Cat.singleton $ Run p2 (Cat.singleton l2) l2 (Cat.singleton $ LayoutMismatch 13 p1 p2) p2))
      (Run p3 (Cat.singleton l3) l3 Empty p3)
       Empty

exampleI331E301 :: Text
exampleI331E301 =
  "       \t one\n\
  \         two\n\
  \ \t three\n\
  \"

resultI331E301 :: Layout
resultI331E301 =
  let
    pt1 = "       \t "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = "         "
    p2 = Prefix pt2
    l2 = rel 13 $ Lex.lex $ pt2 <> "two\n"
    pt3 = " \t "
    p3 = Prefix pt3
    l3 = rel 26 $ Lex.lex $ pt3 <> "three\n"
  in
    V 34
       Empty
      (Run p1 (Cat.singleton l1) l1 Empty p1)
      ((Rev . Cat.singleton $ Run p2 (Cat.singleton l2) l2 (Cat.singleton $ LayoutMismatch 13 p1 p2) p2) <>
       (Rev . Cat.singleton $ Run p3 (Cat.singleton l3) l3 (Cat.singleton $ LayoutMismatch 26 p2 p3) p3))

exampleI331E310 :: Text
exampleI331E310 =
  "       \t one\n\
  \ \t       two\n\
  \   three\n\
  \"

resultI331E310 :: Layout
resultI331E310 =
  let
    pt1 = "       \t "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = " \t       "
    p2 = Prefix pt2
    l2 = rel 13 $ Lex.lex $ pt2 <> "two\n"
    pt3 = "   "
    p3 = Prefix pt3
    l3 = rel 26 $ Lex.lex $ pt3 <> "three\n"
  in
    V 34
       Empty
      (Run p1 (Cat.singleton l1) l1 Empty p1)
      ((Rev . Cat.singleton $ Run p2 (Cat.singleton l2) l2 (Cat.singleton $ LayoutMismatch 13 p1 p2) p2) <>
       (Rev . Cat.singleton $ Run p3 (Cat.singleton l3) l3 (Cat.singleton $ LayoutMismatch 26 p2 p3) p3))

exampleI331E311 :: Text
exampleI331E311 =
  "       \t one\n\
  \ \t       two\n\
  \ \t three\n\
  \"

resultI331E311 :: Layout
resultI331E311 =
  let
    pt1 = "       \t "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = " \t       "
    p2 = Prefix pt2
    l2 = rel 13 $ Lex.lex $ pt2 <> "two\n"
    pt3 = " \t "
    p3 = Prefix pt3
    l3 = rel 26 $ Lex.lex $ pt3 <> "three\n"
  in
    V 34
       Empty
      (Run p1 (Cat.singleton l1) l1 Empty p1)
      ((Rev . Cat.singleton $ Run p2 (Cat.singleton l2) l2 (Cat.singleton $ LayoutMismatch 13 p1 p2) p2) <>
       (Rev . Cat.singleton $ Run p3 (Cat.singleton l3) l3 Empty p3))

exampleI331E320 :: Text
exampleI331E320 =
  "       \t one\n\
  \    \t    two\n\
  \   three\n\
  \"

resultI331E320 :: Layout
resultI331E320 =
  let
    pt1 = "       \t "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = "    \t    "
    p2 = Prefix pt2
    l2 = rel 13 $ Lex.lex $ pt2 <> "two\n"
    pt3 = "   "
    p3 = Prefix pt3
    l3 = rel 26 $ Lex.lex $ pt3 <> "three\n"
  in
    V 34
      ((Cat.singleton $ Run p1 (Cat.singleton l1) l1 Empty p1) <>
       (Cat.singleton $ Run p2 (Cat.singleton l2) l2 (Cat.singleton $ LayoutMismatch 13 p1 p2) p2))
      (Run p3 (Cat.singleton l3) l3 Empty p3)
       Empty

exampleI331E321 :: Text
exampleI331E321 =
  "       \t one\n\
  \    \t    two\n\
  \ \t three\n\
  \"

resultI331E321 :: Layout
resultI331E321 =
  let
    pt1 = "       \t "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = "    \t    "
    p2 = Prefix pt2
    l2 = rel 13 $ Lex.lex $ pt2 <> "two\n"
    pt3 = " \t "
    p3 = Prefix pt3
    l3 = rel 26 $ Lex.lex $ pt3 <> "three\n"
  in
    V 34
       Empty
      (Run p1 (Cat.singleton l1) l1 Empty p1)
      ((Rev . Cat.singleton $ Run p2 (Cat.singleton l2) l2 (Cat.singleton $ LayoutMismatch 13 p1 p2) p2) <>
       (Rev . Cat.singleton $ Run p3 (Cat.singleton l3) l3 (Cat.singleton $ LayoutMismatch 26 p2 p3) p3))

exampleI331E330 :: Text
exampleI331E330 =
  "       \t one\n\
  \       \t two\n\
  \   three\n\
  \"

resultI331E330 :: Layout
resultI331E330 =
  let
    pt1 = "       \t "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = "       \t "
    p2 = Prefix pt2
    l2 = rel 13 $ Lex.lex $ pt2 <> "two\n"
    pt3 = "   "
    p3 = Prefix pt3
    l3 = rel 26 $ Lex.lex $ pt3 <> "three\n"
  in
    V 34
      ((Cat.singleton $ Run p1 (Cat.singleton l1) l1 Empty p1) <>
       (Cat.singleton $ Run p2 (Cat.singleton l2) l2 Empty p2))
      (Run p3 (Cat.singleton l3) l3 Empty p3)
       Empty

exampleI331E331 :: Text
exampleI331E331 =
  "       \t one\n\
  \       \t two\n\
  \ \t three\n\
  \"

resultI331E331 :: Layout
resultI331E331 =
  let
    pt1 = "       \t "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = "       \t "
    p2 = Prefix pt2
    l2 = rel 13 $ Lex.lex $ pt2 <> "two\n"
    pt3 = " \t "
    p3 = Prefix pt3
    l3 = rel 26 $ Lex.lex $ pt3 <> "three\n"
  in
    V 34
       Empty
      (Run p1 (Cat.singleton l1) l1 Empty p1)
      ((Rev . Cat.singleton $ Run p2 (Cat.singleton l2) l2 Empty p2) <>
       (Rev . Cat.singleton $ Run p3 (Cat.singleton l3) l3 (Cat.singleton $ LayoutMismatch 26 p2 p3) p3))

exampleI332E000 :: Text
exampleI332E000 =
  "         one\n\
  \         two\n\
  \      three\n\
  \"

resultI332E000 :: Layout
resultI332E000 =
  let
    pt1 = "         "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = "         "
    p2 = Prefix pt2
    l2 = rel 13 $ Lex.lex $ pt2 <> "two\n"
    pt3 = "      "
    p3 = Prefix pt3
    l3 = rel 26 $ Lex.lex $ pt3 <> "three\n"
  in
    V 37
      ((Cat.singleton $ Run p1 (Cat.singleton l1) l1 Empty p1) <>
       (Cat.singleton $ Run p2 (Cat.singleton l2) l2 Empty p2))
      (Run p3 (Cat.singleton l3) l3 Empty p3)
       Empty

exampleI332E001 :: Text
exampleI332E001 =
  "         one\n\
  \         two\n\
  \ \t    three\n\
  \"

resultI332E001 :: Layout
resultI332E001 =
  let
    pt1 = "         "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = "         "
    p2 = Prefix pt2
    l2 = rel 13 $ Lex.lex $ pt2 <> "two\n"
    pt3 = " \t    "
    p3 = Prefix pt3
    l3 = rel 26 $ Lex.lex $ pt3 <> "three\n"
  in
    V 37
       Empty
      (Run p1 (Cat.singleton l1) l1 Empty p1)
      ((Rev . Cat.singleton $ Run p2 (Cat.singleton l2) l2 Empty p2) <>
       (Rev . Cat.singleton $ Run p3 (Cat.singleton l3) l3 (Cat.singleton $ LayoutMismatch 26 p2 p3) p3))

exampleI332E002 :: Text
exampleI332E002 =
  "         one\n\
  \         two\n\
  \    \t three\n\
  \"

resultI332E002 :: Layout
resultI332E002 =
  let
    pt1 = "         "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = "         "
    p2 = Prefix pt2
    l2 = rel 13 $ Lex.lex $ pt2 <> "two\n"
    pt3 = "    \t "
    p3 = Prefix pt3
    l3 = rel 26 $ Lex.lex $ pt3 <> "three\n"
  in
    V 37
       Empty
      (Run p1 (Cat.singleton l1) l1 Empty p1)
      ((Rev . Cat.singleton $ Run p2 (Cat.singleton l2) l2 Empty p2) <>
       (Rev . Cat.singleton $ Run p3 (Cat.singleton l3) l3 (Cat.singleton $ LayoutMismatch 26 p2 p3) p3))

exampleI332E010 :: Text
exampleI332E010 =
  "         one\n\
  \ \t       two\n\
  \      three\n\
  \"

resultI332E010 :: Layout
resultI332E010 =
  let
    pt1 = "         "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = " \t       "
    p2 = Prefix pt2
    l2 = rel 13 $ Lex.lex $ pt2 <> "two\n"
    pt3 = "      "
    p3 = Prefix pt3
    l3 = rel 26 $ Lex.lex $ pt3 <> "three\n"
  in
    V 37
       Empty
      (Run p1 (Cat.singleton l1) l1 Empty p1)
      ((Rev . Cat.singleton $ Run p2 (Cat.singleton l2) l2 (Cat.singleton $ LayoutMismatch 13 p1 p2) p2) <>
       (Rev . Cat.singleton $ Run p3 (Cat.singleton l3) l3 (Cat.singleton $ LayoutMismatch 26 p2 p3) p3))

exampleI332E011 :: Text
exampleI332E011 =
  "         one\n\
  \ \t       two\n\
  \ \t    three\n\
  \"

resultI332E011 :: Layout
resultI332E011 =
  let
    pt1 = "         "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = " \t       "
    p2 = Prefix pt2
    l2 = rel 13 $ Lex.lex $ pt2 <> "two\n"
    pt3 = " \t    "
    p3 = Prefix pt3
    l3 = rel 26 $ Lex.lex $ pt3 <> "three\n"
  in
    V 37
       Empty
      (Run p1 (Cat.singleton l1) l1 Empty p1)
      ((Rev . Cat.singleton $ Run p2 (Cat.singleton l2) l2 (Cat.singleton $ LayoutMismatch 13 p1 p2) p2) <>
       (Rev . Cat.singleton $ Run p3 (Cat.singleton l3) l3 Empty p3))

exampleI332E012 :: Text
exampleI332E012 =
  "         one\n\
  \ \t       two\n\
  \    \t three\n\
  \"

resultI332E012 :: Layout
resultI332E012 =
  let
    pt1 = "         "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = " \t       "
    p2 = Prefix pt2
    l2 = rel 13 $ Lex.lex $ pt2 <> "two\n"
    pt3 = "    \t "
    p3 = Prefix pt3
    l3 = rel 26 $ Lex.lex $ pt3 <> "three\n"
  in
    V 37
       Empty
      (Run p1 (Cat.singleton l1) l1 Empty p1)
      ((Rev . Cat.singleton $ Run p2 (Cat.singleton l2) l2 (Cat.singleton $ LayoutMismatch 13 p1 p2) p2) <>
       (Rev . Cat.singleton $ Run p3 (Cat.singleton l3) l3 (Cat.singleton $ LayoutMismatch 26 p2 p3) p3))

exampleI332E020 :: Text
exampleI332E020 =
  "         one\n\
  \    \t    two\n\
  \      three\n\
  \"

resultI332E020 :: Layout
resultI332E020 =
  let
    pt1 = "         "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = "    \t    "
    p2 = Prefix pt2
    l2 = rel 13 $ Lex.lex $ pt2 <> "two\n"
    pt3 = "      "
    p3 = Prefix pt3
    l3 = rel 26 $ Lex.lex $ pt3 <> "three\n"
  in
    V 37
       Empty
      (Run p1 (Cat.singleton l1) l1 Empty p1)
      ((Rev . Cat.singleton $ Run p2 (Cat.singleton l2) l2 (Cat.singleton $ LayoutMismatch 13 p1 p2) p2) <>
       (Rev . Cat.singleton $ Run p3 (Cat.singleton l3) l3 (Cat.singleton $ LayoutMismatch 26 p2 p3) p3))

exampleI332E021 :: Text
exampleI332E021 =
  "         one\n\
  \    \t    two\n\
  \ \t    three\n\
  \"

resultI332E021 :: Layout
resultI332E021 =
  let
    pt1 = "         "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = "    \t    "
    p2 = Prefix pt2
    l2 = rel 13 $ Lex.lex $ pt2 <> "two\n"
    pt3 = " \t    "
    p3 = Prefix pt3
    l3 = rel 26 $ Lex.lex $ pt3 <> "three\n"
  in
    V 37
       Empty
      (Run p1 (Cat.singleton l1) l1 Empty p1)
      ((Rev . Cat.singleton $ Run p2 (Cat.singleton l2) l2 (Cat.singleton $ LayoutMismatch 13 p1 p2) p2) <>
       (Rev . Cat.singleton $ Run p3 (Cat.singleton l3) l3 (Cat.singleton $ LayoutMismatch 26 p2 p3) p3))

exampleI332E022 :: Text
exampleI332E022 =
  "         one\n\
  \    \t    two\n\
  \    \t three\n\
  \"

resultI332E022 :: Layout
resultI332E022 =
  let
    pt1 = "         "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = "    \t    "
    p2 = Prefix pt2
    l2 = rel 13 $ Lex.lex $ pt2 <> "two\n"
    pt3 = "    \t "
    p3 = Prefix pt3
    l3 = rel 26 $ Lex.lex $ pt3 <> "three\n"
  in
    V 37
       Empty
      (Run p1 (Cat.singleton l1) l1 Empty p1)
      ((Rev . Cat.singleton $ Run p2 (Cat.singleton l2) l2 (Cat.singleton $ LayoutMismatch 13 p1 p2) p2) <>
       (Rev . Cat.singleton $ Run p3 (Cat.singleton l3) l3 Empty p3))

exampleI332E030 :: Text
exampleI332E030 =
  "         one\n\
  \       \t two\n\
  \      three\n\
  \"

resultI332E030 :: Layout
resultI332E030 =
  let
    pt1 = "         "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = "       \t "
    p2 = Prefix pt2
    l2 = rel 13 $ Lex.lex $ pt2 <> "two\n"
    pt3 = "      "
    p3 = Prefix pt3
    l3 = rel 26 $ Lex.lex $ pt3 <> "three\n"
  in
    V 37
      ((Cat.singleton $ Run p1 (Cat.singleton l1) l1 Empty p1) <>
       (Cat.singleton $ Run p2 (Cat.singleton l2) l2 (Cat.singleton $ LayoutMismatch 13 p1 p2) p2))
      (Run p3 (Cat.singleton l3) l3 Empty p3)
       Empty

exampleI332E031 :: Text
exampleI332E031 =
  "         one\n\
  \       \t two\n\
  \ \t    three\n\
  \"

resultI332E031 :: Layout
resultI332E031 =
  let
    pt1 = "         "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = "       \t "
    p2 = Prefix pt2
    l2 = rel 13 $ Lex.lex $ pt2 <> "two\n"
    pt3 = " \t    "
    p3 = Prefix pt3
    l3 = rel 26 $ Lex.lex $ pt3 <> "three\n"
  in
    V 37
       Empty
      (Run p1 (Cat.singleton l1) l1 Empty p1)
      ((Rev . Cat.singleton $ Run p2 (Cat.singleton l2) l2 (Cat.singleton $ LayoutMismatch 13 p1 p2) p2) <>
       (Rev . Cat.singleton $ Run p3 (Cat.singleton l3) l3 (Cat.singleton $ LayoutMismatch 26 p2 p3) p3))

exampleI332E032 :: Text
exampleI332E032 =
  "         one\n\
  \       \t two\n\
  \    \t three\n\
  \"

resultI332E032 :: Layout
resultI332E032 =
  let
    pt1 = "         "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = "       \t "
    p2 = Prefix pt2
    l2 = rel 13 $ Lex.lex $ pt2 <> "two\n"
    pt3 = "    \t "
    p3 = Prefix pt3
    l3 = rel 26 $ Lex.lex $ pt3 <> "three\n"
  in
    V 37
       Empty
      (Run p1 (Cat.singleton l1) l1 Empty p1)
      ((Rev . Cat.singleton $ Run p2 (Cat.singleton l2) l2 (Cat.singleton $ LayoutMismatch 13 p1 p2) p2) <>
       (Rev . Cat.singleton $ Run p3 (Cat.singleton l3) l3 (Cat.singleton $ LayoutMismatch 26 p2 p3) p3))

exampleI332E100 :: Text
exampleI332E100 =
  " \t       one\n\
  \         two\n\
  \      three\n\
  \"

resultI332E100 :: Layout
resultI332E100 =
  let
    pt1 = " \t       "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = "         "
    p2 = Prefix pt2
    l2 = rel 13 $ Lex.lex $ pt2 <> "two\n"
    pt3 = "      "
    p3 = Prefix pt3
    l3 = rel 26 $ Lex.lex $ pt3 <> "three\n"
  in
    V 37
       Empty
      (Run p1 (Cat.singleton l1) l1 Empty p1)
      ((Rev . Cat.singleton $ Run p2 (Cat.singleton l2) l2 (Cat.singleton $ LayoutMismatch 13 p1 p2) p2) <>
       (Rev . Cat.singleton $ Run p3 (Cat.singleton l3) l3 Empty p3))

exampleI332E101 :: Text
exampleI332E101 =
  " \t       one\n\
  \         two\n\
  \ \t    three\n\
  \"

resultI332E101 :: Layout
resultI332E101 =
  let
    pt1 = " \t       "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = "         "
    p2 = Prefix pt2
    l2 = rel 13 $ Lex.lex $ pt2 <> "two\n"
    pt3 = " \t    "
    p3 = Prefix pt3
    l3 = rel 26 $ Lex.lex $ pt3 <> "three\n"
  in
    V 37
       Empty
      (Run p1 (Cat.singleton l1) l1 Empty p1)
      ((Rev . Cat.singleton $ Run p2 (Cat.singleton l2) l2 (Cat.singleton $ LayoutMismatch 13 p1 p2) p2) <>
       (Rev . Cat.singleton $ Run p3 (Cat.singleton l3) l3 (Cat.singleton $ LayoutMismatch 26 p2 p3) p3))

exampleI332E102 :: Text
exampleI332E102 =
  " \t       one\n\
  \         two\n\
  \    \t three\n\
  \"

resultI332E102 :: Layout
resultI332E102 =
  let
    pt1 = " \t       "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = "         "
    p2 = Prefix pt2
    l2 = rel 13 $ Lex.lex $ pt2 <> "two\n"
    pt3 = "    \t "
    p3 = Prefix pt3
    l3 = rel 26 $ Lex.lex $ pt3 <> "three\n"
  in
    V 37
       Empty
      (Run p1 (Cat.singleton l1) l1 Empty p1)
      ((Rev . Cat.singleton $ Run p2 (Cat.singleton l2) l2 (Cat.singleton $ LayoutMismatch 13 p1 p2) p2) <>
       (Rev . Cat.singleton $ Run p3 (Cat.singleton l3) l3 (Cat.singleton $ LayoutMismatch 26 p2 p3) p3))

exampleI332E110 :: Text
exampleI332E110 =
  " \t       one\n\
  \ \t       two\n\
  \      three\n\
  \"

resultI332E110 :: Layout
resultI332E110 =
  let
    pt1 = " \t       "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = " \t       "
    p2 = Prefix pt2
    l2 = rel 13 $ Lex.lex $ pt2 <> "two\n"
    pt3 = "      "
    p3 = Prefix pt3
    l3 = rel 26 $ Lex.lex $ pt3 <> "three\n"
  in
    V 37
       Empty
      (Run p1 (Cat.singleton l1) l1 Empty p1)
      ((Rev . Cat.singleton $ Run p2 (Cat.singleton l2) l2 Empty p2) <>
       (Rev . Cat.singleton $ Run p3 (Cat.singleton l3) l3 (Cat.singleton $ LayoutMismatch 26 p2 p3) p3))

exampleI332E111 :: Text
exampleI332E111 =
  " \t       one\n\
  \ \t       two\n\
  \ \t    three\n\
  \"

resultI332E111 :: Layout
resultI332E111 =
  let
    pt1 = " \t       "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = " \t       "
    p2 = Prefix pt2
    l2 = rel 13 $ Lex.lex $ pt2 <> "two\n"
    pt3 = " \t    "
    p3 = Prefix pt3
    l3 = rel 26 $ Lex.lex $ pt3 <> "three\n"
  in
    V 37
      ((Cat.singleton $ Run p1 (Cat.singleton l1) l1 Empty p1) <>
       (Cat.singleton $ Run p2 (Cat.singleton l2) l2 Empty p2))
      (Run p3 (Cat.singleton l3) l3 Empty p3)
       Empty

exampleI332E112 :: Text
exampleI332E112 =
  " \t       one\n\
  \ \t       two\n\
  \    \t three\n\
  \"

resultI332E112 :: Layout
resultI332E112 =
  let
    pt1 = " \t       "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = " \t       "
    p2 = Prefix pt2
    l2 = rel 13 $ Lex.lex $ pt2 <> "two\n"
    pt3 = "    \t "
    p3 = Prefix pt3
    l3 = rel 26 $ Lex.lex $ pt3 <> "three\n"
  in
    V 37
       Empty
      (Run p1 (Cat.singleton l1) l1 Empty p1)
      ((Rev . Cat.singleton $ Run p2 (Cat.singleton l2) l2 Empty p2) <>
       (Rev . Cat.singleton $ Run p3 (Cat.singleton l3) l3 (Cat.singleton $ LayoutMismatch 26 p2 p3) p3))

exampleI332E120 :: Text
exampleI332E120 =
  " \t       one\n\
  \    \t    two\n\
  \      three\n\
  \"

resultI332E120 :: Layout
resultI332E120 =
  let
    pt1 = " \t       "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = "    \t    "
    p2 = Prefix pt2
    l2 = rel 13 $ Lex.lex $ pt2 <> "two\n"
    pt3 = "      "
    p3 = Prefix pt3
    l3 = rel 26 $ Lex.lex $ pt3 <> "three\n"
  in
    V 37
       Empty
      (Run p1 (Cat.singleton l1) l1 Empty p1)
      ((Rev . Cat.singleton $ Run p2 (Cat.singleton l2) l2 (Cat.singleton $ LayoutMismatch 13 p1 p2) p2) <>
       (Rev . Cat.singleton $ Run p3 (Cat.singleton l3) l3 (Cat.singleton $ LayoutMismatch 26 p2 p3) p3))

exampleI332E121 :: Text
exampleI332E121 =
  " \t       one\n\
  \    \t    two\n\
  \ \t    three\n\
  \"

resultI332E121 :: Layout
resultI332E121 =
  let
    pt1 = " \t       "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = "    \t    "
    p2 = Prefix pt2
    l2 = rel 13 $ Lex.lex $ pt2 <> "two\n"
    pt3 = " \t    "
    p3 = Prefix pt3
    l3 = rel 26 $ Lex.lex $ pt3 <> "three\n"
  in
    V 37
       Empty
      (Run p1 (Cat.singleton l1) l1 Empty p1)
      ((Rev . Cat.singleton $ Run p2 (Cat.singleton l2) l2 (Cat.singleton $ LayoutMismatch 13 p1 p2) p2) <>
       (Rev . Cat.singleton $ Run p3 (Cat.singleton l3) l3 (Cat.singleton $ LayoutMismatch 26 p2 p3) p3))

exampleI332E122 :: Text
exampleI332E122 =
  " \t       one\n\
  \    \t    two\n\
  \    \t three\n\
  \"

resultI332E122 :: Layout
resultI332E122 =
  let
    pt1 = " \t       "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = "    \t    "
    p2 = Prefix pt2
    l2 = rel 13 $ Lex.lex $ pt2 <> "two\n"
    pt3 = "    \t "
    p3 = Prefix pt3
    l3 = rel 26 $ Lex.lex $ pt3 <> "three\n"
  in
    V 37
       Empty
      (Run p1 (Cat.singleton l1) l1 Empty p1)
      ((Rev . Cat.singleton $ Run p2 (Cat.singleton l2) l2 (Cat.singleton $ LayoutMismatch 13 p1 p2) p2) <>
       (Rev . Cat.singleton $ Run p3 (Cat.singleton l3) l3 Empty p3))

exampleI332E130 :: Text
exampleI332E130 =
  " \t       one\n\
  \       \t two\n\
  \      three\n\
  \"

resultI332E130 :: Layout
resultI332E130 =
  let
    pt1 = " \t       "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = "       \t "
    p2 = Prefix pt2
    l2 = rel 13 $ Lex.lex $ pt2 <> "two\n"
    pt3 = "      "
    p3 = Prefix pt3
    l3 = rel 26 $ Lex.lex $ pt3 <> "three\n"
  in
    V 37
       Empty
      (Run p1 (Cat.singleton l1) l1 Empty p1)
      ((Rev . Cat.singleton $ Run p2 (Cat.singleton l2) l2 (Cat.singleton $ LayoutMismatch 13 p1 p2) p2) <>
       (Rev . Cat.singleton $ Run p3 (Cat.singleton l3) l3 Empty p3))

exampleI332E131 :: Text
exampleI332E131 =
  " \t       one\n\
  \       \t two\n\
  \ \t    three\n\
  \"

resultI332E131 :: Layout
resultI332E131 =
  let
    pt1 = " \t       "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = "       \t "
    p2 = Prefix pt2
    l2 = rel 13 $ Lex.lex $ pt2 <> "two\n"
    pt3 = " \t    "
    p3 = Prefix pt3
    l3 = rel 26 $ Lex.lex $ pt3 <> "three\n"
  in
    V 37
       Empty
      (Run p1 (Cat.singleton l1) l1 Empty p1)
      ((Rev . Cat.singleton $ Run p2 (Cat.singleton l2) l2 (Cat.singleton $ LayoutMismatch 13 p1 p2) p2) <>
       (Rev . Cat.singleton $ Run p3 (Cat.singleton l3) l3 (Cat.singleton $ LayoutMismatch 26 p2 p3) p3))

exampleI332E132 :: Text
exampleI332E132 =
  " \t       one\n\
  \       \t two\n\
  \    \t three\n\
  \"

resultI332E132 :: Layout
resultI332E132 =
  let
    pt1 = " \t       "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = "       \t "
    p2 = Prefix pt2
    l2 = rel 13 $ Lex.lex $ pt2 <> "two\n"
    pt3 = "    \t "
    p3 = Prefix pt3
    l3 = rel 26 $ Lex.lex $ pt3 <> "three\n"
  in
    V 37
       Empty
      (Run p1 (Cat.singleton l1) l1 Empty p1)
      ((Rev . Cat.singleton $ Run p2 (Cat.singleton l2) l2 (Cat.singleton $ LayoutMismatch 13 p1 p2) p2) <>
       (Rev . Cat.singleton $ Run p3 (Cat.singleton l3) l3 (Cat.singleton $ LayoutMismatch 26 p2 p3) p3))

exampleI332E200 :: Text
exampleI332E200 =
  "    \t    one\n\
  \         two\n\
  \      three\n\
  \"

resultI332E200 :: Layout
resultI332E200 =
  let
    pt1 = "    \t    "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = "         "
    p2 = Prefix pt2
    l2 = rel 13 $ Lex.lex $ pt2 <> "two\n"
    pt3 = "      "
    p3 = Prefix pt3
    l3 = rel 26 $ Lex.lex $ pt3 <> "three\n"
  in
    V 37
       Empty
      (Run p1 (Cat.singleton l1) l1 Empty p1)
      ((Rev . Cat.singleton $ Run p2 (Cat.singleton l2) l2 (Cat.singleton $ LayoutMismatch 13 p1 p2) p2) <>
       (Rev . Cat.singleton $ Run p3 (Cat.singleton l3) l3 Empty p3))

exampleI332E201 :: Text
exampleI332E201 =
  "    \t    one\n\
  \         two\n\
  \ \t    three\n\
  \"

resultI332E201 :: Layout
resultI332E201 =
  let
    pt1 = "    \t    "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = "         "
    p2 = Prefix pt2
    l2 = rel 13 $ Lex.lex $ pt2 <> "two\n"
    pt3 = " \t    "
    p3 = Prefix pt3
    l3 = rel 26 $ Lex.lex $ pt3 <> "three\n"
  in
    V 37
       Empty
      (Run p1 (Cat.singleton l1) l1 Empty p1)
      ((Rev . Cat.singleton $ Run p2 (Cat.singleton l2) l2 (Cat.singleton $ LayoutMismatch 13 p1 p2) p2) <>
       (Rev . Cat.singleton $ Run p3 (Cat.singleton l3) l3 (Cat.singleton $ LayoutMismatch 26 p2 p3) p3))

exampleI332E202 :: Text
exampleI332E202 =
  "    \t    one\n\
  \         two\n\
  \    \t three\n\
  \"

resultI332E202 :: Layout
resultI332E202 =
  let
    pt1 = "    \t    "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = "         "
    p2 = Prefix pt2
    l2 = rel 13 $ Lex.lex $ pt2 <> "two\n"
    pt3 = "    \t "
    p3 = Prefix pt3
    l3 = rel 26 $ Lex.lex $ pt3 <> "three\n"
  in
    V 37
       Empty
      (Run p1 (Cat.singleton l1) l1 Empty p1)
      ((Rev . Cat.singleton $ Run p2 (Cat.singleton l2) l2 (Cat.singleton $ LayoutMismatch 13 p1 p2) p2) <>
       (Rev . Cat.singleton $ Run p3 (Cat.singleton l3) l3 (Cat.singleton $ LayoutMismatch 26 p2 p3) p3))

exampleI332E210 :: Text
exampleI332E210 =
  "    \t    one\n\
  \ \t       two\n\
  \      three\n\
  \"

resultI332E210 :: Layout
resultI332E210 =
  let
    pt1 = "    \t    "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = " \t       "
    p2 = Prefix pt2
    l2 = rel 13 $ Lex.lex $ pt2 <> "two\n"
    pt3 = "      "
    p3 = Prefix pt3
    l3 = rel 26 $ Lex.lex $ pt3 <> "three\n"
  in
    V 37
       Empty
      (Run p1 (Cat.singleton l1) l1 Empty p1)
      ((Rev . Cat.singleton $ Run p2 (Cat.singleton l2) l2 (Cat.singleton $ LayoutMismatch 13 p1 p2) p2) <>
       (Rev . Cat.singleton $ Run p3 (Cat.singleton l3) l3 (Cat.singleton $ LayoutMismatch 26 p2 p3) p3))

exampleI332E211 :: Text
exampleI332E211 =
  "    \t    one\n\
  \ \t       two\n\
  \ \t    three\n\
  \"

resultI332E211 :: Layout
resultI332E211 =
  let
    pt1 = "    \t    "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = " \t       "
    p2 = Prefix pt2
    l2 = rel 13 $ Lex.lex $ pt2 <> "two\n"
    pt3 = " \t    "
    p3 = Prefix pt3
    l3 = rel 26 $ Lex.lex $ pt3 <> "three\n"
  in
    V 37
       Empty
      (Run p1 (Cat.singleton l1) l1 Empty p1)
      ((Rev . Cat.singleton $ Run p2 (Cat.singleton l2) l2 (Cat.singleton $ LayoutMismatch 13 p1 p2) p2) <>
       (Rev . Cat.singleton $ Run p3 (Cat.singleton l3) l3 Empty p3))

exampleI332E212 :: Text
exampleI332E212 =
  "    \t    one\n\
  \ \t       two\n\
  \    \t three\n\
  \"

resultI332E212 :: Layout
resultI332E212 =
  let
    pt1 = "    \t    "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = " \t       "
    p2 = Prefix pt2
    l2 = rel 13 $ Lex.lex $ pt2 <> "two\n"
    pt3 = "    \t "
    p3 = Prefix pt3
    l3 = rel 26 $ Lex.lex $ pt3 <> "three\n"
  in
    V 37
       Empty
      (Run p1 (Cat.singleton l1) l1 Empty p1)
      ((Rev . Cat.singleton $ Run p2 (Cat.singleton l2) l2 (Cat.singleton $ LayoutMismatch 13 p1 p2) p2) <>
       (Rev . Cat.singleton $ Run p3 (Cat.singleton l3) l3 (Cat.singleton $ LayoutMismatch 26 p2 p3) p3))

exampleI332E220 :: Text
exampleI332E220 =
  "    \t    one\n\
  \    \t    two\n\
  \      three\n\
  \"

resultI332E220 :: Layout
resultI332E220 =
  let
    pt1 = "    \t    "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = "    \t    "
    p2 = Prefix pt2
    l2 = rel 13 $ Lex.lex $ pt2 <> "two\n"
    pt3 = "      "
    p3 = Prefix pt3
    l3 = rel 26 $ Lex.lex $ pt3 <> "three\n"
  in
    V 37
       Empty
      (Run p1 (Cat.singleton l1) l1 Empty p1)
      ((Rev . Cat.singleton $ Run p2 (Cat.singleton l2) l2 Empty p2) <>
       (Rev . Cat.singleton $ Run p3 (Cat.singleton l3) l3 (Cat.singleton $ LayoutMismatch 26 p2 p3) p3))

exampleI332E221 :: Text
exampleI332E221 =
  "    \t    one\n\
  \    \t    two\n\
  \ \t    three\n\
  \"

resultI332E221 :: Layout
resultI332E221 =
  let
    pt1 = "    \t    "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = "    \t    "
    p2 = Prefix pt2
    l2 = rel 13 $ Lex.lex $ pt2 <> "two\n"
    pt3 = " \t    "
    p3 = Prefix pt3
    l3 = rel 26 $ Lex.lex $ pt3 <> "three\n"
  in
    V 37
       Empty
      (Run p1 (Cat.singleton l1) l1 Empty p1)
      ((Rev . Cat.singleton $ Run p2 (Cat.singleton l2) l2 Empty p2) <>
       (Rev . Cat.singleton $ Run p3 (Cat.singleton l3) l3 (Cat.singleton $ LayoutMismatch 26 p2 p3) p3))

exampleI332E222 :: Text
exampleI332E222 =
  "    \t    one\n\
  \    \t    two\n\
  \    \t three\n\
  \"

resultI332E222 :: Layout
resultI332E222 =
  let
    pt1 = "    \t    "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = "    \t    "
    p2 = Prefix pt2
    l2 = rel 13 $ Lex.lex $ pt2 <> "two\n"
    pt3 = "    \t "
    p3 = Prefix pt3
    l3 = rel 26 $ Lex.lex $ pt3 <> "three\n"
  in
    V 37
      ((Cat.singleton $ Run p1 (Cat.singleton l1) l1 Empty p1) <>
       (Cat.singleton $ Run p2 (Cat.singleton l2) l2 Empty p2))
      (Run p3 (Cat.singleton l3) l3 Empty p3)
       Empty

exampleI332E230 :: Text
exampleI332E230 =
  "    \t    one\n\
  \       \t two\n\
  \      three\n\
  \"

resultI332E230 :: Layout
resultI332E230 =
  let
    pt1 = "    \t    "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = "       \t "
    p2 = Prefix pt2
    l2 = rel 13 $ Lex.lex $ pt2 <> "two\n"
    pt3 = "      "
    p3 = Prefix pt3
    l3 = rel 26 $ Lex.lex $ pt3 <> "three\n"
  in
    V 37
       Empty
      (Run p1 (Cat.singleton l1) l1 Empty p1)
      ((Rev . Cat.singleton $ Run p2 (Cat.singleton l2) l2 (Cat.singleton $ LayoutMismatch 13 p1 p2) p2) <>
       (Rev . Cat.singleton $ Run p3 (Cat.singleton l3) l3 Empty p3))

exampleI332E231 :: Text
exampleI332E231 =
  "    \t    one\n\
  \       \t two\n\
  \ \t    three\n\
  \"

resultI332E231 :: Layout
resultI332E231 =
  let
    pt1 = "    \t    "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = "       \t "
    p2 = Prefix pt2
    l2 = rel 13 $ Lex.lex $ pt2 <> "two\n"
    pt3 = " \t    "
    p3 = Prefix pt3
    l3 = rel 26 $ Lex.lex $ pt3 <> "three\n"
  in
    V 37
       Empty
      (Run p1 (Cat.singleton l1) l1 Empty p1)
      ((Rev . Cat.singleton $ Run p2 (Cat.singleton l2) l2 (Cat.singleton $ LayoutMismatch 13 p1 p2) p2) <>
       (Rev . Cat.singleton $ Run p3 (Cat.singleton l3) l3 (Cat.singleton $ LayoutMismatch 26 p2 p3) p3))

exampleI332E232 :: Text
exampleI332E232 =
  "    \t    one\n\
  \       \t two\n\
  \    \t three\n\
  \"

resultI332E232 :: Layout
resultI332E232 =
  let
    pt1 = "    \t    "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = "       \t "
    p2 = Prefix pt2
    l2 = rel 13 $ Lex.lex $ pt2 <> "two\n"
    pt3 = "    \t "
    p3 = Prefix pt3
    l3 = rel 26 $ Lex.lex $ pt3 <> "three\n"
  in
    V 37
       Empty
      (Run p1 (Cat.singleton l1) l1 Empty p1)
      ((Rev . Cat.singleton $ Run p2 (Cat.singleton l2) l2 (Cat.singleton $ LayoutMismatch 13 p1 p2) p2) <>
       (Rev . Cat.singleton $ Run p3 (Cat.singleton l3) l3 (Cat.singleton $ LayoutMismatch 26 p2 p3) p3))

exampleI332E300 :: Text
exampleI332E300 =
  "       \t one\n\
  \         two\n\
  \      three\n\
  \"

resultI332E300 :: Layout
resultI332E300 =
  let
    pt1 = "       \t "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = "         "
    p2 = Prefix pt2
    l2 = rel 13 $ Lex.lex $ pt2 <> "two\n"
    pt3 = "      "
    p3 = Prefix pt3
    l3 = rel 26 $ Lex.lex $ pt3 <> "three\n"
  in
    V 37
      ((Cat.singleton $ Run p1 (Cat.singleton l1) l1 Empty p1) <>
       (Cat.singleton $ Run p2 (Cat.singleton l2) l2 (Cat.singleton $ LayoutMismatch 13 p1 p2) p2))
      (Run p3 (Cat.singleton l3) l3 Empty p3)
       Empty

exampleI332E301 :: Text
exampleI332E301 =
  "       \t one\n\
  \         two\n\
  \ \t    three\n\
  \"

resultI332E301 :: Layout
resultI332E301 =
  let
    pt1 = "       \t "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = "         "
    p2 = Prefix pt2
    l2 = rel 13 $ Lex.lex $ pt2 <> "two\n"
    pt3 = " \t    "
    p3 = Prefix pt3
    l3 = rel 26 $ Lex.lex $ pt3 <> "three\n"
  in
    V 37
       Empty
      (Run p1 (Cat.singleton l1) l1 Empty p1)
      ((Rev . Cat.singleton $ Run p2 (Cat.singleton l2) l2 (Cat.singleton $ LayoutMismatch 13 p1 p2) p2) <>
       (Rev . Cat.singleton $ Run p3 (Cat.singleton l3) l3 (Cat.singleton $ LayoutMismatch 26 p2 p3) p3))

exampleI332E302 :: Text
exampleI332E302 =
  "       \t one\n\
  \         two\n\
  \    \t three\n\
  \"

resultI332E302 :: Layout
resultI332E302 =
  let
    pt1 = "       \t "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = "         "
    p2 = Prefix pt2
    l2 = rel 13 $ Lex.lex $ pt2 <> "two\n"
    pt3 = "    \t "
    p3 = Prefix pt3
    l3 = rel 26 $ Lex.lex $ pt3 <> "three\n"
  in
    V 37
       Empty
      (Run p1 (Cat.singleton l1) l1 Empty p1)
      ((Rev . Cat.singleton $ Run p2 (Cat.singleton l2) l2 (Cat.singleton $ LayoutMismatch 13 p1 p2) p2) <>
       (Rev . Cat.singleton $ Run p3 (Cat.singleton l3) l3 (Cat.singleton $ LayoutMismatch 26 p2 p3) p3))

exampleI332E310 :: Text
exampleI332E310 =
  "       \t one\n\
  \ \t       two\n\
  \      three\n\
  \"

resultI332E310 :: Layout
resultI332E310 =
  let
    pt1 = "       \t "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = " \t       "
    p2 = Prefix pt2
    l2 = rel 13 $ Lex.lex $ pt2 <> "two\n"
    pt3 = "      "
    p3 = Prefix pt3
    l3 = rel 26 $ Lex.lex $ pt3 <> "three\n"
  in
    V 37
       Empty
      (Run p1 (Cat.singleton l1) l1 Empty p1)
      ((Rev . Cat.singleton $ Run p2 (Cat.singleton l2) l2 (Cat.singleton $ LayoutMismatch 13 p1 p2) p2) <>
       (Rev . Cat.singleton $ Run p3 (Cat.singleton l3) l3 (Cat.singleton $ LayoutMismatch 26 p2 p3) p3))

exampleI332E311 :: Text
exampleI332E311 =
  "       \t one\n\
  \ \t       two\n\
  \ \t    three\n\
  \"

resultI332E311 :: Layout
resultI332E311 =
  let
    pt1 = "       \t "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = " \t       "
    p2 = Prefix pt2
    l2 = rel 13 $ Lex.lex $ pt2 <> "two\n"
    pt3 = " \t    "
    p3 = Prefix pt3
    l3 = rel 26 $ Lex.lex $ pt3 <> "three\n"
  in
    V 37
       Empty
      (Run p1 (Cat.singleton l1) l1 Empty p1)
      ((Rev . Cat.singleton $ Run p2 (Cat.singleton l2) l2 (Cat.singleton $ LayoutMismatch 13 p1 p2) p2) <>
       (Rev . Cat.singleton $ Run p3 (Cat.singleton l3) l3 Empty p3))

exampleI332E312 :: Text
exampleI332E312 =
  "       \t one\n\
  \ \t       two\n\
  \    \t three\n\
  \"

resultI332E312 :: Layout
resultI332E312 =
  let
    pt1 = "       \t "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = " \t       "
    p2 = Prefix pt2
    l2 = rel 13 $ Lex.lex $ pt2 <> "two\n"
    pt3 = "    \t "
    p3 = Prefix pt3
    l3 = rel 26 $ Lex.lex $ pt3 <> "three\n"
  in
    V 37
       Empty
      (Run p1 (Cat.singleton l1) l1 Empty p1)
      ((Rev . Cat.singleton $ Run p2 (Cat.singleton l2) l2 (Cat.singleton $ LayoutMismatch 13 p1 p2) p2) <>
       (Rev . Cat.singleton $ Run p3 (Cat.singleton l3) l3 (Cat.singleton $ LayoutMismatch 26 p2 p3) p3))

exampleI332E320 :: Text
exampleI332E320 =
  "       \t one\n\
  \    \t    two\n\
  \      three\n\
  \"

resultI332E320 :: Layout
resultI332E320 =
  let
    pt1 = "       \t "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = "    \t    "
    p2 = Prefix pt2
    l2 = rel 13 $ Lex.lex $ pt2 <> "two\n"
    pt3 = "      "
    p3 = Prefix pt3
    l3 = rel 26 $ Lex.lex $ pt3 <> "three\n"
  in
    V 37
       Empty
      (Run p1 (Cat.singleton l1) l1 Empty p1)
      ((Rev . Cat.singleton $ Run p2 (Cat.singleton l2) l2 (Cat.singleton $ LayoutMismatch 13 p1 p2) p2) <>
       (Rev . Cat.singleton $ Run p3 (Cat.singleton l3) l3 (Cat.singleton $ LayoutMismatch 26 p2 p3) p3))

exampleI332E321 :: Text
exampleI332E321 =
  "       \t one\n\
  \    \t    two\n\
  \ \t    three\n\
  \"

resultI332E321 :: Layout
resultI332E321 =
  let
    pt1 = "       \t "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = "    \t    "
    p2 = Prefix pt2
    l2 = rel 13 $ Lex.lex $ pt2 <> "two\n"
    pt3 = " \t    "
    p3 = Prefix pt3
    l3 = rel 26 $ Lex.lex $ pt3 <> "three\n"
  in
    V 37
       Empty
      (Run p1 (Cat.singleton l1) l1 Empty p1)
      ((Rev . Cat.singleton $ Run p2 (Cat.singleton l2) l2 (Cat.singleton $ LayoutMismatch 13 p1 p2) p2) <>
       (Rev . Cat.singleton $ Run p3 (Cat.singleton l3) l3 (Cat.singleton $ LayoutMismatch 26 p2 p3) p3))

exampleI332E322 :: Text
exampleI332E322 =
  "       \t one\n\
  \    \t    two\n\
  \    \t three\n\
  \"

resultI332E322 :: Layout
resultI332E322 =
  let
    pt1 = "       \t "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = "    \t    "
    p2 = Prefix pt2
    l2 = rel 13 $ Lex.lex $ pt2 <> "two\n"
    pt3 = "    \t "
    p3 = Prefix pt3
    l3 = rel 26 $ Lex.lex $ pt3 <> "three\n"
  in
    V 37
       Empty
      (Run p1 (Cat.singleton l1) l1 Empty p1)
      ((Rev . Cat.singleton $ Run p2 (Cat.singleton l2) l2 (Cat.singleton $ LayoutMismatch 13 p1 p2) p2) <>
       (Rev . Cat.singleton $ Run p3 (Cat.singleton l3) l3 Empty p3))

exampleI332E330 :: Text
exampleI332E330 =
  "       \t one\n\
  \       \t two\n\
  \      three\n\
  \"

resultI332E330 :: Layout
resultI332E330 =
  let
    pt1 = "       \t "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = "       \t "
    p2 = Prefix pt2
    l2 = rel 13 $ Lex.lex $ pt2 <> "two\n"
    pt3 = "      "
    p3 = Prefix pt3
    l3 = rel 26 $ Lex.lex $ pt3 <> "three\n"
  in
    V 37
      ((Cat.singleton $ Run p1 (Cat.singleton l1) l1 Empty p1) <>
       (Cat.singleton $ Run p2 (Cat.singleton l2) l2 Empty p2))
      (Run p3 (Cat.singleton l3) l3 Empty p3)
       Empty

exampleI332E331 :: Text
exampleI332E331 =
  "       \t one\n\
  \       \t two\n\
  \ \t    three\n\
  \"

resultI332E331 :: Layout
resultI332E331 =
  let
    pt1 = "       \t "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = "       \t "
    p2 = Prefix pt2
    l2 = rel 13 $ Lex.lex $ pt2 <> "two\n"
    pt3 = " \t    "
    p3 = Prefix pt3
    l3 = rel 26 $ Lex.lex $ pt3 <> "three\n"
  in
    V 37
       Empty
      (Run p1 (Cat.singleton l1) l1 Empty p1)
      ((Rev . Cat.singleton $ Run p2 (Cat.singleton l2) l2 Empty p2) <>
       (Rev . Cat.singleton $ Run p3 (Cat.singleton l3) l3 (Cat.singleton $ LayoutMismatch 26 p2 p3) p3))

exampleI332E332 :: Text
exampleI332E332 =
  "       \t one\n\
  \       \t two\n\
  \    \t three\n\
  \"

resultI332E332 :: Layout
resultI332E332 =
  let
    pt1 = "       \t "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = "       \t "
    p2 = Prefix pt2
    l2 = rel 13 $ Lex.lex $ pt2 <> "two\n"
    pt3 = "    \t "
    p3 = Prefix pt3
    l3 = rel 26 $ Lex.lex $ pt3 <> "three\n"
  in
    V 37
       Empty
      (Run p1 (Cat.singleton l1) l1 Empty p1)
      ((Rev . Cat.singleton $ Run p2 (Cat.singleton l2) l2 Empty p2) <>
       (Rev . Cat.singleton $ Run p3 (Cat.singleton l3) l3 (Cat.singleton $ LayoutMismatch 26 p2 p3) p3))

exampleI333E000 :: Text
exampleI333E000 =
  "         one\n\
  \         two\n\
  \         three\n\
  \"

resultI333E000 :: Layout
resultI333E000 =
  let
    pt1 = "         "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = "         "
    p2 = Prefix pt2
    l2 = rel 13 $ Lex.lex $ pt2 <> "two\n"
    pt3 = "         "
    p3 = Prefix pt3
    l3 = rel 26 $ Lex.lex $ pt3 <> "three\n"
  in
    V 40
       Empty
      (Run p1 (Cat.singleton l1) l1 Empty p1)
      ((Rev . Cat.singleton $ Run p2 (Cat.singleton l2) l2 Empty p2) <>
       (Rev . Cat.singleton $ Run p3 (Cat.singleton l3) l3 Empty p3))

exampleI333E001 :: Text
exampleI333E001 =
  "         one\n\
  \         two\n\
  \ \t       three\n\
  \"

resultI333E001 :: Layout
resultI333E001 =
  let
    pt1 = "         "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = "         "
    p2 = Prefix pt2
    l2 = rel 13 $ Lex.lex $ pt2 <> "two\n"
    pt3 = " \t       "
    p3 = Prefix pt3
    l3 = rel 26 $ Lex.lex $ pt3 <> "three\n"
  in
    V 40
       Empty
      (Run p1 (Cat.singleton l1) l1 Empty p1)
      ((Rev . Cat.singleton $ Run p2 (Cat.singleton l2) l2 Empty p2) <>
       (Rev . Cat.singleton $ Run p3 (Cat.singleton l3) l3 (Cat.singleton $ LayoutMismatch 26 p2 p3) p3))

exampleI333E002 :: Text
exampleI333E002 =
  "         one\n\
  \         two\n\
  \    \t    three\n\
  \"

resultI333E002 :: Layout
resultI333E002 =
  let
    pt1 = "         "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = "         "
    p2 = Prefix pt2
    l2 = rel 13 $ Lex.lex $ pt2 <> "two\n"
    pt3 = "    \t    "
    p3 = Prefix pt3
    l3 = rel 26 $ Lex.lex $ pt3 <> "three\n"
  in
    V 40
       Empty
      (Run p1 (Cat.singleton l1) l1 Empty p1)
      ((Rev . Cat.singleton $ Run p2 (Cat.singleton l2) l2 Empty p2) <>
       (Rev . Cat.singleton $ Run p3 (Cat.singleton l3) l3 (Cat.singleton $ LayoutMismatch 26 p2 p3) p3))

exampleI333E003 :: Text
exampleI333E003 =
  "         one\n\
  \         two\n\
  \       \t three\n\
  \"

resultI333E003 :: Layout
resultI333E003 =
  let
    pt1 = "         "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = "         "
    p2 = Prefix pt2
    l2 = rel 13 $ Lex.lex $ pt2 <> "two\n"
    pt3 = "       \t "
    p3 = Prefix pt3
    l3 = rel 26 $ Lex.lex $ pt3 <> "three\n"
  in
    V 40
       Empty
      (Run p1 (Cat.singleton l1) l1 Empty p1)
      ((Rev . Cat.singleton $ Run p2 (Cat.singleton l2) l2 Empty p2) <>
       (Rev . Cat.singleton $ Run p3 (Cat.singleton l3) l3 (Cat.singleton $ LayoutMismatch 26 p2 p3) p3))

exampleI333E010 :: Text
exampleI333E010 =
  "         one\n\
  \ \t       two\n\
  \         three\n\
  \"

resultI333E010 :: Layout
resultI333E010 =
  let
    pt1 = "         "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = " \t       "
    p2 = Prefix pt2
    l2 = rel 13 $ Lex.lex $ pt2 <> "two\n"
    pt3 = "         "
    p3 = Prefix pt3
    l3 = rel 26 $ Lex.lex $ pt3 <> "three\n"
  in
    V 40
       Empty
      (Run p1 (Cat.singleton l1) l1 Empty p1)
      ((Rev . Cat.singleton $ Run p2 (Cat.singleton l2) l2 (Cat.singleton $ LayoutMismatch 13 p1 p2) p2) <>
       (Rev . Cat.singleton $ Run p3 (Cat.singleton l3) l3 (Cat.singleton $ LayoutMismatch 26 p2 p3) p3))

exampleI333E011 :: Text
exampleI333E011 =
  "         one\n\
  \ \t       two\n\
  \ \t       three\n\
  \"

resultI333E011 :: Layout
resultI333E011 =
  let
    pt1 = "         "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = " \t       "
    p2 = Prefix pt2
    l2 = rel 13 $ Lex.lex $ pt2 <> "two\n"
    pt3 = " \t       "
    p3 = Prefix pt3
    l3 = rel 26 $ Lex.lex $ pt3 <> "three\n"
  in
    V 40
       Empty
      (Run p1 (Cat.singleton l1) l1 Empty p1)
      ((Rev . Cat.singleton $ Run p2 (Cat.singleton l2) l2 (Cat.singleton $ LayoutMismatch 13 p1 p2) p2) <>
       (Rev . Cat.singleton $ Run p3 (Cat.singleton l3) l3 Empty p3))

exampleI333E012 :: Text
exampleI333E012 =
  "         one\n\
  \ \t       two\n\
  \    \t    three\n\
  \"

resultI333E012 :: Layout
resultI333E012 =
  let
    pt1 = "         "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = " \t       "
    p2 = Prefix pt2
    l2 = rel 13 $ Lex.lex $ pt2 <> "two\n"
    pt3 = "    \t    "
    p3 = Prefix pt3
    l3 = rel 26 $ Lex.lex $ pt3 <> "three\n"
  in
    V 40
       Empty
      (Run p1 (Cat.singleton l1) l1 Empty p1)
      ((Rev . Cat.singleton $ Run p2 (Cat.singleton l2) l2 (Cat.singleton $ LayoutMismatch 13 p1 p2) p2) <>
       (Rev . Cat.singleton $ Run p3 (Cat.singleton l3) l3 (Cat.singleton $ LayoutMismatch 26 p2 p3) p3))

exampleI333E013 :: Text
exampleI333E013 =
  "         one\n\
  \ \t       two\n\
  \       \t three\n\
  \"

resultI333E013 :: Layout
resultI333E013 =
  let
    pt1 = "         "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = " \t       "
    p2 = Prefix pt2
    l2 = rel 13 $ Lex.lex $ pt2 <> "two\n"
    pt3 = "       \t "
    p3 = Prefix pt3
    l3 = rel 26 $ Lex.lex $ pt3 <> "three\n"
  in
    V 40
       Empty
      (Run p1 (Cat.singleton l1) l1 Empty p1)
      ((Rev . Cat.singleton $ Run p2 (Cat.singleton l2) l2 (Cat.singleton $ LayoutMismatch 13 p1 p2) p2) <>
       (Rev . Cat.singleton $ Run p3 (Cat.singleton l3) l3 (Cat.singleton $ LayoutMismatch 26 p2 p3) p3))

exampleI333E020 :: Text
exampleI333E020 =
  "         one\n\
  \    \t    two\n\
  \         three\n\
  \"

resultI333E020 :: Layout
resultI333E020 =
  let
    pt1 = "         "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = "    \t    "
    p2 = Prefix pt2
    l2 = rel 13 $ Lex.lex $ pt2 <> "two\n"
    pt3 = "         "
    p3 = Prefix pt3
    l3 = rel 26 $ Lex.lex $ pt3 <> "three\n"
  in
    V 40
       Empty
      (Run p1 (Cat.singleton l1) l1 Empty p1)
      ((Rev . Cat.singleton $ Run p2 (Cat.singleton l2) l2 (Cat.singleton $ LayoutMismatch 13 p1 p2) p2) <>
       (Rev . Cat.singleton $ Run p3 (Cat.singleton l3) l3 (Cat.singleton $ LayoutMismatch 26 p2 p3) p3))

exampleI333E021 :: Text
exampleI333E021 =
  "         one\n\
  \    \t    two\n\
  \ \t       three\n\
  \"

resultI333E021 :: Layout
resultI333E021 =
  let
    pt1 = "         "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = "    \t    "
    p2 = Prefix pt2
    l2 = rel 13 $ Lex.lex $ pt2 <> "two\n"
    pt3 = " \t       "
    p3 = Prefix pt3
    l3 = rel 26 $ Lex.lex $ pt3 <> "three\n"
  in
    V 40
       Empty
      (Run p1 (Cat.singleton l1) l1 Empty p1)
      ((Rev . Cat.singleton $ Run p2 (Cat.singleton l2) l2 (Cat.singleton $ LayoutMismatch 13 p1 p2) p2) <>
       (Rev . Cat.singleton $ Run p3 (Cat.singleton l3) l3 (Cat.singleton $ LayoutMismatch 26 p2 p3) p3))

exampleI333E022 :: Text
exampleI333E022 =
  "         one\n\
  \    \t    two\n\
  \    \t    three\n\
  \"

resultI333E022 :: Layout
resultI333E022 =
  let
    pt1 = "         "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = "    \t    "
    p2 = Prefix pt2
    l2 = rel 13 $ Lex.lex $ pt2 <> "two\n"
    pt3 = "    \t    "
    p3 = Prefix pt3
    l3 = rel 26 $ Lex.lex $ pt3 <> "three\n"
  in
    V 40
       Empty
      (Run p1 (Cat.singleton l1) l1 Empty p1)
      ((Rev . Cat.singleton $ Run p2 (Cat.singleton l2) l2 (Cat.singleton $ LayoutMismatch 13 p1 p2) p2) <>
       (Rev . Cat.singleton $ Run p3 (Cat.singleton l3) l3 Empty p3))

exampleI333E023 :: Text
exampleI333E023 =
  "         one\n\
  \    \t    two\n\
  \       \t three\n\
  \"

resultI333E023 :: Layout
resultI333E023 =
  let
    pt1 = "         "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = "    \t    "
    p2 = Prefix pt2
    l2 = rel 13 $ Lex.lex $ pt2 <> "two\n"
    pt3 = "       \t "
    p3 = Prefix pt3
    l3 = rel 26 $ Lex.lex $ pt3 <> "three\n"
  in
    V 40
       Empty
      (Run p1 (Cat.singleton l1) l1 Empty p1)
      ((Rev . Cat.singleton $ Run p2 (Cat.singleton l2) l2 (Cat.singleton $ LayoutMismatch 13 p1 p2) p2) <>
       (Rev . Cat.singleton $ Run p3 (Cat.singleton l3) l3 (Cat.singleton $ LayoutMismatch 26 p2 p3) p3))

exampleI333E030 :: Text
exampleI333E030 =
  "         one\n\
  \       \t two\n\
  \         three\n\
  \"

resultI333E030 :: Layout
resultI333E030 =
  let
    pt1 = "         "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = "       \t "
    p2 = Prefix pt2
    l2 = rel 13 $ Lex.lex $ pt2 <> "two\n"
    pt3 = "         "
    p3 = Prefix pt3
    l3 = rel 26 $ Lex.lex $ pt3 <> "three\n"
  in
    V 40
       Empty
      (Run p1 (Cat.singleton l1) l1 Empty p1)
      ((Rev . Cat.singleton $ Run p2 (Cat.singleton l2) l2 (Cat.singleton $ LayoutMismatch 13 p1 p2) p2) <>
       (Rev . Cat.singleton $ Run p3 (Cat.singleton l3) l3 (Cat.singleton $ LayoutMismatch 26 p2 p3) p3))

exampleI333E031 :: Text
exampleI333E031 =
  "         one\n\
  \       \t two\n\
  \ \t       three\n\
  \"

resultI333E031 :: Layout
resultI333E031 =
  let
    pt1 = "         "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = "       \t "
    p2 = Prefix pt2
    l2 = rel 13 $ Lex.lex $ pt2 <> "two\n"
    pt3 = " \t       "
    p3 = Prefix pt3
    l3 = rel 26 $ Lex.lex $ pt3 <> "three\n"
  in
    V 40
       Empty
      (Run p1 (Cat.singleton l1) l1 Empty p1)
      ((Rev . Cat.singleton $ Run p2 (Cat.singleton l2) l2 (Cat.singleton $ LayoutMismatch 13 p1 p2) p2) <>
       (Rev . Cat.singleton $ Run p3 (Cat.singleton l3) l3 (Cat.singleton $ LayoutMismatch 26 p2 p3) p3))

exampleI333E032 :: Text
exampleI333E032 =
  "         one\n\
  \       \t two\n\
  \    \t    three\n\
  \"

resultI333E032 :: Layout
resultI333E032 =
  let
    pt1 = "         "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = "       \t "
    p2 = Prefix pt2
    l2 = rel 13 $ Lex.lex $ pt2 <> "two\n"
    pt3 = "    \t    "
    p3 = Prefix pt3
    l3 = rel 26 $ Lex.lex $ pt3 <> "three\n"
  in
    V 40
       Empty
      (Run p1 (Cat.singleton l1) l1 Empty p1)
      ((Rev . Cat.singleton $ Run p2 (Cat.singleton l2) l2 (Cat.singleton $ LayoutMismatch 13 p1 p2) p2) <>
       (Rev . Cat.singleton $ Run p3 (Cat.singleton l3) l3 (Cat.singleton $ LayoutMismatch 26 p2 p3) p3))

exampleI333E033 :: Text
exampleI333E033 =
  "         one\n\
  \       \t two\n\
  \       \t three\n\
  \"

resultI333E033 :: Layout
resultI333E033 =
  let
    pt1 = "         "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = "       \t "
    p2 = Prefix pt2
    l2 = rel 13 $ Lex.lex $ pt2 <> "two\n"
    pt3 = "       \t "
    p3 = Prefix pt3
    l3 = rel 26 $ Lex.lex $ pt3 <> "three\n"
  in
    V 40
       Empty
      (Run p1 (Cat.singleton l1) l1 Empty p1)
      ((Rev . Cat.singleton $ Run p2 (Cat.singleton l2) l2 (Cat.singleton $ LayoutMismatch 13 p1 p2) p2) <>
       (Rev . Cat.singleton $ Run p3 (Cat.singleton l3) l3 Empty p3))

exampleI333E100 :: Text
exampleI333E100 =
  " \t       one\n\
  \         two\n\
  \         three\n\
  \"

resultI333E100 :: Layout
resultI333E100 =
  let
    pt1 = " \t       "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = "         "
    p2 = Prefix pt2
    l2 = rel 13 $ Lex.lex $ pt2 <> "two\n"
    pt3 = "         "
    p3 = Prefix pt3
    l3 = rel 26 $ Lex.lex $ pt3 <> "three\n"
  in
    V 40
       Empty
      (Run p1 (Cat.singleton l1) l1 Empty p1)
      ((Rev . Cat.singleton $ Run p2 (Cat.singleton l2) l2 (Cat.singleton $ LayoutMismatch 13 p1 p2) p2) <>
       (Rev . Cat.singleton $ Run p3 (Cat.singleton l3) l3 Empty p3))

exampleI333E101 :: Text
exampleI333E101 =
  " \t       one\n\
  \         two\n\
  \ \t       three\n\
  \"

resultI333E101 :: Layout
resultI333E101 =
  let
    pt1 = " \t       "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = "         "
    p2 = Prefix pt2
    l2 = rel 13 $ Lex.lex $ pt2 <> "two\n"
    pt3 = " \t       "
    p3 = Prefix pt3
    l3 = rel 26 $ Lex.lex $ pt3 <> "three\n"
  in
    V 40
       Empty
      (Run p1 (Cat.singleton l1) l1 Empty p1)
      ((Rev . Cat.singleton $ Run p2 (Cat.singleton l2) l2 (Cat.singleton $ LayoutMismatch 13 p1 p2) p2) <>
       (Rev . Cat.singleton $ Run p3 (Cat.singleton l3) l3 (Cat.singleton $ LayoutMismatch 26 p2 p3) p3))

exampleI333E102 :: Text
exampleI333E102 =
  " \t       one\n\
  \         two\n\
  \    \t    three\n\
  \"

resultI333E102 :: Layout
resultI333E102 =
  let
    pt1 = " \t       "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = "         "
    p2 = Prefix pt2
    l2 = rel 13 $ Lex.lex $ pt2 <> "two\n"
    pt3 = "    \t    "
    p3 = Prefix pt3
    l3 = rel 26 $ Lex.lex $ pt3 <> "three\n"
  in
    V 40
       Empty
      (Run p1 (Cat.singleton l1) l1 Empty p1)
      ((Rev . Cat.singleton $ Run p2 (Cat.singleton l2) l2 (Cat.singleton $ LayoutMismatch 13 p1 p2) p2) <>
       (Rev . Cat.singleton $ Run p3 (Cat.singleton l3) l3 (Cat.singleton $ LayoutMismatch 26 p2 p3) p3))

exampleI333E103 :: Text
exampleI333E103 =
  " \t       one\n\
  \         two\n\
  \       \t three\n\
  \"

resultI333E103 :: Layout
resultI333E103 =
  let
    pt1 = " \t       "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = "         "
    p2 = Prefix pt2
    l2 = rel 13 $ Lex.lex $ pt2 <> "two\n"
    pt3 = "       \t "
    p3 = Prefix pt3
    l3 = rel 26 $ Lex.lex $ pt3 <> "three\n"
  in
    V 40
       Empty
      (Run p1 (Cat.singleton l1) l1 Empty p1)
      ((Rev . Cat.singleton $ Run p2 (Cat.singleton l2) l2 (Cat.singleton $ LayoutMismatch 13 p1 p2) p2) <>
       (Rev . Cat.singleton $ Run p3 (Cat.singleton l3) l3 (Cat.singleton $ LayoutMismatch 26 p2 p3) p3))

exampleI333E110 :: Text
exampleI333E110 =
  " \t       one\n\
  \ \t       two\n\
  \         three\n\
  \"

resultI333E110 :: Layout
resultI333E110 =
  let
    pt1 = " \t       "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = " \t       "
    p2 = Prefix pt2
    l2 = rel 13 $ Lex.lex $ pt2 <> "two\n"
    pt3 = "         "
    p3 = Prefix pt3
    l3 = rel 26 $ Lex.lex $ pt3 <> "three\n"
  in
    V 40
       Empty
      (Run p1 (Cat.singleton l1) l1 Empty p1)
      ((Rev . Cat.singleton $ Run p2 (Cat.singleton l2) l2 Empty p2) <>
       (Rev . Cat.singleton $ Run p3 (Cat.singleton l3) l3 (Cat.singleton $ LayoutMismatch 26 p2 p3) p3))

exampleI333E111 :: Text
exampleI333E111 =
  " \t       one\n\
  \ \t       two\n\
  \ \t       three\n\
  \"

resultI333E111 :: Layout
resultI333E111 =
  let
    pt1 = " \t       "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = " \t       "
    p2 = Prefix pt2
    l2 = rel 13 $ Lex.lex $ pt2 <> "two\n"
    pt3 = " \t       "
    p3 = Prefix pt3
    l3 = rel 26 $ Lex.lex $ pt3 <> "three\n"
  in
    V 40
       Empty
      (Run p1 (Cat.singleton l1) l1 Empty p1)
      ((Rev . Cat.singleton $ Run p2 (Cat.singleton l2) l2 Empty p2) <>
       (Rev . Cat.singleton $ Run p3 (Cat.singleton l3) l3 Empty p3))

exampleI333E112 :: Text
exampleI333E112 =
  " \t       one\n\
  \ \t       two\n\
  \    \t    three\n\
  \"

resultI333E112 :: Layout
resultI333E112 =
  let
    pt1 = " \t       "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = " \t       "
    p2 = Prefix pt2
    l2 = rel 13 $ Lex.lex $ pt2 <> "two\n"
    pt3 = "    \t    "
    p3 = Prefix pt3
    l3 = rel 26 $ Lex.lex $ pt3 <> "three\n"
  in
    V 40
       Empty
      (Run p1 (Cat.singleton l1) l1 Empty p1)
      ((Rev . Cat.singleton $ Run p2 (Cat.singleton l2) l2 Empty p2) <>
       (Rev . Cat.singleton $ Run p3 (Cat.singleton l3) l3 (Cat.singleton $ LayoutMismatch 26 p2 p3) p3))

exampleI333E113 :: Text
exampleI333E113 =
  " \t       one\n\
  \ \t       two\n\
  \       \t three\n\
  \"

resultI333E113 :: Layout
resultI333E113 =
  let
    pt1 = " \t       "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = " \t       "
    p2 = Prefix pt2
    l2 = rel 13 $ Lex.lex $ pt2 <> "two\n"
    pt3 = "       \t "
    p3 = Prefix pt3
    l3 = rel 26 $ Lex.lex $ pt3 <> "three\n"
  in
    V 40
       Empty
      (Run p1 (Cat.singleton l1) l1 Empty p1)
      ((Rev . Cat.singleton $ Run p2 (Cat.singleton l2) l2 Empty p2) <>
       (Rev . Cat.singleton $ Run p3 (Cat.singleton l3) l3 (Cat.singleton $ LayoutMismatch 26 p2 p3) p3))

exampleI333E120 :: Text
exampleI333E120 =
  " \t       one\n\
  \    \t    two\n\
  \         three\n\
  \"

resultI333E120 :: Layout
resultI333E120 =
  let
    pt1 = " \t       "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = "    \t    "
    p2 = Prefix pt2
    l2 = rel 13 $ Lex.lex $ pt2 <> "two\n"
    pt3 = "         "
    p3 = Prefix pt3
    l3 = rel 26 $ Lex.lex $ pt3 <> "three\n"
  in
    V 40
       Empty
      (Run p1 (Cat.singleton l1) l1 Empty p1)
      ((Rev . Cat.singleton $ Run p2 (Cat.singleton l2) l2 (Cat.singleton $ LayoutMismatch 13 p1 p2) p2) <>
       (Rev . Cat.singleton $ Run p3 (Cat.singleton l3) l3 (Cat.singleton $ LayoutMismatch 26 p2 p3) p3))

exampleI333E121 :: Text
exampleI333E121 =
  " \t       one\n\
  \    \t    two\n\
  \ \t       three\n\
  \"

resultI333E121 :: Layout
resultI333E121 =
  let
    pt1 = " \t       "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = "    \t    "
    p2 = Prefix pt2
    l2 = rel 13 $ Lex.lex $ pt2 <> "two\n"
    pt3 = " \t       "
    p3 = Prefix pt3
    l3 = rel 26 $ Lex.lex $ pt3 <> "three\n"
  in
    V 40
       Empty
      (Run p1 (Cat.singleton l1) l1 Empty p1)
      ((Rev . Cat.singleton $ Run p2 (Cat.singleton l2) l2 (Cat.singleton $ LayoutMismatch 13 p1 p2) p2) <>
       (Rev . Cat.singleton $ Run p3 (Cat.singleton l3) l3 (Cat.singleton $ LayoutMismatch 26 p2 p3) p3))

exampleI333E122 :: Text
exampleI333E122 =
  " \t       one\n\
  \    \t    two\n\
  \    \t    three\n\
  \"

resultI333E122 :: Layout
resultI333E122 =
  let
    pt1 = " \t       "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = "    \t    "
    p2 = Prefix pt2
    l2 = rel 13 $ Lex.lex $ pt2 <> "two\n"
    pt3 = "    \t    "
    p3 = Prefix pt3
    l3 = rel 26 $ Lex.lex $ pt3 <> "three\n"
  in
    V 40
       Empty
      (Run p1 (Cat.singleton l1) l1 Empty p1)
      ((Rev . Cat.singleton $ Run p2 (Cat.singleton l2) l2 (Cat.singleton $ LayoutMismatch 13 p1 p2) p2) <>
       (Rev . Cat.singleton $ Run p3 (Cat.singleton l3) l3 Empty p3))

exampleI333E123 :: Text
exampleI333E123 =
  " \t       one\n\
  \    \t    two\n\
  \       \t three\n\
  \"

resultI333E123 :: Layout
resultI333E123 =
  let
    pt1 = " \t       "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = "    \t    "
    p2 = Prefix pt2
    l2 = rel 13 $ Lex.lex $ pt2 <> "two\n"
    pt3 = "       \t "
    p3 = Prefix pt3
    l3 = rel 26 $ Lex.lex $ pt3 <> "three\n"
  in
    V 40
       Empty
      (Run p1 (Cat.singleton l1) l1 Empty p1)
      ((Rev . Cat.singleton $ Run p2 (Cat.singleton l2) l2 (Cat.singleton $ LayoutMismatch 13 p1 p2) p2) <>
       (Rev . Cat.singleton $ Run p3 (Cat.singleton l3) l3 (Cat.singleton $ LayoutMismatch 26 p2 p3) p3))

exampleI333E130 :: Text
exampleI333E130 =
  " \t       one\n\
  \       \t two\n\
  \         three\n\
  \"

resultI333E130 :: Layout
resultI333E130 =
  let
    pt1 = " \t       "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = "       \t "
    p2 = Prefix pt2
    l2 = rel 13 $ Lex.lex $ pt2 <> "two\n"
    pt3 = "         "
    p3 = Prefix pt3
    l3 = rel 26 $ Lex.lex $ pt3 <> "three\n"
  in
    V 40
       Empty
      (Run p1 (Cat.singleton l1) l1 Empty p1)
      ((Rev . Cat.singleton $ Run p2 (Cat.singleton l2) l2 (Cat.singleton $ LayoutMismatch 13 p1 p2) p2) <>
       (Rev . Cat.singleton $ Run p3 (Cat.singleton l3) l3 (Cat.singleton $ LayoutMismatch 26 p2 p3) p3))

exampleI333E131 :: Text
exampleI333E131 =
  " \t       one\n\
  \       \t two\n\
  \ \t       three\n\
  \"

resultI333E131 :: Layout
resultI333E131 =
  let
    pt1 = " \t       "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = "       \t "
    p2 = Prefix pt2
    l2 = rel 13 $ Lex.lex $ pt2 <> "two\n"
    pt3 = " \t       "
    p3 = Prefix pt3
    l3 = rel 26 $ Lex.lex $ pt3 <> "three\n"
  in
    V 40
       Empty
      (Run p1 (Cat.singleton l1) l1 Empty p1)
      ((Rev . Cat.singleton $ Run p2 (Cat.singleton l2) l2 (Cat.singleton $ LayoutMismatch 13 p1 p2) p2) <>
       (Rev . Cat.singleton $ Run p3 (Cat.singleton l3) l3 (Cat.singleton $ LayoutMismatch 26 p2 p3) p3))

exampleI333E132 :: Text
exampleI333E132 =
  " \t       one\n\
  \       \t two\n\
  \    \t    three\n\
  \"

resultI333E132 :: Layout
resultI333E132 =
  let
    pt1 = " \t       "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = "       \t "
    p2 = Prefix pt2
    l2 = rel 13 $ Lex.lex $ pt2 <> "two\n"
    pt3 = "    \t    "
    p3 = Prefix pt3
    l3 = rel 26 $ Lex.lex $ pt3 <> "three\n"
  in
    V 40
       Empty
      (Run p1 (Cat.singleton l1) l1 Empty p1)
      ((Rev . Cat.singleton $ Run p2 (Cat.singleton l2) l2 (Cat.singleton $ LayoutMismatch 13 p1 p2) p2) <>
       (Rev . Cat.singleton $ Run p3 (Cat.singleton l3) l3 (Cat.singleton $ LayoutMismatch 26 p2 p3) p3))

exampleI333E133 :: Text
exampleI333E133 =
  " \t       one\n\
  \       \t two\n\
  \       \t three\n\
  \"

resultI333E133 :: Layout
resultI333E133 =
  let
    pt1 = " \t       "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = "       \t "
    p2 = Prefix pt2
    l2 = rel 13 $ Lex.lex $ pt2 <> "two\n"
    pt3 = "       \t "
    p3 = Prefix pt3
    l3 = rel 26 $ Lex.lex $ pt3 <> "three\n"
  in
    V 40
       Empty
      (Run p1 (Cat.singleton l1) l1 Empty p1)
      ((Rev . Cat.singleton $ Run p2 (Cat.singleton l2) l2 (Cat.singleton $ LayoutMismatch 13 p1 p2) p2) <>
       (Rev . Cat.singleton $ Run p3 (Cat.singleton l3) l3 Empty p3))

exampleI333E200 :: Text
exampleI333E200 =
  "    \t    one\n\
  \         two\n\
  \         three\n\
  \"

resultI333E200 :: Layout
resultI333E200 =
  let
    pt1 = "    \t    "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = "         "
    p2 = Prefix pt2
    l2 = rel 13 $ Lex.lex $ pt2 <> "two\n"
    pt3 = "         "
    p3 = Prefix pt3
    l3 = rel 26 $ Lex.lex $ pt3 <> "three\n"
  in
    V 40
       Empty
      (Run p1 (Cat.singleton l1) l1 Empty p1)
      ((Rev . Cat.singleton $ Run p2 (Cat.singleton l2) l2 (Cat.singleton $ LayoutMismatch 13 p1 p2) p2) <>
       (Rev . Cat.singleton $ Run p3 (Cat.singleton l3) l3 Empty p3))

exampleI333E201 :: Text
exampleI333E201 =
  "    \t    one\n\
  \         two\n\
  \ \t       three\n\
  \"

resultI333E201 :: Layout
resultI333E201 =
  let
    pt1 = "    \t    "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = "         "
    p2 = Prefix pt2
    l2 = rel 13 $ Lex.lex $ pt2 <> "two\n"
    pt3 = " \t       "
    p3 = Prefix pt3
    l3 = rel 26 $ Lex.lex $ pt3 <> "three\n"
  in
    V 40
       Empty
      (Run p1 (Cat.singleton l1) l1 Empty p1)
      ((Rev . Cat.singleton $ Run p2 (Cat.singleton l2) l2 (Cat.singleton $ LayoutMismatch 13 p1 p2) p2) <>
       (Rev . Cat.singleton $ Run p3 (Cat.singleton l3) l3 (Cat.singleton $ LayoutMismatch 26 p2 p3) p3))

exampleI333E202 :: Text
exampleI333E202 =
  "    \t    one\n\
  \         two\n\
  \    \t    three\n\
  \"

resultI333E202 :: Layout
resultI333E202 =
  let
    pt1 = "    \t    "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = "         "
    p2 = Prefix pt2
    l2 = rel 13 $ Lex.lex $ pt2 <> "two\n"
    pt3 = "    \t    "
    p3 = Prefix pt3
    l3 = rel 26 $ Lex.lex $ pt3 <> "three\n"
  in
    V 40
       Empty
      (Run p1 (Cat.singleton l1) l1 Empty p1)
      ((Rev . Cat.singleton $ Run p2 (Cat.singleton l2) l2 (Cat.singleton $ LayoutMismatch 13 p1 p2) p2) <>
       (Rev . Cat.singleton $ Run p3 (Cat.singleton l3) l3 (Cat.singleton $ LayoutMismatch 26 p2 p3) p3))

exampleI333E203 :: Text
exampleI333E203 =
  "    \t    one\n\
  \         two\n\
  \       \t three\n\
  \"

resultI333E203 :: Layout
resultI333E203 =
  let
    pt1 = "    \t    "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = "         "
    p2 = Prefix pt2
    l2 = rel 13 $ Lex.lex $ pt2 <> "two\n"
    pt3 = "       \t "
    p3 = Prefix pt3
    l3 = rel 26 $ Lex.lex $ pt3 <> "three\n"
  in
    V 40
       Empty
      (Run p1 (Cat.singleton l1) l1 Empty p1)
      ((Rev . Cat.singleton $ Run p2 (Cat.singleton l2) l2 (Cat.singleton $ LayoutMismatch 13 p1 p2) p2) <>
       (Rev . Cat.singleton $ Run p3 (Cat.singleton l3) l3 (Cat.singleton $ LayoutMismatch 26 p2 p3) p3))

exampleI333E210 :: Text
exampleI333E210 =
  "    \t    one\n\
  \ \t       two\n\
  \         three\n\
  \"

resultI333E210 :: Layout
resultI333E210 =
  let
    pt1 = "    \t    "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = " \t       "
    p2 = Prefix pt2
    l2 = rel 13 $ Lex.lex $ pt2 <> "two\n"
    pt3 = "         "
    p3 = Prefix pt3
    l3 = rel 26 $ Lex.lex $ pt3 <> "three\n"
  in
    V 40
       Empty
      (Run p1 (Cat.singleton l1) l1 Empty p1)
      ((Rev . Cat.singleton $ Run p2 (Cat.singleton l2) l2 (Cat.singleton $ LayoutMismatch 13 p1 p2) p2) <>
       (Rev . Cat.singleton $ Run p3 (Cat.singleton l3) l3 (Cat.singleton $ LayoutMismatch 26 p2 p3) p3))

exampleI333E211 :: Text
exampleI333E211 =
  "    \t    one\n\
  \ \t       two\n\
  \ \t       three\n\
  \"

resultI333E211 :: Layout
resultI333E211 =
  let
    pt1 = "    \t    "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = " \t       "
    p2 = Prefix pt2
    l2 = rel 13 $ Lex.lex $ pt2 <> "two\n"
    pt3 = " \t       "
    p3 = Prefix pt3
    l3 = rel 26 $ Lex.lex $ pt3 <> "three\n"
  in
    V 40
       Empty
      (Run p1 (Cat.singleton l1) l1 Empty p1)
      ((Rev . Cat.singleton $ Run p2 (Cat.singleton l2) l2 (Cat.singleton $ LayoutMismatch 13 p1 p2) p2) <>
       (Rev . Cat.singleton $ Run p3 (Cat.singleton l3) l3 Empty p3))

exampleI333E212 :: Text
exampleI333E212 =
  "    \t    one\n\
  \ \t       two\n\
  \    \t    three\n\
  \"

resultI333E212 :: Layout
resultI333E212 =
  let
    pt1 = "    \t    "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = " \t       "
    p2 = Prefix pt2
    l2 = rel 13 $ Lex.lex $ pt2 <> "two\n"
    pt3 = "    \t    "
    p3 = Prefix pt3
    l3 = rel 26 $ Lex.lex $ pt3 <> "three\n"
  in
    V 40
       Empty
      (Run p1 (Cat.singleton l1) l1 Empty p1)
      ((Rev . Cat.singleton $ Run p2 (Cat.singleton l2) l2 (Cat.singleton $ LayoutMismatch 13 p1 p2) p2) <>
       (Rev . Cat.singleton $ Run p3 (Cat.singleton l3) l3 (Cat.singleton $ LayoutMismatch 26 p2 p3) p3))

exampleI333E213 :: Text
exampleI333E213 =
  "    \t    one\n\
  \ \t       two\n\
  \       \t three\n\
  \"

resultI333E213 :: Layout
resultI333E213 =
  let
    pt1 = "    \t    "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = " \t       "
    p2 = Prefix pt2
    l2 = rel 13 $ Lex.lex $ pt2 <> "two\n"
    pt3 = "       \t "
    p3 = Prefix pt3
    l3 = rel 26 $ Lex.lex $ pt3 <> "three\n"
  in
    V 40
       Empty
      (Run p1 (Cat.singleton l1) l1 Empty p1)
      ((Rev . Cat.singleton $ Run p2 (Cat.singleton l2) l2 (Cat.singleton $ LayoutMismatch 13 p1 p2) p2) <>
       (Rev . Cat.singleton $ Run p3 (Cat.singleton l3) l3 (Cat.singleton $ LayoutMismatch 26 p2 p3) p3))

exampleI333E220 :: Text
exampleI333E220 =
  "    \t    one\n\
  \    \t    two\n\
  \         three\n\
  \"

resultI333E220 :: Layout
resultI333E220 =
  let
    pt1 = "    \t    "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = "    \t    "
    p2 = Prefix pt2
    l2 = rel 13 $ Lex.lex $ pt2 <> "two\n"
    pt3 = "         "
    p3 = Prefix pt3
    l3 = rel 26 $ Lex.lex $ pt3 <> "three\n"
  in
    V 40
       Empty
      (Run p1 (Cat.singleton l1) l1 Empty p1)
      ((Rev . Cat.singleton $ Run p2 (Cat.singleton l2) l2 Empty p2) <>
       (Rev . Cat.singleton $ Run p3 (Cat.singleton l3) l3 (Cat.singleton $ LayoutMismatch 26 p2 p3) p3))

exampleI333E221 :: Text
exampleI333E221 =
  "    \t    one\n\
  \    \t    two\n\
  \ \t       three\n\
  \"

resultI333E221 :: Layout
resultI333E221 =
  let
    pt1 = "    \t    "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = "    \t    "
    p2 = Prefix pt2
    l2 = rel 13 $ Lex.lex $ pt2 <> "two\n"
    pt3 = " \t       "
    p3 = Prefix pt3
    l3 = rel 26 $ Lex.lex $ pt3 <> "three\n"
  in
    V 40
       Empty
      (Run p1 (Cat.singleton l1) l1 Empty p1)
      ((Rev . Cat.singleton $ Run p2 (Cat.singleton l2) l2 Empty p2) <>
       (Rev . Cat.singleton $ Run p3 (Cat.singleton l3) l3 (Cat.singleton $ LayoutMismatch 26 p2 p3) p3))

exampleI333E222 :: Text
exampleI333E222 =
  "    \t    one\n\
  \    \t    two\n\
  \    \t    three\n\
  \"

resultI333E222 :: Layout
resultI333E222 =
  let
    pt1 = "    \t    "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = "    \t    "
    p2 = Prefix pt2
    l2 = rel 13 $ Lex.lex $ pt2 <> "two\n"
    pt3 = "    \t    "
    p3 = Prefix pt3
    l3 = rel 26 $ Lex.lex $ pt3 <> "three\n"
  in
    V 40
       Empty
      (Run p1 (Cat.singleton l1) l1 Empty p1)
      ((Rev . Cat.singleton $ Run p2 (Cat.singleton l2) l2 Empty p2) <>
       (Rev . Cat.singleton $ Run p3 (Cat.singleton l3) l3 Empty p3))

exampleI333E223 :: Text
exampleI333E223 =
  "    \t    one\n\
  \    \t    two\n\
  \       \t three\n\
  \"

resultI333E223 :: Layout
resultI333E223 =
  let
    pt1 = "    \t    "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = "    \t    "
    p2 = Prefix pt2
    l2 = rel 13 $ Lex.lex $ pt2 <> "two\n"
    pt3 = "       \t "
    p3 = Prefix pt3
    l3 = rel 26 $ Lex.lex $ pt3 <> "three\n"
  in
    V 40
       Empty
      (Run p1 (Cat.singleton l1) l1 Empty p1)
      ((Rev . Cat.singleton $ Run p2 (Cat.singleton l2) l2 Empty p2) <>
       (Rev . Cat.singleton $ Run p3 (Cat.singleton l3) l3 (Cat.singleton $ LayoutMismatch 26 p2 p3) p3))

exampleI333E230 :: Text
exampleI333E230 =
  "    \t    one\n\
  \       \t two\n\
  \         three\n\
  \"

resultI333E230 :: Layout
resultI333E230 =
  let
    pt1 = "    \t    "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = "       \t "
    p2 = Prefix pt2
    l2 = rel 13 $ Lex.lex $ pt2 <> "two\n"
    pt3 = "         "
    p3 = Prefix pt3
    l3 = rel 26 $ Lex.lex $ pt3 <> "three\n"
  in
    V 40
       Empty
      (Run p1 (Cat.singleton l1) l1 Empty p1)
      ((Rev . Cat.singleton $ Run p2 (Cat.singleton l2) l2 (Cat.singleton $ LayoutMismatch 13 p1 p2) p2) <>
       (Rev . Cat.singleton $ Run p3 (Cat.singleton l3) l3 (Cat.singleton $ LayoutMismatch 26 p2 p3) p3))

exampleI333E231 :: Text
exampleI333E231 =
  "    \t    one\n\
  \       \t two\n\
  \ \t       three\n\
  \"

resultI333E231 :: Layout
resultI333E231 =
  let
    pt1 = "    \t    "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = "       \t "
    p2 = Prefix pt2
    l2 = rel 13 $ Lex.lex $ pt2 <> "two\n"
    pt3 = " \t       "
    p3 = Prefix pt3
    l3 = rel 26 $ Lex.lex $ pt3 <> "three\n"
  in
    V 40
       Empty
      (Run p1 (Cat.singleton l1) l1 Empty p1)
      ((Rev . Cat.singleton $ Run p2 (Cat.singleton l2) l2 (Cat.singleton $ LayoutMismatch 13 p1 p2) p2) <>
       (Rev . Cat.singleton $ Run p3 (Cat.singleton l3) l3 (Cat.singleton $ LayoutMismatch 26 p2 p3) p3))

exampleI333E232 :: Text
exampleI333E232 =
  "    \t    one\n\
  \       \t two\n\
  \    \t    three\n\
  \"

resultI333E232 :: Layout
resultI333E232 =
  let
    pt1 = "    \t    "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = "       \t "
    p2 = Prefix pt2
    l2 = rel 13 $ Lex.lex $ pt2 <> "two\n"
    pt3 = "    \t    "
    p3 = Prefix pt3
    l3 = rel 26 $ Lex.lex $ pt3 <> "three\n"
  in
    V 40
       Empty
      (Run p1 (Cat.singleton l1) l1 Empty p1)
      ((Rev . Cat.singleton $ Run p2 (Cat.singleton l2) l2 (Cat.singleton $ LayoutMismatch 13 p1 p2) p2) <>
       (Rev . Cat.singleton $ Run p3 (Cat.singleton l3) l3 (Cat.singleton $ LayoutMismatch 26 p2 p3) p3))

exampleI333E233 :: Text
exampleI333E233 =
  "    \t    one\n\
  \       \t two\n\
  \       \t three\n\
  \"

resultI333E233 :: Layout
resultI333E233 =
  let
    pt1 = "    \t    "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = "       \t "
    p2 = Prefix pt2
    l2 = rel 13 $ Lex.lex $ pt2 <> "two\n"
    pt3 = "       \t "
    p3 = Prefix pt3
    l3 = rel 26 $ Lex.lex $ pt3 <> "three\n"
  in
    V 40
       Empty
      (Run p1 (Cat.singleton l1) l1 Empty p1)
      ((Rev . Cat.singleton $ Run p2 (Cat.singleton l2) l2 (Cat.singleton $ LayoutMismatch 13 p1 p2) p2) <>
       (Rev . Cat.singleton $ Run p3 (Cat.singleton l3) l3 Empty p3))

exampleI333E300 :: Text
exampleI333E300 =
  "       \t one\n\
  \         two\n\
  \         three\n\
  \"

resultI333E300 :: Layout
resultI333E300 =
  let
    pt1 = "       \t "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = "         "
    p2 = Prefix pt2
    l2 = rel 13 $ Lex.lex $ pt2 <> "two\n"
    pt3 = "         "
    p3 = Prefix pt3
    l3 = rel 26 $ Lex.lex $ pt3 <> "three\n"
  in
    V 40
       Empty
      (Run p1 (Cat.singleton l1) l1 Empty p1)
      ((Rev . Cat.singleton $ Run p2 (Cat.singleton l2) l2 (Cat.singleton $ LayoutMismatch 13 p1 p2) p2) <>
       (Rev . Cat.singleton $ Run p3 (Cat.singleton l3) l3 Empty p3))

exampleI333E301 :: Text
exampleI333E301 =
  "       \t one\n\
  \         two\n\
  \ \t       three\n\
  \"

resultI333E301 :: Layout
resultI333E301 =
  let
    pt1 = "       \t "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = "         "
    p2 = Prefix pt2
    l2 = rel 13 $ Lex.lex $ pt2 <> "two\n"
    pt3 = " \t       "
    p3 = Prefix pt3
    l3 = rel 26 $ Lex.lex $ pt3 <> "three\n"
  in
    V 40
       Empty
      (Run p1 (Cat.singleton l1) l1 Empty p1)
      ((Rev . Cat.singleton $ Run p2 (Cat.singleton l2) l2 (Cat.singleton $ LayoutMismatch 13 p1 p2) p2) <>
       (Rev . Cat.singleton $ Run p3 (Cat.singleton l3) l3 (Cat.singleton $ LayoutMismatch 26 p2 p3) p3))

exampleI333E302 :: Text
exampleI333E302 =
  "       \t one\n\
  \         two\n\
  \    \t    three\n\
  \"

resultI333E302 :: Layout
resultI333E302 =
  let
    pt1 = "       \t "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = "         "
    p2 = Prefix pt2
    l2 = rel 13 $ Lex.lex $ pt2 <> "two\n"
    pt3 = "    \t    "
    p3 = Prefix pt3
    l3 = rel 26 $ Lex.lex $ pt3 <> "three\n"
  in
    V 40
       Empty
      (Run p1 (Cat.singleton l1) l1 Empty p1)
      ((Rev . Cat.singleton $ Run p2 (Cat.singleton l2) l2 (Cat.singleton $ LayoutMismatch 13 p1 p2) p2) <>
       (Rev . Cat.singleton $ Run p3 (Cat.singleton l3) l3 (Cat.singleton $ LayoutMismatch 26 p2 p3) p3))

exampleI333E303 :: Text
exampleI333E303 =
  "       \t one\n\
  \         two\n\
  \       \t three\n\
  \"

resultI333E303 :: Layout
resultI333E303 =
  let
    pt1 = "       \t "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = "         "
    p2 = Prefix pt2
    l2 = rel 13 $ Lex.lex $ pt2 <> "two\n"
    pt3 = "       \t "
    p3 = Prefix pt3
    l3 = rel 26 $ Lex.lex $ pt3 <> "three\n"
  in
    V 40
       Empty
      (Run p1 (Cat.singleton l1) l1 Empty p1)
      ((Rev . Cat.singleton $ Run p2 (Cat.singleton l2) l2 (Cat.singleton $ LayoutMismatch 13 p1 p2) p2) <>
       (Rev . Cat.singleton $ Run p3 (Cat.singleton l3) l3 (Cat.singleton $ LayoutMismatch 26 p2 p3) p3))

exampleI333E310 :: Text
exampleI333E310 =
  "       \t one\n\
  \ \t       two\n\
  \         three\n\
  \"

resultI333E310 :: Layout
resultI333E310 =
  let
    pt1 = "       \t "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = " \t       "
    p2 = Prefix pt2
    l2 = rel 13 $ Lex.lex $ pt2 <> "two\n"
    pt3 = "         "
    p3 = Prefix pt3
    l3 = rel 26 $ Lex.lex $ pt3 <> "three\n"
  in
    V 40
       Empty
      (Run p1 (Cat.singleton l1) l1 Empty p1)
      ((Rev . Cat.singleton $ Run p2 (Cat.singleton l2) l2 (Cat.singleton $ LayoutMismatch 13 p1 p2) p2) <>
       (Rev . Cat.singleton $ Run p3 (Cat.singleton l3) l3 (Cat.singleton $ LayoutMismatch 26 p2 p3) p3))

exampleI333E311 :: Text
exampleI333E311 =
  "       \t one\n\
  \ \t       two\n\
  \ \t       three\n\
  \"

resultI333E311 :: Layout
resultI333E311 =
  let
    pt1 = "       \t "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = " \t       "
    p2 = Prefix pt2
    l2 = rel 13 $ Lex.lex $ pt2 <> "two\n"
    pt3 = " \t       "
    p3 = Prefix pt3
    l3 = rel 26 $ Lex.lex $ pt3 <> "three\n"
  in
    V 40
       Empty
      (Run p1 (Cat.singleton l1) l1 Empty p1)
      ((Rev . Cat.singleton $ Run p2 (Cat.singleton l2) l2 (Cat.singleton $ LayoutMismatch 13 p1 p2) p2) <>
       (Rev . Cat.singleton $ Run p3 (Cat.singleton l3) l3 Empty p3))

exampleI333E312 :: Text
exampleI333E312 =
  "       \t one\n\
  \ \t       two\n\
  \    \t    three\n\
  \"

resultI333E312 :: Layout
resultI333E312 =
  let
    pt1 = "       \t "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = " \t       "
    p2 = Prefix pt2
    l2 = rel 13 $ Lex.lex $ pt2 <> "two\n"
    pt3 = "    \t    "
    p3 = Prefix pt3
    l3 = rel 26 $ Lex.lex $ pt3 <> "three\n"
  in
    V 40
       Empty
      (Run p1 (Cat.singleton l1) l1 Empty p1)
      ((Rev . Cat.singleton $ Run p2 (Cat.singleton l2) l2 (Cat.singleton $ LayoutMismatch 13 p1 p2) p2) <>
       (Rev . Cat.singleton $ Run p3 (Cat.singleton l3) l3 (Cat.singleton $ LayoutMismatch 26 p2 p3) p3))

exampleI333E313 :: Text
exampleI333E313 =
  "       \t one\n\
  \ \t       two\n\
  \       \t three\n\
  \"

resultI333E313 :: Layout
resultI333E313 =
  let
    pt1 = "       \t "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = " \t       "
    p2 = Prefix pt2
    l2 = rel 13 $ Lex.lex $ pt2 <> "two\n"
    pt3 = "       \t "
    p3 = Prefix pt3
    l3 = rel 26 $ Lex.lex $ pt3 <> "three\n"
  in
    V 40
       Empty
      (Run p1 (Cat.singleton l1) l1 Empty p1)
      ((Rev . Cat.singleton $ Run p2 (Cat.singleton l2) l2 (Cat.singleton $ LayoutMismatch 13 p1 p2) p2) <>
       (Rev . Cat.singleton $ Run p3 (Cat.singleton l3) l3 (Cat.singleton $ LayoutMismatch 26 p2 p3) p3))

exampleI333E320 :: Text
exampleI333E320 =
  "       \t one\n\
  \    \t    two\n\
  \         three\n\
  \"

resultI333E320 :: Layout
resultI333E320 =
  let
    pt1 = "       \t "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = "    \t    "
    p2 = Prefix pt2
    l2 = rel 13 $ Lex.lex $ pt2 <> "two\n"
    pt3 = "         "
    p3 = Prefix pt3
    l3 = rel 26 $ Lex.lex $ pt3 <> "three\n"
  in
    V 40
       Empty
      (Run p1 (Cat.singleton l1) l1 Empty p1)
      ((Rev . Cat.singleton $ Run p2 (Cat.singleton l2) l2 (Cat.singleton $ LayoutMismatch 13 p1 p2) p2) <>
       (Rev . Cat.singleton $ Run p3 (Cat.singleton l3) l3 (Cat.singleton $ LayoutMismatch 26 p2 p3) p3))

exampleI333E321 :: Text
exampleI333E321 =
  "       \t one\n\
  \    \t    two\n\
  \ \t       three\n\
  \"

resultI333E321 :: Layout
resultI333E321 =
  let
    pt1 = "       \t "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = "    \t    "
    p2 = Prefix pt2
    l2 = rel 13 $ Lex.lex $ pt2 <> "two\n"
    pt3 = " \t       "
    p3 = Prefix pt3
    l3 = rel 26 $ Lex.lex $ pt3 <> "three\n"
  in
    V 40
       Empty
      (Run p1 (Cat.singleton l1) l1 Empty p1)
      ((Rev . Cat.singleton $ Run p2 (Cat.singleton l2) l2 (Cat.singleton $ LayoutMismatch 13 p1 p2) p2) <>
       (Rev . Cat.singleton $ Run p3 (Cat.singleton l3) l3 (Cat.singleton $ LayoutMismatch 26 p2 p3) p3))

exampleI333E322 :: Text
exampleI333E322 =
  "       \t one\n\
  \    \t    two\n\
  \    \t    three\n\
  \"

resultI333E322 :: Layout
resultI333E322 =
  let
    pt1 = "       \t "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = "    \t    "
    p2 = Prefix pt2
    l2 = rel 13 $ Lex.lex $ pt2 <> "two\n"
    pt3 = "    \t    "
    p3 = Prefix pt3
    l3 = rel 26 $ Lex.lex $ pt3 <> "three\n"
  in
    V 40
       Empty
      (Run p1 (Cat.singleton l1) l1 Empty p1)
      ((Rev . Cat.singleton $ Run p2 (Cat.singleton l2) l2 (Cat.singleton $ LayoutMismatch 13 p1 p2) p2) <>
       (Rev . Cat.singleton $ Run p3 (Cat.singleton l3) l3 Empty p3))


exampleI333E323 :: Text
exampleI333E323 =
  "       \t one\n\
  \    \t    two\n\
  \       \t three\n\
  \"

resultI333E323 :: Layout
resultI333E323 =
  let
    pt1 = "       \t "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = "    \t    "
    p2 = Prefix pt2
    l2 = rel 13 $ Lex.lex $ pt2 <> "two\n"
    pt3 = "       \t "
    p3 = Prefix pt3
    l3 = rel 26 $ Lex.lex $ pt3 <> "three\n"
  in
    V 40
       Empty
      (Run p1 (Cat.singleton l1) l1 Empty p1)
      ((Rev . Cat.singleton $ Run p2 (Cat.singleton l2) l2 (Cat.singleton $ LayoutMismatch 13 p1 p2) p2) <>
       (Rev . Cat.singleton $ Run p3 (Cat.singleton l3) l3 (Cat.singleton $ LayoutMismatch 26 p2 p3) p3))

exampleI333E330 :: Text
exampleI333E330 =
  "       \t one\n\
  \       \t two\n\
  \         three\n\
  \"

resultI333E330 :: Layout
resultI333E330 =
  let
    pt1 = "       \t "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = "       \t "
    p2 = Prefix pt2
    l2 = rel 13 $ Lex.lex $ pt2 <> "two\n"
    pt3 = "         "
    p3 = Prefix pt3
    l3 = rel 26 $ Lex.lex $ pt3 <> "three\n"
  in
    V 40
       Empty
      (Run p1 (Cat.singleton l1) l1 Empty p1)
      ((Rev . Cat.singleton $ Run p2 (Cat.singleton l2) l2 Empty p2) <>
       (Rev . Cat.singleton $ Run p3 (Cat.singleton l3) l3 (Cat.singleton $ LayoutMismatch 26 p2 p3) p3))

exampleI333E331 :: Text
exampleI333E331 =
  "       \t one\n\
  \       \t two\n\
  \ \t       three\n\
  \"

resultI333E331 :: Layout
resultI333E331 =
  let
    pt1 = "       \t "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = "       \t "
    p2 = Prefix pt2
    l2 = rel 13 $ Lex.lex $ pt2 <> "two\n"
    pt3 = " \t       "
    p3 = Prefix pt3
    l3 = rel 26 $ Lex.lex $ pt3 <> "three\n"
  in
    V 40
       Empty
      (Run p1 (Cat.singleton l1) l1 Empty p1)
      ((Rev . Cat.singleton $ Run p2 (Cat.singleton l2) l2 Empty p2) <>
       (Rev . Cat.singleton $ Run p3 (Cat.singleton l3) l3 (Cat.singleton $ LayoutMismatch 26 p2 p3) p3))

exampleI333E332 :: Text
exampleI333E332 =
  "       \t one\n\
  \       \t two\n\
  \    \t    three\n\
  \"

resultI333E332 :: Layout
resultI333E332 =
  let
    pt1 = "       \t "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = "       \t "
    p2 = Prefix pt2
    l2 = rel 13 $ Lex.lex $ pt2 <> "two\n"
    pt3 = "    \t    "
    p3 = Prefix pt3
    l3 = rel 26 $ Lex.lex $ pt3 <> "three\n"
  in
    V 40
       Empty
      (Run p1 (Cat.singleton l1) l1 Empty p1)
      ((Rev . Cat.singleton $ Run p2 (Cat.singleton l2) l2 Empty p2) <>
       (Rev . Cat.singleton $ Run p3 (Cat.singleton l3) l3 (Cat.singleton $ LayoutMismatch 26 p2 p3) p3))

exampleI333E333 :: Text
exampleI333E333 =
  "       \t one\n\
  \       \t two\n\
  \       \t three\n\
  \"

resultI333E333 :: Layout
resultI333E333 =
  let
    pt1 = "       \t "
    p1 = Prefix pt1
    l1 = Lex.lex $ pt1 <> "one\n"
    pt2 = "       \t "
    p2 = Prefix pt2
    l2 = rel 13 $ Lex.lex $ pt2 <> "two\n"
    pt3 = "       \t "
    p3 = Prefix pt3
    l3 = rel 26 $ Lex.lex $ pt3 <> "three\n"
  in
    V 40
       Empty
      (Run p1 (Cat.singleton l1) l1 Empty p1)
      ((Rev . Cat.singleton $ Run p2 (Cat.singleton l2) l2 Empty p2) <>
       (Rev . Cat.singleton $ Run p3 (Cat.singleton l3) l3 Empty p3))


test_layout_example :: TestTree
test_layout_example =
  testGroup "example" [
    testGroup "one" [
      testCase "I1E0"  $ assertAllEqTo exampleI1E0 resultI1E0
    , testCase "I1E1"  $ assertAllEqTo exampleI1E1 resultI1E1
    ]
  , testGroup "two" [
      testCase "I11E00"  $ assertAllEqTo exampleI11E00 resultI11E00
    , testCase "I11E01"  $ assertAllEqTo exampleI11E01 resultI11E01
    , testCase "I11E10"  $ assertAllEqTo exampleI11E10 resultI11E10
    , testCase "I11E11"  $ assertAllEqTo exampleI11E11 resultI11E11
    , testCase "I12E00"  $ assertAllEqTo exampleI12E00 resultI12E00
    , testCase "I12E01"  $ assertAllEqTo exampleI12E01 resultI12E01
    , testCase "I12E02"  $ assertAllEqTo exampleI12E02 resultI12E02
    , testCase "I12E10"  $ assertAllEqTo exampleI12E10 resultI12E10
    , testCase "I12E11"  $ assertAllEqTo exampleI12E11 resultI12E11
    , testCase "I12E12"  $ assertAllEqTo exampleI12E12 resultI12E12
    , testCase "I21E00"  $ assertAllEqTo exampleI21E00 resultI21E00
    , testCase "I21E01"  $ assertAllEqTo exampleI21E01 resultI21E01
    , testCase "I21E10"  $ assertAllEqTo exampleI21E10 resultI21E10
    , testCase "I21E11"  $ assertAllEqTo exampleI21E11 resultI21E11
    , testCase "I21E20"  $ assertAllEqTo exampleI21E20 resultI21E20
    , testCase "I21E21"  $ assertAllEqTo exampleI21E21 resultI21E21
    , testCase "I22E00"  $ assertAllEqTo exampleI22E00 resultI22E00
    , testCase "I22E01"  $ assertAllEqTo exampleI22E01 resultI22E01
    , testCase "I22E02"  $ assertAllEqTo exampleI22E02 resultI22E02
    , testCase "I22E10"  $ assertAllEqTo exampleI22E10 resultI22E10
    , testCase "I22E11"  $ assertAllEqTo exampleI22E11 resultI22E11
    , testCase "I22E12"  $ assertAllEqTo exampleI22E12 resultI22E12
    , testCase "I22E20"  $ assertAllEqTo exampleI22E20 resultI22E20
    , testCase "I22E21"  $ assertAllEqTo exampleI22E21 resultI22E21
    , testCase "I22E22"  $ assertAllEqTo exampleI22E22 resultI22E22
    ]
  , testGroup "three" [
      testCase "I111E000"  $ assertAllEqTo exampleI111E000 resultI111E000
    , testCase "I111E001"  $ assertAllEqTo exampleI111E001 resultI111E001
    , testCase "I111E010"  $ assertAllEqTo exampleI111E010 resultI111E010
    , testCase "I111E011"  $ assertAllEqTo exampleI111E011 resultI111E011
    , testCase "I111E100"  $ assertAllEqTo exampleI111E100 resultI111E100
    , testCase "I111E101"  $ assertAllEqTo exampleI111E101 resultI111E101
    , testCase "I111E110"  $ assertAllEqTo exampleI111E110 resultI111E110
    , testCase "I111E111"  $ assertAllEqTo exampleI111E111 resultI111E111
    , testCase "I112E000"  $ assertAllEqTo exampleI112E000 resultI112E000
    , testCase "I112E001"  $ assertAllEqTo exampleI112E001 resultI112E001
    , testCase "I112E002"  $ assertAllEqTo exampleI112E002 resultI112E002
    , testCase "I112E010"  $ assertAllEqTo exampleI112E010 resultI112E010
    , testCase "I112E011"  $ assertAllEqTo exampleI112E011 resultI112E011
    , testCase "I112E012"  $ assertAllEqTo exampleI112E012 resultI112E012
    , testCase "I112E100"  $ assertAllEqTo exampleI112E100 resultI112E100
    , testCase "I112E101"  $ assertAllEqTo exampleI112E101 resultI112E101
    , testCase "I112E102"  $ assertAllEqTo exampleI112E102 resultI112E102
    , testCase "I112E110"  $ assertAllEqTo exampleI112E110 resultI112E110
    , testCase "I112E111"  $ assertAllEqTo exampleI112E111 resultI112E111
    , testCase "I112E112"  $ assertAllEqTo exampleI112E112 resultI112E112
    , testCase "I113E000"  $ assertAllEqTo exampleI113E000 resultI113E000
    , testCase "I113E001"  $ assertAllEqTo exampleI113E001 resultI113E001
    , testCase "I113E002"  $ assertAllEqTo exampleI113E002 resultI113E002
    , testCase "I113E003"  $ assertAllEqTo exampleI113E003 resultI113E003
    , testCase "I113E010"  $ assertAllEqTo exampleI113E010 resultI113E010
    , testCase "I113E011"  $ assertAllEqTo exampleI113E011 resultI113E011
    , testCase "I113E012"  $ assertAllEqTo exampleI113E012 resultI113E012
    , testCase "I113E013"  $ assertAllEqTo exampleI113E013 resultI113E013
    , testCase "I113E100"  $ assertAllEqTo exampleI113E100 resultI113E100
    , testCase "I113E101"  $ assertAllEqTo exampleI113E101 resultI113E101
    , testCase "I113E102"  $ assertAllEqTo exampleI113E102 resultI113E102
    , testCase "I113E103"  $ assertAllEqTo exampleI113E103 resultI113E103
    , testCase "I113E110"  $ assertAllEqTo exampleI113E110 resultI113E110
    , testCase "I113E111"  $ assertAllEqTo exampleI113E111 resultI113E111
    , testCase "I113E112"  $ assertAllEqTo exampleI113E112 resultI113E112
    , testCase "I113E113"  $ assertAllEqTo exampleI113E113 resultI113E113
    , testCase "I121E000"  $ assertAllEqTo exampleI121E000 resultI121E000
    , testCase "I121E001"  $ assertAllEqTo exampleI121E001 resultI121E001
    , testCase "I121E010"  $ assertAllEqTo exampleI121E010 resultI121E010
    , testCase "I121E011"  $ assertAllEqTo exampleI121E011 resultI121E011
    , testCase "I121E020"  $ assertAllEqTo exampleI121E020 resultI121E020
    , testCase "I121E021"  $ assertAllEqTo exampleI121E021 resultI121E021
    , testCase "I121E100"  $ assertAllEqTo exampleI121E100 resultI121E100
    , testCase "I121E101"  $ assertAllEqTo exampleI121E101 resultI121E101
    , testCase "I121E110"  $ assertAllEqTo exampleI121E110 resultI121E110
    , testCase "I121E111"  $ assertAllEqTo exampleI121E111 resultI121E111
    , testCase "I121E120"  $ assertAllEqTo exampleI121E120 resultI121E120
    , testCase "I121E121"  $ assertAllEqTo exampleI121E121 resultI121E121
    , testCase "I122E000"  $ assertAllEqTo exampleI122E000 resultI122E000
    , testCase "I122E001"  $ assertAllEqTo exampleI122E001 resultI122E001
    , testCase "I122E002"  $ assertAllEqTo exampleI122E002 resultI122E002
    , testCase "I122E010"  $ assertAllEqTo exampleI122E010 resultI122E010
    , testCase "I122E011"  $ assertAllEqTo exampleI122E011 resultI122E011
    , testCase "I122E012"  $ assertAllEqTo exampleI122E012 resultI122E012
    , testCase "I122E020"  $ assertAllEqTo exampleI122E020 resultI122E020
    , testCase "I122E021"  $ assertAllEqTo exampleI122E021 resultI122E021
    , testCase "I122E022"  $ assertAllEqTo exampleI122E022 resultI122E022
    , testCase "I122E100"  $ assertAllEqTo exampleI122E100 resultI122E100
    , testCase "I122E101"  $ assertAllEqTo exampleI122E101 resultI122E101
    , testCase "I122E102"  $ assertAllEqTo exampleI122E102 resultI122E102
    , testCase "I122E110"  $ assertAllEqTo exampleI122E110 resultI122E110
    , testCase "I122E111"  $ assertAllEqTo exampleI122E111 resultI122E111
    , testCase "I122E112"  $ assertAllEqTo exampleI122E112 resultI122E112
    , testCase "I122E120"  $ assertAllEqTo exampleI122E120 resultI122E120
    , testCase "I122E121"  $ assertAllEqTo exampleI122E121 resultI122E121
    , testCase "I122E122"  $ assertAllEqTo exampleI122E122 resultI122E122
    , testCase "I123E000"  $ assertAllEqTo exampleI123E000 resultI123E000
    , testCase "I123E001"  $ assertAllEqTo exampleI123E001 resultI123E001
    , testCase "I123E002"  $ assertAllEqTo exampleI123E002 resultI123E002
    , testCase "I123E003"  $ assertAllEqTo exampleI123E003 resultI123E003
    , testCase "I123E010"  $ assertAllEqTo exampleI123E010 resultI123E010
    , testCase "I123E011"  $ assertAllEqTo exampleI123E011 resultI123E011
    , testCase "I123E012"  $ assertAllEqTo exampleI123E012 resultI123E012
    , testCase "I123E013"  $ assertAllEqTo exampleI123E013 resultI123E013
    , testCase "I123E020"  $ assertAllEqTo exampleI123E020 resultI123E020
    , testCase "I123E021"  $ assertAllEqTo exampleI123E021 resultI123E021
    , testCase "I123E022"  $ assertAllEqTo exampleI123E022 resultI123E022
    , testCase "I123E023"  $ assertAllEqTo exampleI123E023 resultI123E023
    , testCase "I123E100"  $ assertAllEqTo exampleI123E100 resultI123E100
    , testCase "I123E101"  $ assertAllEqTo exampleI123E101 resultI123E101
    , testCase "I123E102"  $ assertAllEqTo exampleI123E102 resultI123E102
    , testCase "I123E103"  $ assertAllEqTo exampleI123E103 resultI123E103
    , testCase "I123E110"  $ assertAllEqTo exampleI123E110 resultI123E110
    , testCase "I123E111"  $ assertAllEqTo exampleI123E111 resultI123E111
    , testCase "I123E112"  $ assertAllEqTo exampleI123E112 resultI123E112
    , testCase "I123E113"  $ assertAllEqTo exampleI123E113 resultI123E113
    , testCase "I123E120"  $ assertAllEqTo exampleI123E120 resultI123E120
    , testCase "I123E121"  $ assertAllEqTo exampleI123E121 resultI123E121
    , testCase "I123E122"  $ assertAllEqTo exampleI123E122 resultI123E122
    , testCase "I123E123"  $ assertAllEqTo exampleI123E123 resultI123E123
    , testCase "I131E000"  $ assertAllEqTo exampleI131E000 resultI131E000
    , testCase "I131E001"  $ assertAllEqTo exampleI131E001 resultI131E001
    , testCase "I131E010"  $ assertAllEqTo exampleI131E010 resultI131E010
    , testCase "I131E011"  $ assertAllEqTo exampleI131E011 resultI131E011
    , testCase "I131E020"  $ assertAllEqTo exampleI131E020 resultI131E020
    , testCase "I131E021"  $ assertAllEqTo exampleI131E021 resultI131E021
    , testCase "I131E030"  $ assertAllEqTo exampleI131E030 resultI131E030
    , testCase "I131E031"  $ assertAllEqTo exampleI131E031 resultI131E031
    , testCase "I131E100"  $ assertAllEqTo exampleI131E100 resultI131E100
    , testCase "I131E101"  $ assertAllEqTo exampleI131E101 resultI131E101
    , testCase "I131E110"  $ assertAllEqTo exampleI131E110 resultI131E110
    , testCase "I131E111"  $ assertAllEqTo exampleI131E111 resultI131E111
    , testCase "I131E120"  $ assertAllEqTo exampleI131E120 resultI131E120
    , testCase "I131E121"  $ assertAllEqTo exampleI131E121 resultI131E121
    , testCase "I131E130"  $ assertAllEqTo exampleI131E130 resultI131E130
    , testCase "I131E131"  $ assertAllEqTo exampleI131E131 resultI131E131
    , testCase "I132E000"  $ assertAllEqTo exampleI132E000 resultI132E000
    , testCase "I132E001"  $ assertAllEqTo exampleI132E001 resultI132E001
    , testCase "I132E002"  $ assertAllEqTo exampleI132E002 resultI132E002
    , testCase "I132E010"  $ assertAllEqTo exampleI132E010 resultI132E010
    , testCase "I132E011"  $ assertAllEqTo exampleI132E011 resultI132E011
    , testCase "I132E012"  $ assertAllEqTo exampleI132E012 resultI132E012
    , testCase "I132E020"  $ assertAllEqTo exampleI132E020 resultI132E020
    , testCase "I132E021"  $ assertAllEqTo exampleI132E021 resultI132E021
    , testCase "I132E022"  $ assertAllEqTo exampleI132E022 resultI132E022
    , testCase "I132E030"  $ assertAllEqTo exampleI132E030 resultI132E030
    , testCase "I132E031"  $ assertAllEqTo exampleI132E031 resultI132E031
    , testCase "I132E032"  $ assertAllEqTo exampleI132E032 resultI132E032
    , testCase "I132E100"  $ assertAllEqTo exampleI132E100 resultI132E100
    , testCase "I132E101"  $ assertAllEqTo exampleI132E101 resultI132E101
    , testCase "I132E102"  $ assertAllEqTo exampleI132E102 resultI132E102
    , testCase "I132E110"  $ assertAllEqTo exampleI132E110 resultI132E110
    , testCase "I132E111"  $ assertAllEqTo exampleI132E111 resultI132E111
    , testCase "I132E112"  $ assertAllEqTo exampleI132E112 resultI132E112
    , testCase "I132E120"  $ assertAllEqTo exampleI132E120 resultI132E120
    , testCase "I132E121"  $ assertAllEqTo exampleI132E121 resultI132E121
    , testCase "I132E122"  $ assertAllEqTo exampleI132E122 resultI132E122
    , testCase "I132E130"  $ assertAllEqTo exampleI132E130 resultI132E130
    , testCase "I132E131"  $ assertAllEqTo exampleI132E131 resultI132E131
    , testCase "I132E132"  $ assertAllEqTo exampleI132E132 resultI132E132
    , testCase "I133E000"  $ assertAllEqTo exampleI133E000 resultI133E000
    , testCase "I133E001"  $ assertAllEqTo exampleI133E001 resultI133E001
    , testCase "I133E002"  $ assertAllEqTo exampleI133E002 resultI133E002
    , testCase "I133E003"  $ assertAllEqTo exampleI133E003 resultI133E003
    , testCase "I133E010"  $ assertAllEqTo exampleI133E010 resultI133E010
    , testCase "I133E011"  $ assertAllEqTo exampleI133E011 resultI133E011
    , testCase "I133E012"  $ assertAllEqTo exampleI133E012 resultI133E012
    , testCase "I133E013"  $ assertAllEqTo exampleI133E013 resultI133E013
    , testCase "I133E020"  $ assertAllEqTo exampleI133E020 resultI133E020
    , testCase "I133E021"  $ assertAllEqTo exampleI133E021 resultI133E021
    , testCase "I133E022"  $ assertAllEqTo exampleI133E022 resultI133E022
    , testCase "I133E023"  $ assertAllEqTo exampleI133E023 resultI133E023
    , testCase "I133E030"  $ assertAllEqTo exampleI133E030 resultI133E030
    , testCase "I133E031"  $ assertAllEqTo exampleI133E031 resultI133E031
    , testCase "I133E032"  $ assertAllEqTo exampleI133E032 resultI133E032
    , testCase "I133E033"  $ assertAllEqTo exampleI133E033 resultI133E033
    , testCase "I133E100"  $ assertAllEqTo exampleI133E100 resultI133E100
    , testCase "I133E101"  $ assertAllEqTo exampleI133E101 resultI133E101
    , testCase "I133E102"  $ assertAllEqTo exampleI133E102 resultI133E102
    , testCase "I133E103"  $ assertAllEqTo exampleI133E103 resultI133E103
    , testCase "I133E110"  $ assertAllEqTo exampleI133E110 resultI133E110
    , testCase "I133E111"  $ assertAllEqTo exampleI133E111 resultI133E111
    , testCase "I133E112"  $ assertAllEqTo exampleI133E112 resultI133E112
    , testCase "I133E113"  $ assertAllEqTo exampleI133E113 resultI133E113
    , testCase "I133E120"  $ assertAllEqTo exampleI133E120 resultI133E120
    , testCase "I133E121"  $ assertAllEqTo exampleI133E121 resultI133E121
    , testCase "I133E122"  $ assertAllEqTo exampleI133E122 resultI133E122
    , testCase "I133E123"  $ assertAllEqTo exampleI133E123 resultI133E123
    , testCase "I133E130"  $ assertAllEqTo exampleI133E130 resultI133E130
    , testCase "I133E131"  $ assertAllEqTo exampleI133E131 resultI133E131
    , testCase "I133E132"  $ assertAllEqTo exampleI133E132 resultI133E132
    , testCase "I133E133"  $ assertAllEqTo exampleI133E133 resultI133E133
    , testCase "I211E000"  $ assertAllEqTo exampleI211E000 resultI211E000
    , testCase "I211E001"  $ assertAllEqTo exampleI211E001 resultI211E001
    , testCase "I211E010"  $ assertAllEqTo exampleI211E010 resultI211E010
    , testCase "I211E011"  $ assertAllEqTo exampleI211E011 resultI211E011
    , testCase "I211E100"  $ assertAllEqTo exampleI211E100 resultI211E100
    , testCase "I211E101"  $ assertAllEqTo exampleI211E101 resultI211E101
    , testCase "I211E110"  $ assertAllEqTo exampleI211E110 resultI211E110
    , testCase "I211E111"  $ assertAllEqTo exampleI211E111 resultI211E111
    , testCase "I211E200"  $ assertAllEqTo exampleI211E200 resultI211E200
    , testCase "I211E201"  $ assertAllEqTo exampleI211E201 resultI211E201
    , testCase "I211E210"  $ assertAllEqTo exampleI211E210 resultI211E210
    , testCase "I211E211"  $ assertAllEqTo exampleI211E211 resultI211E211
    , testCase "I212E000"  $ assertAllEqTo exampleI212E000 resultI212E000
    , testCase "I212E001"  $ assertAllEqTo exampleI212E001 resultI212E001
    , testCase "I212E002"  $ assertAllEqTo exampleI212E002 resultI212E002
    , testCase "I212E010"  $ assertAllEqTo exampleI212E010 resultI212E010
    , testCase "I212E011"  $ assertAllEqTo exampleI212E011 resultI212E011
    , testCase "I212E012"  $ assertAllEqTo exampleI212E012 resultI212E012
    , testCase "I212E100"  $ assertAllEqTo exampleI212E100 resultI212E100
    , testCase "I212E101"  $ assertAllEqTo exampleI212E101 resultI212E101
    , testCase "I212E102"  $ assertAllEqTo exampleI212E102 resultI212E102
    , testCase "I212E110"  $ assertAllEqTo exampleI212E110 resultI212E110
    , testCase "I212E111"  $ assertAllEqTo exampleI212E111 resultI212E111
    , testCase "I212E112"  $ assertAllEqTo exampleI212E112 resultI212E112
    , testCase "I212E200"  $ assertAllEqTo exampleI212E200 resultI212E200
    , testCase "I212E201"  $ assertAllEqTo exampleI212E201 resultI212E201
    , testCase "I212E202"  $ assertAllEqTo exampleI212E202 resultI212E202
    , testCase "I212E210"  $ assertAllEqTo exampleI212E210 resultI212E210
    , testCase "I212E211"  $ assertAllEqTo exampleI212E211 resultI212E211
    , testCase "I212E212"  $ assertAllEqTo exampleI212E212 resultI212E212
    , testCase "I213E000"  $ assertAllEqTo exampleI213E000 resultI213E000
    , testCase "I213E001"  $ assertAllEqTo exampleI213E001 resultI213E001
    , testCase "I213E002"  $ assertAllEqTo exampleI213E002 resultI213E002
    , testCase "I213E003"  $ assertAllEqTo exampleI213E003 resultI213E003
    , testCase "I213E010"  $ assertAllEqTo exampleI213E010 resultI213E010
    , testCase "I213E011"  $ assertAllEqTo exampleI213E011 resultI213E011
    , testCase "I213E012"  $ assertAllEqTo exampleI213E012 resultI213E012
    , testCase "I213E013"  $ assertAllEqTo exampleI213E013 resultI213E013
    , testCase "I213E100"  $ assertAllEqTo exampleI213E100 resultI213E100
    , testCase "I213E101"  $ assertAllEqTo exampleI213E101 resultI213E101
    , testCase "I213E102"  $ assertAllEqTo exampleI213E102 resultI213E102
    , testCase "I213E103"  $ assertAllEqTo exampleI213E103 resultI213E103
    , testCase "I213E110"  $ assertAllEqTo exampleI213E110 resultI213E110
    , testCase "I213E111"  $ assertAllEqTo exampleI213E111 resultI213E111
    , testCase "I213E112"  $ assertAllEqTo exampleI213E112 resultI213E112
    , testCase "I213E113"  $ assertAllEqTo exampleI213E113 resultI213E113
    , testCase "I213E200"  $ assertAllEqTo exampleI213E200 resultI213E200
    , testCase "I213E201"  $ assertAllEqTo exampleI213E201 resultI213E201
    , testCase "I213E202"  $ assertAllEqTo exampleI213E202 resultI213E202
    , testCase "I213E203"  $ assertAllEqTo exampleI213E203 resultI213E203
    , testCase "I213E210"  $ assertAllEqTo exampleI213E210 resultI213E210
    , testCase "I213E211"  $ assertAllEqTo exampleI213E211 resultI213E211
    , testCase "I213E212"  $ assertAllEqTo exampleI213E212 resultI213E212
    , testCase "I213E213"  $ assertAllEqTo exampleI213E213 resultI213E213
    , testCase "I221E000"  $ assertAllEqTo exampleI221E000 resultI221E000
    , testCase "I221E001"  $ assertAllEqTo exampleI221E001 resultI221E001
    , testCase "I221E010"  $ assertAllEqTo exampleI221E010 resultI221E010
    , testCase "I221E011"  $ assertAllEqTo exampleI221E011 resultI221E011
    , testCase "I221E020"  $ assertAllEqTo exampleI221E020 resultI221E020
    , testCase "I221E021"  $ assertAllEqTo exampleI221E021 resultI221E021
    , testCase "I221E100"  $ assertAllEqTo exampleI221E100 resultI221E100
    , testCase "I221E101"  $ assertAllEqTo exampleI221E101 resultI221E101
    , testCase "I221E110"  $ assertAllEqTo exampleI221E110 resultI221E110
    , testCase "I221E111"  $ assertAllEqTo exampleI221E111 resultI221E111
    , testCase "I221E120"  $ assertAllEqTo exampleI221E120 resultI221E120
    , testCase "I221E121"  $ assertAllEqTo exampleI221E121 resultI221E121
    , testCase "I221E200"  $ assertAllEqTo exampleI221E200 resultI221E200
    , testCase "I221E201"  $ assertAllEqTo exampleI221E201 resultI221E201
    , testCase "I221E210"  $ assertAllEqTo exampleI221E210 resultI221E210
    , testCase "I221E211"  $ assertAllEqTo exampleI221E211 resultI221E211
    , testCase "I221E220"  $ assertAllEqTo exampleI221E220 resultI221E220
    , testCase "I221E221"  $ assertAllEqTo exampleI221E221 resultI221E221
    , testCase "I222E000"  $ assertAllEqTo exampleI222E000 resultI222E000
    , testCase "I222E001"  $ assertAllEqTo exampleI222E001 resultI222E001
    , testCase "I222E002"  $ assertAllEqTo exampleI222E002 resultI222E002
    , testCase "I222E010"  $ assertAllEqTo exampleI222E010 resultI222E010
    , testCase "I222E011"  $ assertAllEqTo exampleI222E011 resultI222E011
    , testCase "I222E012"  $ assertAllEqTo exampleI222E012 resultI222E012
    , testCase "I222E020"  $ assertAllEqTo exampleI222E020 resultI222E020
    , testCase "I222E021"  $ assertAllEqTo exampleI222E021 resultI222E021
    , testCase "I222E022"  $ assertAllEqTo exampleI222E022 resultI222E022
    , testCase "I222E100"  $ assertAllEqTo exampleI222E100 resultI222E100
    , testCase "I222E101"  $ assertAllEqTo exampleI222E101 resultI222E101
    , testCase "I222E102"  $ assertAllEqTo exampleI222E102 resultI222E102
    , testCase "I222E110"  $ assertAllEqTo exampleI222E110 resultI222E110
    , testCase "I222E111"  $ assertAllEqTo exampleI222E111 resultI222E111
    , testCase "I222E112"  $ assertAllEqTo exampleI222E112 resultI222E112
    , testCase "I222E120"  $ assertAllEqTo exampleI222E120 resultI222E120
    , testCase "I222E121"  $ assertAllEqTo exampleI222E121 resultI222E121
    , testCase "I222E122"  $ assertAllEqTo exampleI222E122 resultI222E122
    , testCase "I222E200"  $ assertAllEqTo exampleI222E200 resultI222E200
    , testCase "I222E201"  $ assertAllEqTo exampleI222E201 resultI222E201
    , testCase "I222E202"  $ assertAllEqTo exampleI222E202 resultI222E202
    , testCase "I222E210"  $ assertAllEqTo exampleI222E210 resultI222E210
    , testCase "I222E211"  $ assertAllEqTo exampleI222E211 resultI222E211
    , testCase "I222E212"  $ assertAllEqTo exampleI222E212 resultI222E212
    , testCase "I222E220"  $ assertAllEqTo exampleI222E220 resultI222E220
    , testCase "I222E221"  $ assertAllEqTo exampleI222E221 resultI222E221
    , testCase "I222E222"  $ assertAllEqTo exampleI222E222 resultI222E222
    , testCase "I223E000"  $ assertAllEqTo exampleI223E000 resultI223E000
    , testCase "I223E001"  $ assertAllEqTo exampleI223E001 resultI223E001
    , testCase "I223E002"  $ assertAllEqTo exampleI223E002 resultI223E002
    , testCase "I223E003"  $ assertAllEqTo exampleI223E003 resultI223E003
    , testCase "I223E010"  $ assertAllEqTo exampleI223E010 resultI223E010
    , testCase "I223E011"  $ assertAllEqTo exampleI223E011 resultI223E011
    , testCase "I223E012"  $ assertAllEqTo exampleI223E012 resultI223E012
    , testCase "I223E013"  $ assertAllEqTo exampleI223E013 resultI223E013
    , testCase "I223E020"  $ assertAllEqTo exampleI223E020 resultI223E020
    , testCase "I223E021"  $ assertAllEqTo exampleI223E021 resultI223E021
    , testCase "I223E022"  $ assertAllEqTo exampleI223E022 resultI223E022
    , testCase "I223E023"  $ assertAllEqTo exampleI223E023 resultI223E023
    , testCase "I223E100"  $ assertAllEqTo exampleI223E100 resultI223E100
    , testCase "I223E101"  $ assertAllEqTo exampleI223E101 resultI223E101
    , testCase "I223E102"  $ assertAllEqTo exampleI223E102 resultI223E102
    , testCase "I223E103"  $ assertAllEqTo exampleI223E103 resultI223E103
    , testCase "I223E110"  $ assertAllEqTo exampleI223E110 resultI223E110
    , testCase "I223E111"  $ assertAllEqTo exampleI223E111 resultI223E111
    , testCase "I223E112"  $ assertAllEqTo exampleI223E112 resultI223E112
    , testCase "I223E113"  $ assertAllEqTo exampleI223E113 resultI223E113
    , testCase "I223E120"  $ assertAllEqTo exampleI223E120 resultI223E120
    , testCase "I223E121"  $ assertAllEqTo exampleI223E121 resultI223E121
    , testCase "I223E122"  $ assertAllEqTo exampleI223E122 resultI223E122
    , testCase "I223E123"  $ assertAllEqTo exampleI223E123 resultI223E123
    , testCase "I223E200"  $ assertAllEqTo exampleI223E200 resultI223E200
    , testCase "I223E201"  $ assertAllEqTo exampleI223E201 resultI223E201
    , testCase "I223E202"  $ assertAllEqTo exampleI223E202 resultI223E202
    , testCase "I223E203"  $ assertAllEqTo exampleI223E203 resultI223E203
    , testCase "I223E210"  $ assertAllEqTo exampleI223E210 resultI223E210
    , testCase "I223E211"  $ assertAllEqTo exampleI223E211 resultI223E211
    , testCase "I223E212"  $ assertAllEqTo exampleI223E212 resultI223E212
    , testCase "I223E213"  $ assertAllEqTo exampleI223E213 resultI223E213
    , testCase "I223E220"  $ assertAllEqTo exampleI223E220 resultI223E220
    , testCase "I223E221"  $ assertAllEqTo exampleI223E221 resultI223E221
    , testCase "I223E222"  $ assertAllEqTo exampleI223E222 resultI223E222
    , testCase "I223E223"  $ assertAllEqTo exampleI223E223 resultI223E223
    , testCase "I231E000"  $ assertAllEqTo exampleI231E000 resultI231E000
    , testCase "I231E001"  $ assertAllEqTo exampleI231E001 resultI231E001
    , testCase "I231E010"  $ assertAllEqTo exampleI231E010 resultI231E010
    , testCase "I231E011"  $ assertAllEqTo exampleI231E011 resultI231E011
    , testCase "I231E020"  $ assertAllEqTo exampleI231E020 resultI231E020
    , testCase "I231E021"  $ assertAllEqTo exampleI231E021 resultI231E021
    , testCase "I231E030"  $ assertAllEqTo exampleI231E030 resultI231E030
    , testCase "I231E031"  $ assertAllEqTo exampleI231E031 resultI231E031
    , testCase "I231E100"  $ assertAllEqTo exampleI231E100 resultI231E100
    , testCase "I231E101"  $ assertAllEqTo exampleI231E101 resultI231E101
    , testCase "I231E110"  $ assertAllEqTo exampleI231E110 resultI231E110
    , testCase "I231E111"  $ assertAllEqTo exampleI231E111 resultI231E111
    , testCase "I231E120"  $ assertAllEqTo exampleI231E120 resultI231E120
    , testCase "I231E121"  $ assertAllEqTo exampleI231E121 resultI231E121
    , testCase "I231E130"  $ assertAllEqTo exampleI231E130 resultI231E130
    , testCase "I231E131"  $ assertAllEqTo exampleI231E131 resultI231E131
    , testCase "I231E200"  $ assertAllEqTo exampleI231E200 resultI231E200
    , testCase "I231E201"  $ assertAllEqTo exampleI231E201 resultI231E201
    , testCase "I231E210"  $ assertAllEqTo exampleI231E210 resultI231E210
    , testCase "I231E211"  $ assertAllEqTo exampleI231E211 resultI231E211
    , testCase "I231E220"  $ assertAllEqTo exampleI231E220 resultI231E220
    , testCase "I231E221"  $ assertAllEqTo exampleI231E221 resultI231E221
    , testCase "I231E230"  $ assertAllEqTo exampleI231E230 resultI231E230
    , testCase "I231E231"  $ assertAllEqTo exampleI231E231 resultI231E231
    , testCase "I232E000"  $ assertAllEqTo exampleI232E000 resultI232E000
    , testCase "I232E001"  $ assertAllEqTo exampleI232E001 resultI232E001
    , testCase "I232E002"  $ assertAllEqTo exampleI232E002 resultI232E002
    , testCase "I232E010"  $ assertAllEqTo exampleI232E010 resultI232E010
    , testCase "I232E011"  $ assertAllEqTo exampleI232E011 resultI232E011
    , testCase "I232E012"  $ assertAllEqTo exampleI232E012 resultI232E012
    , testCase "I232E020"  $ assertAllEqTo exampleI232E020 resultI232E020
    , testCase "I232E021"  $ assertAllEqTo exampleI232E021 resultI232E021
    , testCase "I232E022"  $ assertAllEqTo exampleI232E022 resultI232E022
    , testCase "I232E030"  $ assertAllEqTo exampleI232E030 resultI232E030
    , testCase "I232E031"  $ assertAllEqTo exampleI232E031 resultI232E031
    , testCase "I232E032"  $ assertAllEqTo exampleI232E032 resultI232E032
    , testCase "I232E100"  $ assertAllEqTo exampleI232E100 resultI232E100
    , testCase "I232E101"  $ assertAllEqTo exampleI232E101 resultI232E101
    , testCase "I232E102"  $ assertAllEqTo exampleI232E102 resultI232E102
    , testCase "I232E110"  $ assertAllEqTo exampleI232E110 resultI232E110
    , testCase "I232E111"  $ assertAllEqTo exampleI232E111 resultI232E111
    , testCase "I232E112"  $ assertAllEqTo exampleI232E112 resultI232E112
    , testCase "I232E120"  $ assertAllEqTo exampleI232E120 resultI232E120
    , testCase "I232E121"  $ assertAllEqTo exampleI232E121 resultI232E121
    , testCase "I232E122"  $ assertAllEqTo exampleI232E122 resultI232E122
    , testCase "I232E130"  $ assertAllEqTo exampleI232E130 resultI232E130
    , testCase "I232E131"  $ assertAllEqTo exampleI232E131 resultI232E131
    , testCase "I232E132"  $ assertAllEqTo exampleI232E132 resultI232E132
    , testCase "I232E200"  $ assertAllEqTo exampleI232E200 resultI232E200
    , testCase "I232E201"  $ assertAllEqTo exampleI232E201 resultI232E201
    , testCase "I232E202"  $ assertAllEqTo exampleI232E202 resultI232E202
    , testCase "I232E210"  $ assertAllEqTo exampleI232E210 resultI232E210
    , testCase "I232E211"  $ assertAllEqTo exampleI232E211 resultI232E211
    , testCase "I232E212"  $ assertAllEqTo exampleI232E212 resultI232E212
    , testCase "I232E220"  $ assertAllEqTo exampleI232E220 resultI232E220
    , testCase "I232E221"  $ assertAllEqTo exampleI232E221 resultI232E221
    , testCase "I232E222"  $ assertAllEqTo exampleI232E222 resultI232E222
    , testCase "I232E230"  $ assertAllEqTo exampleI232E230 resultI232E230
    , testCase "I232E231"  $ assertAllEqTo exampleI232E231 resultI232E231
    , testCase "I232E232"  $ assertAllEqTo exampleI232E232 resultI232E232
    , testCase "I233E000"  $ assertAllEqTo exampleI233E000 resultI233E000
    , testCase "I233E001"  $ assertAllEqTo exampleI233E001 resultI233E001
    , testCase "I233E002"  $ assertAllEqTo exampleI233E002 resultI233E002
    , testCase "I233E003"  $ assertAllEqTo exampleI233E003 resultI233E003
    , testCase "I233E010"  $ assertAllEqTo exampleI233E010 resultI233E010
    , testCase "I233E011"  $ assertAllEqTo exampleI233E011 resultI233E011
    , testCase "I233E012"  $ assertAllEqTo exampleI233E012 resultI233E012
    , testCase "I233E013"  $ assertAllEqTo exampleI233E013 resultI233E013
    , testCase "I233E020"  $ assertAllEqTo exampleI233E020 resultI233E020
    , testCase "I233E021"  $ assertAllEqTo exampleI233E021 resultI233E021
    , testCase "I233E022"  $ assertAllEqTo exampleI233E022 resultI233E022
    , testCase "I233E023"  $ assertAllEqTo exampleI233E023 resultI233E023
    , testCase "I233E030"  $ assertAllEqTo exampleI233E030 resultI233E030
    , testCase "I233E031"  $ assertAllEqTo exampleI233E031 resultI233E031
    , testCase "I233E032"  $ assertAllEqTo exampleI233E032 resultI233E032
    , testCase "I233E033"  $ assertAllEqTo exampleI233E033 resultI233E033
    , testCase "I233E100"  $ assertAllEqTo exampleI233E100 resultI233E100
    , testCase "I233E101"  $ assertAllEqTo exampleI233E101 resultI233E101
    , testCase "I233E102"  $ assertAllEqTo exampleI233E102 resultI233E102
    , testCase "I233E103"  $ assertAllEqTo exampleI233E103 resultI233E103
    , testCase "I233E110"  $ assertAllEqTo exampleI233E110 resultI233E110
    , testCase "I233E111"  $ assertAllEqTo exampleI233E111 resultI233E111
    , testCase "I233E112"  $ assertAllEqTo exampleI233E112 resultI233E112
    , testCase "I233E113"  $ assertAllEqTo exampleI233E113 resultI233E113
    , testCase "I233E120"  $ assertAllEqTo exampleI233E120 resultI233E120
    , testCase "I233E121"  $ assertAllEqTo exampleI233E121 resultI233E121
    , testCase "I233E122"  $ assertAllEqTo exampleI233E122 resultI233E122
    , testCase "I233E123"  $ assertAllEqTo exampleI233E123 resultI233E123
    , testCase "I233E130"  $ assertAllEqTo exampleI233E130 resultI233E130
    , testCase "I233E131"  $ assertAllEqTo exampleI233E131 resultI233E131
    , testCase "I233E132"  $ assertAllEqTo exampleI233E132 resultI233E132
    , testCase "I233E133"  $ assertAllEqTo exampleI233E133 resultI233E133
    , testCase "I233E200"  $ assertAllEqTo exampleI233E200 resultI233E200
    , testCase "I233E201"  $ assertAllEqTo exampleI233E201 resultI233E201
    , testCase "I233E202"  $ assertAllEqTo exampleI233E202 resultI233E202
    , testCase "I233E203"  $ assertAllEqTo exampleI233E203 resultI233E203
    , testCase "I233E210"  $ assertAllEqTo exampleI233E210 resultI233E210
    , testCase "I233E211"  $ assertAllEqTo exampleI233E211 resultI233E211
    , testCase "I233E212"  $ assertAllEqTo exampleI233E212 resultI233E212
    , testCase "I233E213"  $ assertAllEqTo exampleI233E213 resultI233E213
    , testCase "I233E220"  $ assertAllEqTo exampleI233E220 resultI233E220
    , testCase "I233E221"  $ assertAllEqTo exampleI233E221 resultI233E221
    , testCase "I233E222"  $ assertAllEqTo exampleI233E222 resultI233E222
    , testCase "I233E223"  $ assertAllEqTo exampleI233E223 resultI233E223
    , testCase "I233E230"  $ assertAllEqTo exampleI233E230 resultI233E230
    , testCase "I233E231"  $ assertAllEqTo exampleI233E231 resultI233E231
    , testCase "I233E232"  $ assertAllEqTo exampleI233E232 resultI233E232
    , testCase "I233E233"  $ assertAllEqTo exampleI233E233 resultI233E233
    , testCase "I311E000"  $ assertAllEqTo exampleI311E000 resultI311E000
    , testCase "I311E001"  $ assertAllEqTo exampleI311E001 resultI311E001
    , testCase "I311E010"  $ assertAllEqTo exampleI311E010 resultI311E010
    , testCase "I311E011"  $ assertAllEqTo exampleI311E011 resultI311E011
    , testCase "I311E100"  $ assertAllEqTo exampleI311E100 resultI311E100
    , testCase "I311E101"  $ assertAllEqTo exampleI311E101 resultI311E101
    , testCase "I311E110"  $ assertAllEqTo exampleI311E110 resultI311E110
    , testCase "I311E111"  $ assertAllEqTo exampleI311E111 resultI311E111
    , testCase "I311E200"  $ assertAllEqTo exampleI311E200 resultI311E200
    , testCase "I311E201"  $ assertAllEqTo exampleI311E201 resultI311E201
    , testCase "I311E210"  $ assertAllEqTo exampleI311E210 resultI311E210
    , testCase "I311E211"  $ assertAllEqTo exampleI311E211 resultI311E211
    , testCase "I311E300"  $ assertAllEqTo exampleI311E300 resultI311E300
    , testCase "I311E301"  $ assertAllEqTo exampleI311E301 resultI311E301
    , testCase "I311E310"  $ assertAllEqTo exampleI311E310 resultI311E310
    , testCase "I311E311"  $ assertAllEqTo exampleI311E311 resultI311E311
    , testCase "I312E000"  $ assertAllEqTo exampleI312E000 resultI312E000
    , testCase "I312E001"  $ assertAllEqTo exampleI312E001 resultI312E001
    , testCase "I312E002"  $ assertAllEqTo exampleI312E002 resultI312E002
    , testCase "I312E010"  $ assertAllEqTo exampleI312E010 resultI312E010
    , testCase "I312E011"  $ assertAllEqTo exampleI312E011 resultI312E011
    , testCase "I312E012"  $ assertAllEqTo exampleI312E012 resultI312E012
    , testCase "I312E100"  $ assertAllEqTo exampleI312E100 resultI312E100
    , testCase "I312E101"  $ assertAllEqTo exampleI312E101 resultI312E101
    , testCase "I312E102"  $ assertAllEqTo exampleI312E102 resultI312E102
    , testCase "I312E110"  $ assertAllEqTo exampleI312E110 resultI312E110
    , testCase "I312E111"  $ assertAllEqTo exampleI312E111 resultI312E111
    , testCase "I312E112"  $ assertAllEqTo exampleI312E112 resultI312E112
    , testCase "I312E200"  $ assertAllEqTo exampleI312E200 resultI312E200
    , testCase "I312E201"  $ assertAllEqTo exampleI312E201 resultI312E201
    , testCase "I312E202"  $ assertAllEqTo exampleI312E202 resultI312E202
    , testCase "I312E210"  $ assertAllEqTo exampleI312E210 resultI312E210
    , testCase "I312E211"  $ assertAllEqTo exampleI312E211 resultI312E211
    , testCase "I312E212"  $ assertAllEqTo exampleI312E212 resultI312E212
    , testCase "I312E300"  $ assertAllEqTo exampleI312E300 resultI312E300
    , testCase "I312E301"  $ assertAllEqTo exampleI312E301 resultI312E301
    , testCase "I312E302"  $ assertAllEqTo exampleI312E302 resultI312E302
    , testCase "I312E310"  $ assertAllEqTo exampleI312E310 resultI312E310
    , testCase "I312E311"  $ assertAllEqTo exampleI312E311 resultI312E311
    , testCase "I312E312"  $ assertAllEqTo exampleI312E312 resultI312E312
    , testCase "I313E000"  $ assertAllEqTo exampleI313E000 resultI313E000
    , testCase "I313E001"  $ assertAllEqTo exampleI313E001 resultI313E001
    , testCase "I313E002"  $ assertAllEqTo exampleI313E002 resultI313E002
    , testCase "I313E003"  $ assertAllEqTo exampleI313E003 resultI313E003
    , testCase "I313E010"  $ assertAllEqTo exampleI313E010 resultI313E010
    , testCase "I313E011"  $ assertAllEqTo exampleI313E011 resultI313E011
    , testCase "I313E012"  $ assertAllEqTo exampleI313E012 resultI313E012
    , testCase "I313E013"  $ assertAllEqTo exampleI313E013 resultI313E013
    , testCase "I313E100"  $ assertAllEqTo exampleI313E100 resultI313E100
    , testCase "I313E101"  $ assertAllEqTo exampleI313E101 resultI313E101
    , testCase "I313E102"  $ assertAllEqTo exampleI313E102 resultI313E102
    , testCase "I313E103"  $ assertAllEqTo exampleI313E103 resultI313E103
    , testCase "I313E110"  $ assertAllEqTo exampleI313E110 resultI313E110
    , testCase "I313E111"  $ assertAllEqTo exampleI313E111 resultI313E111
    , testCase "I313E112"  $ assertAllEqTo exampleI313E112 resultI313E112
    , testCase "I313E113"  $ assertAllEqTo exampleI313E113 resultI313E113
    , testCase "I313E200"  $ assertAllEqTo exampleI313E200 resultI313E200
    , testCase "I313E201"  $ assertAllEqTo exampleI313E201 resultI313E201
    , testCase "I313E202"  $ assertAllEqTo exampleI313E202 resultI313E202
    , testCase "I313E203"  $ assertAllEqTo exampleI313E203 resultI313E203
    , testCase "I313E210"  $ assertAllEqTo exampleI313E210 resultI313E210
    , testCase "I313E211"  $ assertAllEqTo exampleI313E211 resultI313E211
    , testCase "I313E212"  $ assertAllEqTo exampleI313E212 resultI313E212
    , testCase "I313E213"  $ assertAllEqTo exampleI313E213 resultI313E213
    , testCase "I313E300"  $ assertAllEqTo exampleI313E300 resultI313E300
    , testCase "I313E301"  $ assertAllEqTo exampleI313E301 resultI313E301
    , testCase "I313E302"  $ assertAllEqTo exampleI313E302 resultI313E302
    , testCase "I313E303"  $ assertAllEqTo exampleI313E303 resultI313E303
    , testCase "I313E310"  $ assertAllEqTo exampleI313E310 resultI313E310
    , testCase "I313E311"  $ assertAllEqTo exampleI313E311 resultI313E311
    , testCase "I313E312"  $ assertAllEqTo exampleI313E312 resultI313E312
    , testCase "I313E313"  $ assertAllEqTo exampleI313E313 resultI313E313
    , testCase "I321E000"  $ assertAllEqTo exampleI321E000 resultI321E000
    , testCase "I321E001"  $ assertAllEqTo exampleI321E001 resultI321E001
    , testCase "I321E010"  $ assertAllEqTo exampleI321E010 resultI321E010
    , testCase "I321E011"  $ assertAllEqTo exampleI321E011 resultI321E011
    , testCase "I321E020"  $ assertAllEqTo exampleI321E020 resultI321E020
    , testCase "I321E021"  $ assertAllEqTo exampleI321E021 resultI321E021
    , testCase "I321E100"  $ assertAllEqTo exampleI321E100 resultI321E100
    , testCase "I321E101"  $ assertAllEqTo exampleI321E101 resultI321E101
    , testCase "I321E110"  $ assertAllEqTo exampleI321E110 resultI321E110
    , testCase "I321E111"  $ assertAllEqTo exampleI321E111 resultI321E111
    , testCase "I321E120"  $ assertAllEqTo exampleI321E120 resultI321E120
    , testCase "I321E121"  $ assertAllEqTo exampleI321E121 resultI321E121
    , testCase "I321E200"  $ assertAllEqTo exampleI321E200 resultI321E200
    , testCase "I321E201"  $ assertAllEqTo exampleI321E201 resultI321E201
    , testCase "I321E210"  $ assertAllEqTo exampleI321E210 resultI321E210
    , testCase "I321E211"  $ assertAllEqTo exampleI321E211 resultI321E211
    , testCase "I321E220"  $ assertAllEqTo exampleI321E220 resultI321E220
    , testCase "I321E221"  $ assertAllEqTo exampleI321E221 resultI321E221
    , testCase "I321E300"  $ assertAllEqTo exampleI321E300 resultI321E300
    , testCase "I321E301"  $ assertAllEqTo exampleI321E301 resultI321E301
    , testCase "I321E310"  $ assertAllEqTo exampleI321E310 resultI321E310
    , testCase "I321E311"  $ assertAllEqTo exampleI321E311 resultI321E311
    , testCase "I321E320"  $ assertAllEqTo exampleI321E320 resultI321E320
    , testCase "I321E321"  $ assertAllEqTo exampleI321E321 resultI321E321
    -- , testCase "I322E000"  $ assertAllEqTo exampleI322E000 resultI322E000
    -- , testCase "I322E001"  $ assertAllEqTo exampleI322E001 resultI322E001
    -- , testCase "I322E002"  $ assertAllEqTo exampleI322E002 resultI322E002
    -- , testCase "I322E010"  $ assertAllEqTo exampleI322E010 resultI322E010
    -- , testCase "I322E011"  $ assertAllEqTo exampleI322E011 resultI322E011
    -- , testCase "I322E012"  $ assertAllEqTo exampleI322E012 resultI322E012
    -- , testCase "I322E020"  $ assertAllEqTo exampleI322E020 resultI322E020
    -- , testCase "I322E021"  $ assertAllEqTo exampleI322E021 resultI322E021
    -- , testCase "I322E022"  $ assertAllEqTo exampleI322E022 resultI322E022
    -- , testCase "I322E100"  $ assertAllEqTo exampleI322E100 resultI322E100
    -- , testCase "I322E101"  $ assertAllEqTo exampleI322E101 resultI322E101
    -- , testCase "I322E102"  $ assertAllEqTo exampleI322E102 resultI322E102
    -- , testCase "I322E110"  $ assertAllEqTo exampleI322E110 resultI322E110
    -- , testCase "I322E111"  $ assertAllEqTo exampleI322E111 resultI322E111
    -- , testCase "I322E112"  $ assertAllEqTo exampleI322E112 resultI322E112
    -- , testCase "I322E120"  $ assertAllEqTo exampleI322E120 resultI322E120
    -- , testCase "I322E121"  $ assertAllEqTo exampleI322E121 resultI322E121
    -- , testCase "I322E122"  $ assertAllEqTo exampleI322E122 resultI322E122
    -- , testCase "I322E200"  $ assertAllEqTo exampleI322E200 resultI322E200
    -- , testCase "I322E201"  $ assertAllEqTo exampleI322E201 resultI322E201
    -- , testCase "I322E202"  $ assertAllEqTo exampleI322E202 resultI322E202
    -- , testCase "I322E210"  $ assertAllEqTo exampleI322E210 resultI322E210
    -- , testCase "I322E211"  $ assertAllEqTo exampleI322E211 resultI322E211
    -- , testCase "I322E212"  $ assertAllEqTo exampleI322E212 resultI322E212
    -- , testCase "I322E220"  $ assertAllEqTo exampleI322E220 resultI322E220
    -- , testCase "I322E221"  $ assertAllEqTo exampleI322E221 resultI322E221
    -- , testCase "I322E222"  $ assertAllEqTo exampleI322E222 resultI322E222
    -- , testCase "I322E300"  $ assertAllEqTo exampleI322E300 resultI322E300
    -- , testCase "I322E301"  $ assertAllEqTo exampleI322E301 resultI322E301
    -- , testCase "I322E302"  $ assertAllEqTo exampleI322E302 resultI322E302
    -- , testCase "I322E310"  $ assertAllEqTo exampleI322E310 resultI322E310
    -- , testCase "I322E311"  $ assertAllEqTo exampleI322E311 resultI322E311
    -- , testCase "I322E312"  $ assertAllEqTo exampleI322E312 resultI322E312
    -- , testCase "I322E320"  $ assertAllEqTo exampleI322E320 resultI322E320
    -- , testCase "I322E321"  $ assertAllEqTo exampleI322E321 resultI322E321
    -- , testCase "I322E322"  $ assertAllEqTo exampleI322E322 resultI322E322
    -- , testCase "I323E000"  $ assertAllEqTo exampleI323E000 resultI323E000
    -- , testCase "I323E001"  $ assertAllEqTo exampleI323E001 resultI323E001
    -- , testCase "I323E002"  $ assertAllEqTo exampleI323E002 resultI323E002
    -- , testCase "I323E003"  $ assertAllEqTo exampleI323E003 resultI323E003
    -- , testCase "I323E010"  $ assertAllEqTo exampleI323E010 resultI323E010
    -- , testCase "I323E011"  $ assertAllEqTo exampleI323E011 resultI323E011
    -- , testCase "I323E012"  $ assertAllEqTo exampleI323E012 resultI323E012
    -- , testCase "I323E013"  $ assertAllEqTo exampleI323E013 resultI323E013
    -- , testCase "I323E020"  $ assertAllEqTo exampleI323E020 resultI323E020
    -- , testCase "I323E021"  $ assertAllEqTo exampleI323E021 resultI323E021
    -- , testCase "I323E022"  $ assertAllEqTo exampleI323E022 resultI323E022
    -- , testCase "I323E023"  $ assertAllEqTo exampleI323E023 resultI323E023
    -- , testCase "I323E100"  $ assertAllEqTo exampleI323E100 resultI323E100
    -- , testCase "I323E101"  $ assertAllEqTo exampleI323E101 resultI323E101
    -- , testCase "I323E102"  $ assertAllEqTo exampleI323E102 resultI323E102
    -- , testCase "I323E103"  $ assertAllEqTo exampleI323E103 resultI323E103
    -- , testCase "I323E110"  $ assertAllEqTo exampleI323E110 resultI323E110
    -- , testCase "I323E111"  $ assertAllEqTo exampleI323E111 resultI323E111
    -- , testCase "I323E112"  $ assertAllEqTo exampleI323E112 resultI323E112
    -- , testCase "I323E113"  $ assertAllEqTo exampleI323E113 resultI323E113
    -- , testCase "I323E120"  $ assertAllEqTo exampleI323E120 resultI323E120
    -- , testCase "I323E121"  $ assertAllEqTo exampleI323E121 resultI323E121
    -- , testCase "I323E122"  $ assertAllEqTo exampleI323E122 resultI323E122
    -- , testCase "I323E123"  $ assertAllEqTo exampleI323E123 resultI323E123
    -- , testCase "I323E200"  $ assertAllEqTo exampleI323E200 resultI323E200
    -- , testCase "I323E201"  $ assertAllEqTo exampleI323E201 resultI323E201
    -- , testCase "I323E202"  $ assertAllEqTo exampleI323E202 resultI323E202
    -- , testCase "I323E203"  $ assertAllEqTo exampleI323E203 resultI323E203
    -- , testCase "I323E210"  $ assertAllEqTo exampleI323E210 resultI323E210
    -- , testCase "I323E211"  $ assertAllEqTo exampleI323E211 resultI323E211
    -- , testCase "I323E212"  $ assertAllEqTo exampleI323E212 resultI323E212
    -- , testCase "I323E213"  $ assertAllEqTo exampleI323E213 resultI323E213
    -- , testCase "I323E220"  $ assertAllEqTo exampleI323E220 resultI323E220
    -- , testCase "I323E221"  $ assertAllEqTo exampleI323E221 resultI323E221
    -- , testCase "I323E222"  $ assertAllEqTo exampleI323E222 resultI323E222
    -- , testCase "I323E223"  $ assertAllEqTo exampleI323E223 resultI323E223
    -- , testCase "I323E300"  $ assertAllEqTo exampleI323E300 resultI323E300
    -- , testCase "I323E301"  $ assertAllEqTo exampleI323E301 resultI323E301
    -- , testCase "I323E302"  $ assertAllEqTo exampleI323E302 resultI323E302
    -- , testCase "I323E303"  $ assertAllEqTo exampleI323E303 resultI323E303
    -- , testCase "I323E310"  $ assertAllEqTo exampleI323E310 resultI323E310
    -- , testCase "I323E311"  $ assertAllEqTo exampleI323E311 resultI323E311
    -- , testCase "I323E312"  $ assertAllEqTo exampleI323E312 resultI323E312
    -- , testCase "I323E313"  $ assertAllEqTo exampleI323E313 resultI323E313
    -- , testCase "I323E320"  $ assertAllEqTo exampleI323E320 resultI323E320
    -- , testCase "I323E321"  $ assertAllEqTo exampleI323E321 resultI323E321
    -- , testCase "I323E322"  $ assertAllEqTo exampleI323E322 resultI323E322
    -- , testCase "I323E323"  $ assertAllEqTo exampleI323E323 resultI323E323
    -- , testCase "I331E000"  $ assertAllEqTo exampleI331E000 resultI331E000
    -- , testCase "I331E001"  $ assertAllEqTo exampleI331E001 resultI331E001
    -- , testCase "I331E010"  $ assertAllEqTo exampleI331E010 resultI331E010
    -- , testCase "I331E011"  $ assertAllEqTo exampleI331E011 resultI331E011
    -- , testCase "I331E020"  $ assertAllEqTo exampleI331E020 resultI331E020
    -- , testCase "I331E021"  $ assertAllEqTo exampleI331E021 resultI331E021
    -- , testCase "I331E030"  $ assertAllEqTo exampleI331E030 resultI331E030
    -- , testCase "I331E031"  $ assertAllEqTo exampleI331E031 resultI331E031
    -- , testCase "I331E100"  $ assertAllEqTo exampleI331E100 resultI331E100
    -- , testCase "I331E101"  $ assertAllEqTo exampleI331E101 resultI331E101
    -- , testCase "I331E110"  $ assertAllEqTo exampleI331E110 resultI331E110
    -- , testCase "I331E111"  $ assertAllEqTo exampleI331E111 resultI331E111
    -- , testCase "I331E120"  $ assertAllEqTo exampleI331E120 resultI331E120
    -- , testCase "I331E121"  $ assertAllEqTo exampleI331E121 resultI331E121
    -- , testCase "I331E130"  $ assertAllEqTo exampleI331E130 resultI331E130
    -- , testCase "I331E131"  $ assertAllEqTo exampleI331E131 resultI331E131
    -- , testCase "I331E200"  $ assertAllEqTo exampleI331E200 resultI331E200
    -- , testCase "I331E201"  $ assertAllEqTo exampleI331E201 resultI331E201
    -- , testCase "I331E210"  $ assertAllEqTo exampleI331E210 resultI331E210
    -- , testCase "I331E211"  $ assertAllEqTo exampleI331E211 resultI331E211
    -- , testCase "I331E220"  $ assertAllEqTo exampleI331E220 resultI331E220
    -- , testCase "I331E221"  $ assertAllEqTo exampleI331E221 resultI331E221
    -- , testCase "I331E230"  $ assertAllEqTo exampleI331E230 resultI331E230
    -- , testCase "I331E231"  $ assertAllEqTo exampleI331E231 resultI331E231
    -- , testCase "I331E300"  $ assertAllEqTo exampleI331E300 resultI331E300
    -- , testCase "I331E301"  $ assertAllEqTo exampleI331E301 resultI331E301
    -- , testCase "I331E310"  $ assertAllEqTo exampleI331E310 resultI331E310
    -- , testCase "I331E311"  $ assertAllEqTo exampleI331E311 resultI331E311
    -- , testCase "I331E320"  $ assertAllEqTo exampleI331E320 resultI331E320
    -- , testCase "I331E321"  $ assertAllEqTo exampleI331E321 resultI331E321
    -- , testCase "I331E330"  $ assertAllEqTo exampleI331E330 resultI331E330
    -- , testCase "I331E331"  $ assertAllEqTo exampleI331E331 resultI331E331
    -- , testCase "I332E000"  $ assertAllEqTo exampleI332E000 resultI332E000
    -- , testCase "I332E001"  $ assertAllEqTo exampleI332E001 resultI332E001
    -- , testCase "I332E002"  $ assertAllEqTo exampleI332E002 resultI332E002
    -- , testCase "I332E010"  $ assertAllEqTo exampleI332E010 resultI332E010
    -- , testCase "I332E011"  $ assertAllEqTo exampleI332E011 resultI332E011
    -- , testCase "I332E012"  $ assertAllEqTo exampleI332E012 resultI332E012
    -- , testCase "I332E020"  $ assertAllEqTo exampleI332E020 resultI332E020
    -- , testCase "I332E021"  $ assertAllEqTo exampleI332E021 resultI332E021
    -- , testCase "I332E022"  $ assertAllEqTo exampleI332E022 resultI332E022
    -- , testCase "I332E030"  $ assertAllEqTo exampleI332E030 resultI332E030
    -- , testCase "I332E031"  $ assertAllEqTo exampleI332E031 resultI332E031
    -- , testCase "I332E032"  $ assertAllEqTo exampleI332E032 resultI332E032
    -- , testCase "I332E100"  $ assertAllEqTo exampleI332E100 resultI332E100
    -- , testCase "I332E101"  $ assertAllEqTo exampleI332E101 resultI332E101
    -- , testCase "I332E102"  $ assertAllEqTo exampleI332E102 resultI332E102
    -- , testCase "I332E110"  $ assertAllEqTo exampleI332E110 resultI332E110
    -- , testCase "I332E111"  $ assertAllEqTo exampleI332E111 resultI332E111
    -- , testCase "I332E112"  $ assertAllEqTo exampleI332E112 resultI332E112
    -- , testCase "I332E120"  $ assertAllEqTo exampleI332E120 resultI332E120
    -- , testCase "I332E121"  $ assertAllEqTo exampleI332E121 resultI332E121
    -- , testCase "I332E122"  $ assertAllEqTo exampleI332E122 resultI332E122
    -- , testCase "I332E130"  $ assertAllEqTo exampleI332E130 resultI332E130
    -- , testCase "I332E131"  $ assertAllEqTo exampleI332E131 resultI332E131
    -- , testCase "I332E132"  $ assertAllEqTo exampleI332E132 resultI332E132
    -- , testCase "I332E200"  $ assertAllEqTo exampleI332E200 resultI332E200
    -- , testCase "I332E201"  $ assertAllEqTo exampleI332E201 resultI332E201
    -- , testCase "I332E202"  $ assertAllEqTo exampleI332E202 resultI332E202
    -- , testCase "I332E210"  $ assertAllEqTo exampleI332E210 resultI332E210
    -- , testCase "I332E211"  $ assertAllEqTo exampleI332E211 resultI332E211
    -- , testCase "I332E212"  $ assertAllEqTo exampleI332E212 resultI332E212
    -- , testCase "I332E220"  $ assertAllEqTo exampleI332E220 resultI332E220
    -- , testCase "I332E221"  $ assertAllEqTo exampleI332E221 resultI332E221
    -- , testCase "I332E222"  $ assertAllEqTo exampleI332E222 resultI332E222
    -- , testCase "I332E230"  $ assertAllEqTo exampleI332E230 resultI332E230
    -- , testCase "I332E231"  $ assertAllEqTo exampleI332E231 resultI332E231
    -- , testCase "I332E232"  $ assertAllEqTo exampleI332E232 resultI332E232
    -- , testCase "I332E300"  $ assertAllEqTo exampleI332E300 resultI332E300
    -- , testCase "I332E301"  $ assertAllEqTo exampleI332E301 resultI332E301
    -- , testCase "I332E302"  $ assertAllEqTo exampleI332E302 resultI332E302
    -- , testCase "I332E310"  $ assertAllEqTo exampleI332E310 resultI332E310
    -- , testCase "I332E311"  $ assertAllEqTo exampleI332E311 resultI332E311
    -- , testCase "I332E312"  $ assertAllEqTo exampleI332E312 resultI332E312
    -- , testCase "I332E320"  $ assertAllEqTo exampleI332E320 resultI332E320
    -- , testCase "I332E321"  $ assertAllEqTo exampleI332E321 resultI332E321
    -- , testCase "I332E322"  $ assertAllEqTo exampleI332E322 resultI332E322
    -- , testCase "I332E330"  $ assertAllEqTo exampleI332E330 resultI332E330
    -- , testCase "I332E331"  $ assertAllEqTo exampleI332E331 resultI332E331
    -- , testCase "I332E332"  $ assertAllEqTo exampleI332E332 resultI332E332
    -- , testCase "I333E000"  $ assertAllEqTo exampleI333E000 resultI333E000
    -- , testCase "I333E001"  $ assertAllEqTo exampleI333E001 resultI333E001
    -- , testCase "I333E002"  $ assertAllEqTo exampleI333E002 resultI333E002
    -- , testCase "I333E003"  $ assertAllEqTo exampleI333E003 resultI333E003
    -- , testCase "I333E010"  $ assertAllEqTo exampleI333E010 resultI333E010
    -- , testCase "I333E011"  $ assertAllEqTo exampleI333E011 resultI333E011
    -- , testCase "I333E012"  $ assertAllEqTo exampleI333E012 resultI333E012
    -- , testCase "I333E013"  $ assertAllEqTo exampleI333E013 resultI333E013
    -- , testCase "I333E020"  $ assertAllEqTo exampleI333E020 resultI333E020
    -- , testCase "I333E021"  $ assertAllEqTo exampleI333E021 resultI333E021
    -- , testCase "I333E022"  $ assertAllEqTo exampleI333E022 resultI333E022
    -- , testCase "I333E023"  $ assertAllEqTo exampleI333E023 resultI333E023
    -- , testCase "I333E030"  $ assertAllEqTo exampleI333E030 resultI333E030
    -- , testCase "I333E031"  $ assertAllEqTo exampleI333E031 resultI333E031
    -- , testCase "I333E032"  $ assertAllEqTo exampleI333E032 resultI333E032
    -- , testCase "I333E033"  $ assertAllEqTo exampleI333E033 resultI333E033
    -- , testCase "I333E100"  $ assertAllEqTo exampleI333E100 resultI333E100
    -- , testCase "I333E101"  $ assertAllEqTo exampleI333E101 resultI333E101
    -- , testCase "I333E102"  $ assertAllEqTo exampleI333E102 resultI333E102
    -- , testCase "I333E103"  $ assertAllEqTo exampleI333E103 resultI333E103
    -- , testCase "I333E110"  $ assertAllEqTo exampleI333E110 resultI333E110
    -- , testCase "I333E111"  $ assertAllEqTo exampleI333E111 resultI333E111
    -- , testCase "I333E112"  $ assertAllEqTo exampleI333E112 resultI333E112
    -- , testCase "I333E113"  $ assertAllEqTo exampleI333E113 resultI333E113
    -- , testCase "I333E120"  $ assertAllEqTo exampleI333E120 resultI333E120
    -- , testCase "I333E121"  $ assertAllEqTo exampleI333E121 resultI333E121
    -- , testCase "I333E122"  $ assertAllEqTo exampleI333E122 resultI333E122
    -- , testCase "I333E123"  $ assertAllEqTo exampleI333E123 resultI333E123
    -- , testCase "I333E130"  $ assertAllEqTo exampleI333E130 resultI333E130
    -- , testCase "I333E131"  $ assertAllEqTo exampleI333E131 resultI333E131
    -- , testCase "I333E132"  $ assertAllEqTo exampleI333E132 resultI333E132
    -- , testCase "I333E133"  $ assertAllEqTo exampleI333E133 resultI333E133
    -- , testCase "I333E200"  $ assertAllEqTo exampleI333E200 resultI333E200
    -- , testCase "I333E201"  $ assertAllEqTo exampleI333E201 resultI333E201
    -- , testCase "I333E202"  $ assertAllEqTo exampleI333E202 resultI333E202
    -- , testCase "I333E203"  $ assertAllEqTo exampleI333E203 resultI333E203
    -- , testCase "I333E210"  $ assertAllEqTo exampleI333E210 resultI333E210
    -- , testCase "I333E211"  $ assertAllEqTo exampleI333E211 resultI333E211
    -- , testCase "I333E212"  $ assertAllEqTo exampleI333E212 resultI333E212
    -- , testCase "I333E213"  $ assertAllEqTo exampleI333E213 resultI333E213
    -- , testCase "I333E220"  $ assertAllEqTo exampleI333E220 resultI333E220
    -- , testCase "I333E221"  $ assertAllEqTo exampleI333E221 resultI333E221
    -- , testCase "I333E222"  $ assertAllEqTo exampleI333E222 resultI333E222
    -- , testCase "I333E223"  $ assertAllEqTo exampleI333E223 resultI333E223
    -- , testCase "I333E230"  $ assertAllEqTo exampleI333E230 resultI333E230
    -- , testCase "I333E231"  $ assertAllEqTo exampleI333E231 resultI333E231
    -- , testCase "I333E232"  $ assertAllEqTo exampleI333E232 resultI333E232
    -- , testCase "I333E233"  $ assertAllEqTo exampleI333E233 resultI333E233
    -- , testCase "I333E300"  $ assertAllEqTo exampleI333E300 resultI333E300
    -- , testCase "I333E301"  $ assertAllEqTo exampleI333E301 resultI333E301
    -- , testCase "I333E302"  $ assertAllEqTo exampleI333E302 resultI333E302
    -- , testCase "I333E303"  $ assertAllEqTo exampleI333E303 resultI333E303
    -- , testCase "I333E310"  $ assertAllEqTo exampleI333E310 resultI333E310
    -- , testCase "I333E311"  $ assertAllEqTo exampleI333E311 resultI333E311
    -- , testCase "I333E312"  $ assertAllEqTo exampleI333E312 resultI333E312
    -- , testCase "I333E313"  $ assertAllEqTo exampleI333E313 resultI333E313
    -- , testCase "I333E320"  $ assertAllEqTo exampleI333E320 resultI333E320
    -- , testCase "I333E321"  $ assertAllEqTo exampleI333E321 resultI333E321
    -- , testCase "I333E322"  $ assertAllEqTo exampleI333E322 resultI333E322
    -- , testCase "I333E323"  $ assertAllEqTo exampleI333E323 resultI333E323
    -- , testCase "I333E330"  $ assertAllEqTo exampleI333E330 resultI333E330
    -- , testCase "I333E331"  $ assertAllEqTo exampleI333E331 resultI333E331
    -- , testCase "I333E332"  $ assertAllEqTo exampleI333E332 resultI333E332
    -- , testCase "I333E333"  $ assertAllEqTo exampleI333E333 resultI333E333
    ]
  ]

testAllEq :: Text -> Property
testAllEq x =
  let
    ls = textToLayouts x
  in
    counterexample (show (Layouts ls)) ((=== True) . allEq $ ls)

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
  --   testCase "F1"  $ assertAllEq exampleF1
  -- , testCase "F2"  $ assertAllEq exampleF2
  -- , testCase "F3"  $ assertAllEq exampleF3
  -- , testCase "F4"  $ assertAllEq exampleF4
  -- , testCase "F5"  $ assertAllEq exampleF5
  -- , testCase "F6"  $ assertAllEq exampleF6
  -- , testCase "F7"  $ assertAllEq exampleF7
  -- , testCase "F8"  $ assertAllEq exampleF8
  -- , testCase "F9"  $ assertAllEq exampleF9
  -- , testCase "F10" $ assertAllEq exampleF10
  -- , testCase "E1"  $ assertAllEq exampleE1
  -- , testCase "E2"  $ assertAllEq exampleE2
  -- , testCase "E3"  $ assertAllEq exampleE3
  -- , testCase "E4"  $ assertAllEq exampleE4
  -- , testCase "E5"  $ assertAllEq exampleE5
  -- , testCase "E6"  $ assertAllEq exampleE6
  -- , testCase "E7"  $ assertAllEq exampleE7
  -- , testCase "E8"  $ assertAllEq exampleE8
  -- , testCase "E9"  $ assertAllEq exampleE9
  -- , testCase "E10"  $ assertAllEq exampleE10
  -- ,  testCase "E11"  $ assertAllEq exampleE11
    testProperty "all eq (no do, no errors)" $ testAllEq . modelLinesToText
  , testProperty "deltas (no do, no errors)" $ testDeltas . modelLinesToText
  , testProperty "all eq (with do, no errors)" $ testAllEq . modelLinesWithDoToText
  , testProperty "deltas (with do, no errors)" $ testDeltas . modelLinesWithDoToText
  , testProperty "all eq (no do, with errors)" $ testAllEq . modelLinesWithErrorsToText
  , testProperty "deltas (no do, with errors)" $ testDeltas . modelLinesWithErrorsToText
  -- , testProperty "all eq (with do, with errors)" $ testAllEq . modelLinesWithDoAndErrorsToText
  -- , testProperty "deltas (with do, with errors)" $ testDeltas . modelLinesWithDoAndErrorsToText
  ]
