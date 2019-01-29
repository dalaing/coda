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
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module LayoutTest where

import Control.Monad (replicateM)
import Data.Char (isSpace)
import Data.Foldable
import Data.Text (Text)
import qualified Data.Text as Text
import qualified Data.Text.Unsafe as Text

import Control.Lens hiding (elements)

import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.QuickCheck

import FingerTree hiding (Position)
import Syntax.Prefix
import Syntax.Token
import Syntax.Dyck
import Syntax.Rope
import Relative.Class
import Relative.Cat hiding (null)
import Relative.Delta
import Rev
import Language.Server.Protocol (Position(..))
import qualified Syntax.Lexer as Lex
import Syntax.Layout
import qualified Syntax.Parser as Parse

linesToLayouts :: Delta -> [Text] -> (Delta, [Layout])
linesToLayouts d0 ls =
  let
    f (d, ls) t =
      let dt = Delta . Text.lengthWord16 $ t
      in
        ( d <> dt
        , ls <> pure (dyckLayout dt (fromText t) (Lex.lex t))
        )
  in
    foldl' f (d0, mempty) ls

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
        fold ls1 <> fold ls2
  in
    fmap f [1..length ts - 1]

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
    n <- choose (0, 10)
    xs <- replicateM n arbitrary
    pure $ ModelLines xs
  shrink (ModelLines xs) =
    ModelLines <$> shrinkList (const []) xs

hasTab :: ModelLines -> Bool
hasTab (ModelLines ls) = any (Text.isInfixOf "\t" . _indent) ls

newtype ModelLinesWithErrors = ModelLinesWithErrors ModelLines
  deriving (Eq, Ord, Semigroup, Monoid)

modelLinesWithErrorsToText :: ModelLinesWithErrors -> Text
modelLinesWithErrorsToText (ModelLinesWithErrors ml) = modelLinesToText ml

instance Show ModelLinesWithErrors where
  show = Text.unpack . modelLinesWithErrorsToText

instance Arbitrary ModelLinesWithErrors where
  arbitrary = do
    ModelLines ls <- arbitrary
    let l1 = length ls
    if l1 == 0
    then pure $ ModelLinesWithErrors (ModelLines [])
    else do
      n <- choose (0, l1 - 1)
      let
        l = ls !! n
        l2 = Text.length (_indent l)
      m <- choose (0, l2 - 1)
      let ls' = ls & ix n . indent . ix m .~ '\t'
      pure $ ModelLinesWithErrors (ModelLines ls')
  shrink (ModelLinesWithErrors ml) =
    ModelLinesWithErrors <$> filter hasTab (shrink ml)

data ModelLinesWithDo =
    MLWDLines ModelLines
  | MLWDDo Indent ModelLinesWithDo
  | MLWDTwo ModelLinesWithDo ModelLinesWithDo
  | MLWDThree ModelLinesWithDo ModelLinesWithDo ModelLinesWithDo
  deriving (Eq, Ord)

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
  arbitrary = sized genMLWD
  shrink (MLWDLines ml) = MLWDLines <$> shrink ml
  shrink (MLWDDo i ml) = ml : (MLWDDo i <$> shrink ml)
  shrink (MLWDTwo m1 m2) = m1 : m2 : [MLWDTwo n1 n2 | (n1, n2) <- shrink (m1, m2)]
  shrink (MLWDThree m1 m2 m3) = m1 : m2 : m3 : [MLWDThree n1 n2 n3 | (n1, n2, n3) <- shrink (m1, m2, m3)]

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

test_layout :: TestTree
test_layout = testGroup "layout"
  [
    testCase "F1" $ True @=? (allEq . textToLayouts) exampleF1
  , testCase "F2" $ True @=? (allEq . textToLayouts) exampleF2
  , testCase "F3" $ True @=? (allEq . textToLayouts) exampleF3
  , testCase "F4" $ True @=? (allEq . textToLayouts) exampleF4
  , testCase "F5" $ True @=? (allEq . textToLayouts) exampleF5
  , testCase "F6" $ True @=? (allEq . textToLayouts) exampleF6
  , testCase "F7" $ True @=? (allEq . textToLayouts) exampleF7
  , testCase "F8" $ True @=? (allEq . textToLayouts) exampleF8
  , testCase "F9" $ True @=? (allEq . textToLayouts) exampleF9
  , testCase "F10" $ True @=? (allEq . textToLayouts) exampleF10
  -- , testCase "F10e" $ Layouts [] @=? Layouts (textToLayouts exampleF10)
  , testCase "E1" $ True @=? (allEq . textToLayouts) exampleE1
  -- , testCase "E1e" $ Layouts [] @=? Layouts (textToLayouts exampleE1)
  , testCase "E2" $ True @=? (allEq . textToLayouts) exampleE2
  -- , testCase "E2e" $ Layouts [] @=? Layouts (textToLayouts exampleE2)
  , testCase "E3" $ True @=? (allEq . textToLayouts) exampleE3
  , testCase "E3e" $ Layouts [] @=? Layouts (textToLayouts exampleE3)
  , testProperty "all eq (no do, no errors)" $ allEq . textToLayouts . modelLinesToText
  , testProperty "all eq (with do, no errors)" $ allEq . textToLayouts . modelLinesWithDoToText
  , testProperty "all eq (no do, with errors)" $ allEq . textToLayouts . modelLinesWithErrorsToText
  ]
