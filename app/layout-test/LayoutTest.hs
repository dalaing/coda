{-|
Copyright   : (c) 2018, Commonwealth Scientific and Industrial Research Organisation
License     : BSD3
Maintainer  : dave.laing.80@gmail.com
Stability   : experimental
Portability : non-portable
-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications #-}
module LayoutTest where

import Data.Char (isSpace)
import Data.Foldable
import Data.Text (Text)
import qualified Data.Text as Text
import qualified Data.Text.Unsafe as Text

import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.QuickCheck

import FingerTree hiding (Position)
import Syntax.Prefix
import Syntax.Token
import Syntax.Dyck
import Syntax.Rope
import Relative.Class
import Relative.Delta
import Language.Server.Protocol (Position(..))
import qualified Syntax.Lexer as Lex
import Syntax.Layout
import qualified Syntax.Parser as Parse

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
    fmap f [0..length ts - 1]

allEq :: Eq a => [a] -> Bool
allEq xs =
  and $ zipWith (==) xs (tail xs)

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

data ModelNoDoErrors =
    MNDESingleToken Text
  | MNDEMultiToken [(Int, Text, Text)]
  | MNDELines [ModelNoDoErrors]
  deriving (Eq, Ord)

modelNoDoErrorsToText :: ModelNoDoErrors -> Text
modelNoDoErrorsToText =
  modelNoDoErrorsToText' 0

modelNoDoErrorsToText' :: Int -> ModelNoDoErrors -> Text
modelNoDoErrorsToText' i (MNDESingleToken t) = Text.pack $
  replicate i ' ' ++ Text.unpack t ++ "\n"
modelNoDoErrorsToText' i (MNDEMultiToken xs) =  Text.pack $
  foldMap (\(j, k, t) -> replicate i ' ' ++ Text.unpack k ++ Text.unpack t ++ "\n") xs
modelNoDoErrorsToText' i (MNDELines xs) =
  foldMap (modelNoDoErrorsToText' i) xs

instance Show ModelNoDoErrors where
  show = Text.unpack . modelNoDoErrorsToText

instance Arbitrary ModelNoDoErrors where
  arbitrary =
    let
      genSingleToken =
        MNDESingleToken <$> elements ["one", "two", "three"]
      genMultiToken =
        let
          genMT1 =
            pure [(0, "", "foo")]
          genMT2 = do
            Indent i <- arbitrary
            pure [(0, "", "foo"), (i, Text.pack $ replicate i ' ', "bar")]
          genMT3a = do
            Indent i <- arbitrary
            Indent j <- arbitrary
            pure [ (0, "", "foo")
                 , (i, Text.pack $ replicate i ' ' ++ pure '\t', "bar")
                 , (i + j, Text.pack $ replicate (i + j) ' ' ++ pure '\t', "baz")
                 ]
          genMT3b = do
            Indent i <- arbitrary
            Indent j <- arbitrary
            pure [ (0, "", "foo")
                 , (i, Text.pack $ '\t' : replicate i ' ', "bar")
                 , (i + j, Text.pack $ '\t' : replicate (i + j) ' ', "baz")
                 ]
          genMT3c = do
            Indent i <- arbitrary
            Indent j <- arbitrary
            pure [ (0, "", "foo")
                 , (i, Text.pack $ " " <> replicate i ' ', "bar")
                 , (i + j, Text.pack $ " " <> replicate i ' ' ++ pure '\t' ++ replicate j ' ', "baz")
                 ]
        in
          MNDEMultiToken <$> oneof [genMT1, genMT2, genMT3a, genMT3b, genMT3c]
      genLines = sized $ \s -> do
        n <- choose (1, fromIntegral . floor . sqrt . fromIntegral $ s)
        xs <- sequence . replicate n . resize (s `div` n) $ arbitrary
        pure $ MNDELines xs
    in
      oneof [genSingleToken, genMultiToken, genLines]
  shrink (MNDESingleToken _) =
    []
  shrink (MNDEMultiToken [x]) =
    []
  shrink (MNDEMultiToken [x,y]) =
    [MNDEMultiToken [x]]
  shrink (MNDEMultiToken [x,y,z]) =
    [MNDEMultiToken [x,y]]
  shrink (MNDELines xs) =
    xs ++ (fmap MNDELines . filter (not . null) . shrinkList shrink $ xs)

data Model =
    SingleToken Text
  | MultiToken [(Int, Text)]
  | Do Int [Model]
  | Lines [Model]
  deriving (Eq, Ord)

modelToText :: Model -> Text
modelToText =
  modelToText' 0

modelToText' :: Int -> Model -> Text
modelToText' i (SingleToken t) = Text.pack $
  replicate i ' ' ++ Text.unpack t ++ "\n"
modelToText' i (MultiToken xs) =  Text.pack $
  foldMap (\(j, t) -> replicate (i + j) ' ' ++ Text.unpack t ++ "\n") xs
modelToText' i (Do j xs) = Text.pack $
  replicate i ' ' ++ "do\n" ++ Text.unpack (foldMap (modelToText' (i + j)) xs)
modelToText' i (Lines xs) =
  foldMap (modelToText' i) xs

instance Show Model where
  show = Text.unpack . modelToText

genSingleToken :: Gen Model
genSingleToken =
  SingleToken <$> elements ["one", "two", "three"]

genMultiToken :: Gen Model
genMultiToken =
  let
    genMT1 =
      pure [(0, "foo")]
    genMT2 = do
      Indent i <- arbitrary
      pure [(0, "foo"), (i, "bar")]
    genMT3 = do
      Indent i <- arbitrary
      Indent j <- arbitrary
      pure [(0, "foo"), (i, "bar"), (i + j, "baz")]
  in
    MultiToken <$> oneof [genMT1, genMT2, genMT3]

genDo :: Gen Model
genDo = sized $ \s -> do
  Indent i <- arbitrary
  n <- choose (1, fromIntegral . floor . sqrt . fromIntegral $ s)
  xs <- sequence . replicate n . resize (s `div` n) $ arbitrary
  pure $ Do i xs

genLines :: Gen Model
genLines = sized $ \s -> do
  n <- choose (1, fromIntegral . floor . sqrt . fromIntegral $ s)
  xs <- sequence . replicate n . resize (s `div` n) $ arbitrary
  pure $ Lines xs

instance Arbitrary Model where
  arbitrary =
    -- oneof [genSingleToken, genMultiToken, genLines]
    oneof [genSingleToken, genMultiToken, genDo, genLines]
  shrink (SingleToken _) =
    []
  shrink (MultiToken [x]) =
    []
  shrink (MultiToken [x,y]) =
    [MultiToken [x]]
  shrink (MultiToken [x,y,z]) =
    [MultiToken [x,y]]
  shrink (Do i xs) =
    xs ++ (fmap (Do i) . filter (not . null) . shrinkList shrink $ xs)
  shrink (Lines xs) =
    xs ++ (fmap Lines . filter (not . null) . shrinkList shrink $ xs)

test_layout :: TestTree
test_layout = testGroup "layout"
  [
    testProperty "all eq" $ allEq . textToLayouts . modelToText
  , testProperty "all eq nde" $ allEq . textToLayouts . modelNoDoErrorsToText
  , testCase "E1" $ True @=? (allEq . textToLayouts) exampleE1
  , testCase "E2" $ True @=? (allEq . textToLayouts) exampleE2
  , testCase "E3e" $ [] @=? textToLayouts exampleE3
  , testCase "E3" $ True @=? (allEq . textToLayouts) exampleE3
  , testCase "F1" $ True @=? (allEq . textToLayouts) exampleF1
  , testCase "F2" $ True @=? (allEq . textToLayouts) exampleF2
  , testCase "F3" $ True @=? (allEq . textToLayouts) exampleF3
  , testCase "F4" $ True @=? (allEq . textToLayouts) exampleF4
  -- , testCase "F5e" $ [] @=? textToLayouts exampleF5
  , testCase "F5" $ True @=? (allEq . textToLayouts) exampleF5
  ]
