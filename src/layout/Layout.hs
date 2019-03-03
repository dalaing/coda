{-# language CPP #-}
{-# language OverloadedLists #-}
{-# language LambdaCase #-}
{-# OPTIONS_GHC -Wno-incomplete-patterns #-}
module Layout where

import Control.Lens

#if __GLASGOW_HASKELL__ < 804
import Data.Semigroup
#endif

import Relative.Class
import Relative.Delta
import Relative.Cat as Cat
import Rev
import Syntax.Prefix

import Dyck

import Debug.Trace

data LayoutMismatch = LayoutMismatch !Delta !Prefix !Prefix
  deriving (Eq, Show) -- this is for debugging the Layout Monoid

instance Relative LayoutMismatch where
  rel d (LayoutMismatch d' p q) = LayoutMismatch (d <> d') p q

-- The first Prefix is the lowest indent that covers the whole run
-- The second Prefix is the indent that covers the last line we've seend
data Run = Run {-# unpack #-} !Prefix !(Cat Dyck) {-# unpack #-} !Dyck !(Cat LayoutMismatch) !Prefix
  deriving (Eq, Show) -- this is for debugging the Layout Monoid

-- is it guaranteed that all of a `Run` should be parsed the same?
-- No NonDecreasingIndentation thingamo?
-- should I ever need to switch between the LayoutMode parsers?

instance Relative Run where
  rel d (Run p ds ts es pr) = Run p (rel d ds) (rel d ts) (rel d es) pr

runDyck :: Run -> Dyck
runDyck (Run _ _ ts _ _) = ts

runsDyck :: Cat Run -> Dyck
runsDyck Empty = Empty
runsDyck (x :< xs) = runDyck x <> runsDyck xs

instance HasPrefix Run where
  prefix (Run p _ _ _ _) = p

runDycks :: Run -> Cat Dyck
runDycks (Run _ ds _ _ _) = ds

runsDycks :: Cat Run -> Cat Dyck
runsDycks Empty = Empty
runsDycks (x :< xs) = runDycks x <> runsDycks xs

runMismatch :: Run -> Cat LayoutMismatch
runMismatch (Run _ _ _ es _) = es

runsMismatch :: Cat Run -> Cat LayoutMismatch
runsMismatch Empty = Empty
runsMismatch (x :< xs) = runMismatch x <> runsMismatch xs

data Layout
  = E {-# unpack #-} !Delta
  | S {-# unpack #-} !Delta {-# unpack #-} !Run
  -- It might be worth adding a Cat Run after the Run for the middle of the V,
  -- to track things which have the same indent as the middle of the V.
  -- We can snoc to Cat Run, and if we need to reverse it to shuffle things it should
  -- be shorter than the rightmost part of the V in most cases.
  | V {-# unpack #-} !Delta !(Cat Run) {-# unpack #-} !Run !(Rev Cat Run)
  deriving (Eq, Show) -- this is for debugging the Layout Monoid

instance HasDelta Layout where
  delta (E d) = d
  delta (S d _) = d
  delta (V d _ _ _) = d

instance AsEmpty Layout where
  _Empty = prism (const $ E 0) $ \case
    E 0 -> Right ()
    x   -> Left x

dyckLayout :: Delta -> Prefix -> Dyck -> Layout
dyckLayout d _ Empty = E d
dyckLayout d p t = S d $ Run p [t] t [] p

gatherMismatches :: Layout -> Cat LayoutMismatch
gatherMismatches (E _) = Empty
gatherMismatches (S _ r) = runMismatch r
gatherMismatches (V _ l m (Rev r)) = runsMismatch l <> runMismatch m <> runsMismatch r

gatherMismatchPrefixes :: Cat LayoutMismatch -> [Prefix]
gatherMismatchPrefixes Empty = []
gatherMismatchPrefixes (LayoutMismatch _ p1 p2 :< lms) = p1 : p2 : gatherMismatchPrefixes lms

testMismatchPrefixes :: Prefix -> [Prefix] -> Bool
testMismatchPrefixes p = all $ \tp ->
  case joinAndCompare p tp of
    Right LT -> True
    _ -> False

hasMismatch :: Layout -> Bool
hasMismatch l =
  case gatherMismatches l of
    Empty -> False
    _ -> True

testMismatch :: Prefix -> Layout -> Bool
testMismatch p l = testMismatchPrefixes p (gatherMismatchPrefixes . gatherMismatches $ l)

-- this should almost certainly be revAppendCat :: Relative a => Cat a -> Cat a -> Cat a
revCat :: Relative a => Cat a -> Cat a
revCat Empty = Empty
revCat (x :< xs) = snocCat (revCat xs) x

runSnocMismatch :: LayoutMismatch -> Run -> Run
runSnocMismatch e (Run p ds ts es pr) = Run p ds ts (snocCat es e) pr

layout :: Either a b -> Prefix -> Prefix -> Run -> Run
layout (Right _) _ _ r = r
layout (Left _) pr p' r = layoutError pr p' r

layoutError :: Prefix -> Prefix -> Run -> Run
layoutError = layoutError' 0

layoutError' :: Delta -> Prefix -> Prefix -> Run -> Run
layoutError' d pr p' = runSnocMismatch (LayoutMismatch d pr p')

mergeRun :: Delta -> Run -> Run -> Run
mergeRun d (Run p ds ts es _) (Run _ ds' ts' es' pr') =
  Run p (ds <> rel d ds') (ts <> rel d ts') (es <> rel d es') pr'

-- TODO add a bool so we don't have to case on boring / not boring
shuffle :: Delta -> Run -> Cat Run -> Maybe Run -> Rev Cat Run -> (Run, Cat Run, Maybe Run, Rev Cat Run)
shuffle d m l' m' r' =
  let
    (m'', l''', m''', r''') = shuffle' d m l' m' (revCat (runRev r'))
  in
    (m'', l''', m''', Rev . revCat $ r''')

shuffle' :: Delta -> Run -> Cat Run -> Maybe Run -> Cat Run -> (Run, Cat Run, Maybe Run, Cat Run)
shuffle' d m@(Run p _ ts _ pr) l'@(lh'@(Run p' _ _ Empty _) :< lt') m' r' =
  case joinAndCompare pr p' of
    Left _ -> (m, layoutError pr p' lh' :< lt', m', r')
    Right LT | boring ts -> shuffle' d (mergeRun d m lh') lt' m' r'
    _ -> (m, l', m', r')
shuffle' d m@(Run p _ ts _ pr) Empty (Just m'@(Run p' _ _ Empty _)) r' =
  case joinAndCompare pr p' of
    Left _ -> (m, Empty, Just (layoutError pr p' m'), r')
    Right LT | boring ts -> shuffle' d (mergeRun d m m') Empty Nothing r'
    _ -> (m, Empty, Just m', r')
shuffle' d m@(Run p _ ts _ pr) Empty Nothing r'@(rh'@(Run p' _ _ Empty _) :< rt') =
  case joinAndCompare pr p' of
    Left _ -> (m, Empty, Nothing, layoutError pr p' rh' :< rt')
    Right LT | boring ts -> shuffle' d (mergeRun d m rh') Empty Nothing rt'
    _ -> (m, Empty, Nothing, r')
shuffle' _ m Empty Nothing Empty =
  (m, Empty, Nothing, Empty)
shuffle' _ m l' m' d' =
  (m, l', m', d')

collapse :: Layout -> Layout
collapse (V d Empty m Empty) = S d m
collapse x = x

-- TODO need another property, where we check that all text that can be collapsed is collapsed
-- shuffle is currently using pr, which may not do what we require there

instance Semigroup Layout where
  E 0 <> xs = xs
  xs <> E 0 = xs
  E d <> E d' = E (d <> d')
  E d <> S d' (Run p ds ts es pr) = S (d <> d') $ Run p (rel d ds) (rel d ts) (rel d es) pr
  E d <> V d' l m r = V (d <> d') (rel d l) (rel d m) (rel d r)
  S d m <> E d' = S (d <> d') m
  S d m@(Run p _ ts _ pr) <> S d' m'@(Run p' _ _ _ _) =
    case (joinAndCompare p p', joinAndCompare pr p') of
      (Left _, _) ->
        V (d <> d') Empty m (rel d . Rev . Cat.singleton . layoutError pr p' $ m')
      (Right LT, _) ->
        let (m_, _, m'_, _) = shuffle d m Empty (Just m') Empty
        in collapse $ V (d <> d') Empty m_ (rel d . Rev . maybe Empty Cat.singleton $ m'_)
      (Right EQ, e) ->
        V (d <> d') Empty m (rel d . Rev . Cat.singleton . layout e pr p' $ m')
      (Right GT, e) ->
        V (d <> d') (Cat.singleton m) (rel d . layout e pr p' $ m') Empty

  S d m@(Run p _ _ _ pr) <> V d' Empty m'@(Run p' _ _ _ _) r' =
    case (joinAndCompare p p', joinAndCompare pr p') of
      (Left _, _) ->
        V (d <> d') Empty m ((rel d . Rev . Cat.singleton . layoutError pr p' $ m') <> rel d r')
      (Right LT, _) ->
        let (m_, _, m'_, r'_) = shuffle d m Empty (Just m') r'
        in collapse $ V (d <> d') Empty m_ (rel d ((Rev . maybe Empty Cat.singleton $ m'_) <> r'_))
      (Right EQ, _) ->
        V (d <> d') Empty m (rel d (Rev (Cat.singleton m') <> r'))
      (Right GT, _) ->
        V (d <> d') (Cat.singleton m) (rel d m') (rel d r')

  S d m@(Run p _ _ _ pr) <> V d' l'@(lh'@(Run p' _ _ _ _) :< lt') m' r' =
    case (joinAndCompare p (prefix m'), joinAndCompare pr p') of
      (Left _, _) ->
        V (d <> d') Empty m (rel d ((Rev . Cat.singleton . layoutError pr p' $ lh') <> (Rev . revCat $ lt') <> (Rev . Cat.singleton $ m') <> r'))
      (Right LT, _) ->
        let (m_, l'_, m'_, r'_) = shuffle d m l' (Just m') r'
        in collapse $ V (d <> d') Empty m_ (rel d (Rev (revCat l'_) <> Rev (maybe Empty Cat.singleton m'_) <> r'_))
      (Right EQ, _) ->
        let (m_, l'_, _, _) = shuffle d m l' Nothing Empty
        in V (d <> d') Empty m_ (rel d (Rev (revCat l'_) <> Rev (Cat.singleton m') <> r'))
      (Right GT, _) ->
        let (m_, l'_, _, _) = shuffle d m l' Nothing Empty
        in V (d <> d') (m_ :< rel d l'_) (rel d m') (rel d r')

  V d l m r <> E d' = V (d <> d') l m r

  V d l m@(Run p _ _ _ pr) Empty <> S d' m'@(Run p' _ _ _ _) =
    case (joinAndCompare p p', joinAndCompare pr p') of
      (Left _, _) ->
        V (d <> d') l m (rel d . Rev . Cat.singleton . layoutError pr p' $ m')
      (Right LT, _) ->
        let (m_, _, m'_, _) = shuffle d m Empty (Just m') Empty
        in V (d <> d') l m_ (rel d . Rev . maybe Empty Cat.singleton $ m'_)
      (Right EQ, _) ->
        V (d <> d') l m (rel d . Rev . Cat.singleton $ m')
      (Right GT, _) ->
        V (d <> d') (l <> Cat.singleton m) (rel d m') Empty

  V d l m r@(rt :> rh@(Run _ _ _ _ pr)) <> S d' m'@(Run p' _ _ _ _) =
    case (joinAndCompare (prefix m) p', joinAndCompare pr p') of
      (Left _, Left _) ->
         V (d <> d') l m (r <> (rel d . Rev . Cat.singleton . layoutError pr p' $ m'))
      (Left _, Right LT) ->
        let (rh_, _, m'_, _) = shuffle d rh Empty (Just m') Empty
        in V (d <> d') l m ((rt :> rh_) <> (rel d . Rev . maybe Empty Cat.singleton $ m'_))
      (Left _, Right EQ) ->
        V (d <> d') l m (r :> (rel d m'))
      (Left _, Right GT) ->
         V (d <> d') l m (r <> (rel d . Rev . Cat.singleton $ m'))
      (Right LT, _) ->
        let (rh_, _, m'_, _) = shuffle d rh Empty (Just m') Empty
        in V (d <> d') l m ((rt :> rh_) <> (rel d . Rev . maybe Empty Cat.singleton $ m'_))
      (Right EQ, Left _) ->
        V (d <> d') l m (r :> (rel d . layoutError pr p' $ m'))
      (Right EQ, _) ->
        let (rh_, _, m'_, _) = shuffle d rh Empty (Just m') Empty
        in V (d <> d') l m ((rt :> rh_) <> (rel d . Rev . maybe Empty Cat.singleton $ m'_))
      (Right GT, Left _) ->
        V (d <> d') l m (r :> (rel d . layoutError pr p' $ m'))
      (Right GT, Right _) | testMismatch p' (V d l m r) == False ->
        let (rh_, _, m'_, _) = shuffle d rh Empty (Just m') Empty
        in V (d <> d') l m ((rt :> rh_) <> (rel d . Rev . maybe Empty Cat.singleton $ m'_))
      (Right GT, Right _) ->
        V (d <> d') (l <> Cat.singleton m <> revCat (runRev r)) (rel d m') Empty

  V d l m@(Run p _ _ _ pr) Empty <> V d' Empty m'@(Run p' _ _ _ _) r' =
    case (joinAndCompare p p', joinAndCompare pr p') of
      (Left _, Left _) ->
        V (d <> d') l m (rel d (Rev (Cat.singleton . layoutError pr p' $ m') <> r'))
      (Left _, Right LT) -> error "E1b"
      (Left _, Right EQ) -> error "E1c"
      (Left _, Right GT) -> error "E1d"
      (Right LT, _) ->
        let (m_, _, m'_, r'_) = shuffle d m Empty (Just m') r'
        in V (d <> d') l m_ (rel d (Rev (maybe Empty Cat.singleton m'_) <> r'_))
      (Right EQ, e) ->
        V (d <> d') l m (rel d (Rev (Cat.singleton . layout e pr p' $ m') <> r'))
      (Right GT, e) ->
        V (d <> d') (l <> Cat.singleton m) (rel d . layout e pr p' $ m') (rel d r')

  V d l m@(Run p _ _ _ pr) Empty <> V d' l'@((Run p' _ _ _ _) :< _) m' r' =
    case (joinAndCompare p (prefix m'), joinAndCompare pr p') of
      (Left _, Left _) -> error "F1a"
      (Left _, Right LT) -> error "F1b"
      (Left _, Right EQ) -> error "F1c"
      (Left _, Right GT) -> error "F1d"
      (Right LT, _) ->
        let (m_, l'_, m'_, r'_) = shuffle d m l' (Just m') r'
        in V (d <> d') l m_ (rel d (Rev (revCat l'_) <> Rev (maybe Empty Cat.singleton m'_) <> r'_))
      (Right EQ, _) ->
        let (m_, l'_, _, _) = shuffle d m l' Nothing Empty
        in V (d <> d') l m_ (rel d (Rev (revCat l'_) <> Rev (Cat.singleton m') <> r'))
      (Right GT, _) ->
        let (m_, l'_, _, _) = shuffle d m l' Nothing Empty
        in V (d <> d') (l <> Cat.singleton m_ <> rel d l'_) (rel d m') (rel d r')

  V d l m r@(rt :> rh@(Run _ _ _ _ pr)) <> V d' Empty m'@(Run p' _ _ _ _) r' =
    case (joinAndCompare (prefix m) p', joinAndCompare pr p') of
      (Left _, Left _) ->
        V (d <> d') l m (r <> rel d (Rev (Cat.singleton . layoutError pr p' $ m') <> r'))
      (Left _, Right LT) ->
         let (rh_, _, m'_, r'_) = shuffle d rh Empty (Just m') r'
         in V (d <> d') l m ((rt :> rh_) <> rel d (Rev (maybe Empty Cat.singleton m'_) <> r'_))
      (Left _, Right EQ) ->
        error "G1c"
      (Left _, Right GT) ->
        V (d <> d') l m (r <> rel d (Rev (Cat.singleton m') <> r'))
      (Right LT, _) ->
         let (rh_, _, m'_, r'_) = shuffle d rh Empty (Just m') r'
         in V (d <> d') l m ((rt :> rh_) <> rel d (Rev (maybe Empty Cat.singleton m'_) <> r'_))
      (Right EQ, e) ->
        V (d <> d') l m (r <> rel d (Rev (Cat.singleton . layout e pr p' $ m') <> r'))
      (Right GT, Left _) ->
        case preview _Cons l of
          Nothing -> V (d <> d') Empty m (r <> rel d (Rev (Cat.singleton . layoutError pr p' $ m') <> r'))
          Just (lh, lt) -> V (d <> d') Empty lh (Rev (revCat lt) <> r <> rel d (Rev (Cat.singleton . layoutError pr p' $ m') <> r'))
      (Right GT, Right _) | testMismatch p' (V d l m r) == False ->
        case preview _Cons l of
          Nothing -> V (d <> d') Empty m (r <> rel d (Rev (Cat.singleton m') <> r'))
          Just (lh, lt) -> V (d <> d') Empty lh (Rev (revCat lt) <> r <> rel d (Rev (Cat.singleton m') <> r'))
      (Right GT, e) ->
        V (d <> d') (l <> Cat.singleton m <> revCat (runRev r)) (rel d . layout e pr p' $ m') (rel d r')

  V d l m r@(rt :> rh@(Run _ _ _ _ pr)) <> V d' l'@(lh'@(Run p' _ _ _ _) :< lt') m' r' =
    case (joinAndCompare (prefix m) (prefix m'), joinAndCompare pr p') of
      (Left _, Left _) ->
        error "H1a"
      (Left _, Right LT) ->
        let (rh_, l'_, m'_, r'_) = shuffle d rh l' (Just m') r'
        in V (d <> d') l m ((rt :> rh_) <> rel d (Rev (revCat l'_) <> Rev (maybe Empty Cat.singleton m'_) <> r'_))
      (Left _, Right EQ) ->
        let (rh_, l'_, _, _) = shuffle d rh l' Nothing Empty
        in V (d <> d') l m ((rt :> rh_) <> rel d (Rev (revCat l'_) <> Rev (Cat.singleton m') <> r'))
      (Left _, Right GT) ->
        V (d <> d') l m (r <> rel d (Rev (revCat l') <> Rev (Cat.singleton m') <> r'))
      (Right LT, _) ->
        let (rh_, l'_, m'_, r'_) = shuffle d rh l' (Just m') r'
        in V (d <> d') l m ((rt :> rh_) <> rel d (Rev (revCat l'_) <> Rev (maybe Empty Cat.singleton m'_) <> r'_))
      (Right EQ, _) ->
        let (rh_, l'_, _, _) = shuffle d rh l' Nothing Empty
        in V (d <> d') l m ((rt :> rh_) <> rel d (Rev (revCat l'_) <> Rev (Cat.singleton m') <> r'))
      (Right GT, Left _) | testMismatch (prefix m') (V d l m r) == True ->
        V (d <> d') (l <> Cat.singleton m <> revCat (runRev r) <> (rel d ((Cat.singleton . layoutError pr p' $ lh') <> lt'))) (rel d m') (rel d r')
      (Right GT, Left _) ->
        V (d <> d') l m (r <> rel d (Rev (Cat.singleton . layoutError pr p' $ lh') <> Rev (revCat lt') <> Rev (Cat.singleton m') <> r'))
      (Right GT, Right _) | testMismatch p' (V d l m r) == False ->
        let (rh_, l'_, m'_, r'_) = shuffle d rh l' (Just m') r'
        in V (d <> d') l m ((rt :> rh_) <> rel d (Rev (revCat l'_) <> Rev (maybe Empty Cat.singleton m'_) <> r'_))
      (Right GT, _) ->
        let (rh_, _, lh'_, lt'_) = shuffle' d rh Empty (Just lh') lt'
        in V (d <> d') (l <> Cat.singleton m <> revCat (runRev rt) <> Cat.singleton rh_ <> rel d (maybe Empty Cat.singleton lh'_) <> rel d lt'_) (rel d m') (rel d r')

instance Monoid Layout where
  mempty = E 0
  mappend = (<>)
