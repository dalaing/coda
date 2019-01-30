{-# language CPP #-}
{-# language OverloadedLists #-}
{-# language LambdaCase #-}
{-# OPTIONS_GHC -Wno-incomplete-patterns #-}
module Layout where

import Control.Lens
import Data.Default

#if __GLASGOW_HASKELL__ < 804
import Data.Semigroup
#endif

import Relative.Class
import Relative.Delta
import Relative.Cat as Cat
import Rev
import Syntax.Prefix

import Dyck
import Parser

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

-- this should almost certainly be revAppendCat :: Relative a => Cat a -> Cat a -> Cat a
revCat :: Relative a => Cat a -> Cat a
revCat Empty = Empty
revCat (x :< xs) = snocCat (revCat xs) x

runSnocMismatch :: LayoutMismatch -> Run -> Run
runSnocMismatch e (Run p ds ts es pr) = Run p ds ts (snocCat es e) pr

runMerge :: Delta -> Run -> Run -> Run
runMerge d (Run p ds ts es pr) (Run p' ds' ts' es' pr') =
  case joinAndCompare pr p' of
    Left _ ->
      Run p (ds <> rel d ds') (ts <> rel d ts') (es <> rel d (snocCat es' (LayoutMismatch 0 pr p'))) pr'
    Right _ ->
      Run p (ds <> rel d ds') (ts <> rel d ts') (es <> rel d es') pr'

shuffle :: Delta -> Run -> Cat Run -> Maybe Run -> Rev Cat Run -> (Run, Cat Run, Maybe Run, Rev Cat Run)
shuffle d m l' m' r' =
  let
    (m'', l''', m''', r''') = shuffle' d m l' m' (revCat (runRev r'))
  in
    (m'', rel d l''', fmap (rel d) m''', Rev (revCat (rel d r''')))

-- will this ever need to deal with EQ?
shuffle' :: Delta -> Run -> Cat Run -> Maybe Run -> Cat Run -> (Run, Cat Run, Maybe Run, Cat Run)
shuffle' d m@(Run p _ ts Empty pr) l' m' r' =
  case preview _Cons l' of
    Just (lh'@(Run p' _ _ es' pr'), lt') ->
      case joinAndCompare p p' of
        Right LT | boring ts && Cat.null es' -> shuffle' d (runMerge d m lh') lt' m' r'
        otherwise -> (m, l', m', r')
    Nothing ->
      case m' of
        Just (m''@(Run p' _ _ es' pr')) ->
          case joinAndCompare p p' of
            Right LT | boring ts && Cat.null es' -> shuffle' d (runMerge d m m'') l' Nothing r'
            otherwise -> (m, l', m', r')
        Nothing -> case preview _Cons r' of
          Just (rh'@(Run p' _ _ es' pr'), rt') ->
            case joinAndCompare p p' of
              Right LT | boring ts && Cat.null es' -> shuffle' d (runMerge d m rh') l' Nothing rt'
              otherwise -> (m, l', m', r')
          Nothing -> (m, l', m', r')
shuffle' d m@(Run p _ ts _ pr) l' m' r' =
  (m, l', m', r')

-- do we ever have to consider whether the tokens on the RHS of the join are boring or not?
--
-- how do we deal with things like:
-- foo
--   a
--   do
--      b
--      c
--   d
-- or are they dealt with already?

instance Semigroup Layout where
  E 0 <> xs = xs
  xs <> E 0 = xs
  E d <> E d' = E (d <> d')
  E d <> S d' (Run p ds ts es pr) = S (d <> d') $ Run p (rel d ds) (rel d ts) (rel d es) pr
  E d <> V d' l m r = V (d <> d') (rel d l) (rel d m) (rel d r)
  S d m <> E d' = S (d <> d') m
  S d m@(Run p _ ts _ pr) <> S d' m'@(Run p' _ _ _ pr') =
    case joinAndCompare p p' of
      Left _ ->
        V (d <> d') Empty m (Rev . Cat.singleton . rel d $ runSnocMismatch (LayoutMismatch 0 pr p') m')
      --        m
      --  m       m
      -- <>     <>
      -- m'      m'
      Right LT
        | boring ts ->
            case joinAndCompare pr p' of
              Left _ -> V (d <> d') Empty m (Rev . Cat.singleton . rel d $ runSnocMismatch (LayoutMismatch 0 pr p') m')
              Right _ -> S (d <> d') (runMerge d m m')
        | otherwise ->
          V (d <> d') Empty m (Rev (Cat.singleton (rel d m')))
      --        m
      --  m      m
      -- <>     <>
      -- m'     m'
      Right EQ ->
        V (d <> d') Empty m (Rev (Cat.singleton (rel d m')))
      --         m
      --  m       m
      -- <>     <>
      -- m'     m'
      Right GT ->
        V (d <> d') (Cat.singleton m) (rel d m') Empty

  S d m@(Run p ds ts es pr) <> V d' l' m'@(Run p' ds' ts' es' pr') r' =
    case preview _Cons l' of
      Nothing ->
        case joinAndCompare p p' of
          Left _ ->
            V (d <> d') Empty m (rel d (Rev (Cat.singleton (runSnocMismatch (LayoutMismatch 0 pr p') m')) <> r'))
          Right LT
            -- m
            --   m
            -- <>
            --  m'
            --    r'
            | boring ts ->
              case preview _Snoc r' of
                Nothing ->
                  S (d <> d') (runMerge d m m')
                Just _ ->
                  let
                    (m_, _, m'_, r_) = shuffle d m Empty (Just m') r'
                    r'_ = maybe mempty (Rev . Cat.singleton) m'_ <> r_
                  in
                    case preview _Snoc r'_ of
                      Nothing -> S (d <> d') m_
                      Just _ -> V (d <> d') Empty m_ r'_
            | otherwise ->
              V (d <> d') Empty m (rel d (Rev (Cat.singleton m') <> r'))
          Right EQ ->
            -- m
            --  m
            -- <>
            -- m'
            --   r'
            V (d <> d') Empty m (rel d (Rev (Cat.singleton m') <> r'))
          Right GT ->
            --  m
            --   m
            -- <>
            -- m'
            --   r'
            V (d <> d') (Cat.singleton m) (rel d m') (rel d r')
      Just (lh'@(Run p'' ds'' ts'' es'' pr''), lt') ->
        case (joinAndCompare p p', joinAndCompare p p'') of
          (Left _, _) ->
            V (d <> d') (Cat.singleton m <> rel d (Cat.singleton (runSnocMismatch (LayoutMismatch 0 pr p'') lh') <> lt')) (rel d m') (rel d r')
          (_, Left _) ->
            V (d <> d') (Cat.singleton m <> rel d (Cat.singleton (runSnocMismatch (LayoutMismatch 0 pr p'') lh') <> lt')) (rel d m') (rel d r')
          (Right LT, _) ->
            -- m
            -- <>
            --   l'
            --  m'
            --   r'
            let
              (m_, l'_, m'_, r_) = shuffle d m l' (Just m') r'
              r'_ = (Rev (revCat l'_) <> maybe Empty (Rev . Cat.singleton) m'_ <> r_)
            in
              case preview _Snoc r'_ of
                Nothing -> S (d <> d') m_
                Just _ -> V (d <> d') Empty m_ r'_
          (Right EQ, _) ->
            -- m
            -- <>
            --  l'
            -- m'
            --   r'
            let
              (m_, l'_, _, _) =
                case joinAndCompare pr p'' of
                  Left _ -> shuffle d m (Cat.singleton (runSnocMismatch (LayoutMismatch 0 pr p'') lh') <> lt') Nothing Empty
                  Right _ -> shuffle d m l' Nothing Empty
            in
              V (d <> d') Empty m_ (Rev (revCat l'_) <> rel d (Rev (Cat.singleton m') <> r'))
          (Right GT, Right LT) ->
            --  m
            -- <>
            --    l'
            -- m'
            --   r'
            let
              (m_, l'_, _, _) = shuffle d m l' Nothing Empty
            in
              V (d <> d') (Cat.singleton m_ <> l'_) (rel d m') (rel d r')
          (Right GT, _) ->
            --  m
            -- <>
            --  l'
            -- m'
            --   r'
            V (d <> d') (Cat.singleton m <> rel d l') (rel d m') (rel d r')

  V d l m r <> E d' = V (d <> d') l m r

  V d l m@(Run p ds ts es pr) r <> S d' m'@(Run p' ds' ts' es' pr') =
    case preview _Snoc r of
      Nothing ->
        case joinAndCompare p p' of
          Left _ ->
            V (d <> d') l m (Rev (Cat.singleton (rel d (runSnocMismatch (LayoutMismatch 0 pr p') m'))))
          Right LT
            --  l
            -- m
            -- <>
            --  m'
            | boring ts ->
              case joinAndCompare pr p' of
                Left _ -> V (d <> d') l m (Rev (Cat.singleton (rel d (runSnocMismatch (LayoutMismatch 0 pr p') m'))))
                Right _ ->
                  case preview _Cons l of
                    Nothing -> S (d <> d') (runMerge d m m')
                    Just _ -> V (d <> d') l (runMerge d m m') Empty
            | otherwise ->
              V (d <> d') l m (Rev (Cat.singleton (rel d m')))
          Right EQ ->
            --  l
            -- m
            -- <>
            -- m'
            V (d <> d') l m (Rev (Cat.singleton (rel d m')))
          Right GT ->
            --   l
            --  m
            -- <>
            -- m'
            V (d <> d') (l <> Cat.singleton m) (rel d m') Empty
      Just (rt, rh@(Run p'' ds'' ts'' es'' pr'')) ->
        case (joinAndCompare p p', joinAndCompare p'' p') of
          (Left _, _) ->
            V (d <> d') l m (r <> Rev (Cat.singleton (rel d (runSnocMismatch (LayoutMismatch 0 pr'' p') m'))))
          (_, Left _) ->
            V (d <> d') l m (r <> Rev (Cat.singleton (rel d (runSnocMismatch (LayoutMismatch 0 pr'' p') m'))))
          (Right LT, Right o)
            --  l
            -- m
            --  r
            -- <>
            --  m'
            | boring ts'' && o == LT ->
              case joinAndCompare pr'' p' of
                Left _ -> V (d <> d') l m (r <> Rev (Cat.singleton (rel d (runSnocMismatch (LayoutMismatch 0 pr'' p') m'))))
                Right _ -> V (d <> d') l m (rt <> Rev (Cat.singleton (runMerge d rh m')))
            | otherwise ->
              V (d <> d') l m (r <> Rev (Cat.singleton (rel d m')))
          (Right EQ, _) ->
            --  l
            -- m
            --  r
            -- <>
            -- m'
            V (d <> d') l m (r <> Rev (Cat.singleton (rel d m')))
          (Right GT, _) ->
            --   l
            --  m
            --   r
            -- <>
            -- m'
            V (d <> d') (l <> Cat.singleton m <> revCat (runRev r)) (rel d m') Empty

  V d l m@(Run p ds ts es pr) r <> V d' l' m'@(Run p' ds' ts' es' pr') r' =
    case (preview _Snoc r, preview _Cons l') of
      (Nothing, Nothing) ->
        case joinAndCompare p p' of
          Left _ ->
            V (d <> d') l m (rel d (Rev (Cat.singleton (runSnocMismatch (LayoutMismatch 0 pr p') m')) <> r'))
          Right LT
            --  l
            -- m
            -- <>
            --  m'
            --   r'
            | boring ts ->
              let
                (m_, _, m'_, r_) = shuffle d m Empty (Just m') r'
                r'_ = maybe Empty (Rev . Cat.singleton) m'_ <> r_
              in
                case (preview _Cons l, preview _Snoc r'_) of
                  (Nothing, Nothing) -> S (d <> d') m_
                  _ -> V (d <> d') l m_ r'_
            | otherwise ->
              V (d <> d') l m (rel d (Rev (Cat.singleton m') <> r'))
          Right EQ ->
            --  l
            -- m
            -- <>
            -- m'
            --  r'
            V (d <> d') l m (rel d (Rev (Cat.singleton m') <> r'))
          Right GT ->
            --   l
            --  m
            -- <>
            -- m'
            --  r'
            V (d <> d') (l <> Cat.singleton m) (rel d m') (rel d r')
      (Just (rt, rh@(Run p'' ds'' ts'' es'' pr'')), Nothing) ->
        case joinAndCompare p'' p' of
          Left _ ->
            V (d <> d') l m (r <> rel d (Rev (Cat.singleton (runSnocMismatch (LayoutMismatch 0 pr'' p') m')) <> r'))
          Right _ ->
            case joinAndCompare p p' of
              Left _ ->
                V (d <> d') l m (r <> rel d (Rev (Cat.singleton (runSnocMismatch (LayoutMismatch 0 pr'' p') m')) <> r'))
              Right LT ->
                --  l
                -- m
                --  r
                -- <>
                --  m'
                --   r'
                let
                  (rh_, _, m'', r'') = shuffle d rh Empty (Just m') r'
                in
                  V (d <> d') l m (rt <> Rev (Cat.singleton rh_) <> maybe Empty (Rev . Cat.singleton) m'' <> r'')
              Right EQ ->
                --  l
                -- m
                --  r
                -- <>
                -- m'
                --  r'
                V (d <> d') l m (r <> Rev (Cat.singleton (rel d m')) <>  (rel d r'))
              Right GT ->
                --   l
                --  m
                --   r
                -- <>
                -- m'
                --  r'
                V (d <> d') (l <> Cat.singleton m <> revCat (runRev r)) (rel d m') (rel d r')
      (Nothing, Just (lh'@(Run p''' ds''' ts''' es''' pr'''), lt')) ->
        case (joinAndCompare p p', joinAndCompare p p''') of
          (Left _, _) ->
            V (d <> d') l m (rel d (Rev (Cat.singleton (runSnocMismatch (LayoutMismatch 0 pr p''') lh')) <> Rev (revCat lt') <> Rev (Cat.singleton m') <> r'))
          (_, Left _) ->
            V (d <> d') l m (rel d (Rev (Cat.singleton (runSnocMismatch (LayoutMismatch 0 pr p''') lh')) <> Rev (revCat lt') <> Rev (Cat.singleton m') <> r'))
          (Right LT, _) ->
             --  l
             -- m
             -- <>
             --   l'
             --  m'
             --   r'
             let
               (m_, l'_, m'_, r_) = shuffle d m l' (Just m') r'
               r'_ = Rev (revCat l'_) <> maybe Empty (Rev . Cat.singleton) m'_ <> r_
             in
               case (preview _Cons l, preview _Snoc r'_) of
                 (Nothing, Nothing) -> S (d <> d') m_
                 _ -> V (d <> d') l m_ r'_
          (Right EQ, Right LT) ->
            --  l
            -- m
            -- <>
            --  l'
            -- m'
            --  r'
            let
              (m_, l_, _, _) = shuffle d m l' Nothing Empty
            in
              V (d <> d') l m_ (Rev (revCat l_) <> rel d (Rev (Cat.singleton m') <> r'))
          (Right EQ, _) ->
            --  l
            -- m
            -- <>
            --  l'
            -- m'
            --  r'
            V (d <> d') l m (rel d (Rev (revCat l') <> Rev (Cat.singleton m') <> r'))
          (Right GT, Right LT) ->
            --   l
            --  m
            -- <>
            --  l'
            -- m'
            --  r'
            let
              (m_, l_, _, _) = shuffle d m l' Nothing Empty
            in
              V (d <> d') (l <> Cat.singleton m_ <> l_) (rel d m') (rel d r')
          (Right GT, _) ->
            V (d <> d') (l <> Cat.singleton m <> rel d l') (rel d m') (rel d r')

      (Just (rt, rh@(Run p'' ds'' ts'' es'' pr'')), Just (lh'@(Run p''' ds''' ts''' es''' pr'''), lt')) ->
        case joinAndCompare p'' p''' of
          Left _ ->
            V (d <> d') l m (r <> rel d (Rev (Cat.singleton (runSnocMismatch (LayoutMismatch 0 pr'' p''') lh')) <> Rev (revCat lt') <> Rev (Cat.singleton m') <> r'))
          Right _ ->
            case joinAndCompare p p' of
              Left _ ->
                V (d <> d') l m (r <> rel d (Rev (Cat.singleton (runSnocMismatch (LayoutMismatch 0 pr'' p''') lh')) <> Rev (revCat lt') <> Rev (Cat.singleton m') <> r'))
              Right LT ->
                --  l
                -- m
                --  r
                -- <>
                --   l'
                --  m'
                --   r'
                let
                  (rh'', l'', m'', r'') = shuffle d rh l' (Just m') r'
                in
                  V (d <> d') l m (rt <> Rev (Cat.singleton rh'') <> Rev (revCat l'') <> maybe Empty (Rev . Cat.singleton) m'' <> r'')
              Right EQ ->
                --  l
                -- m
                --  r
                -- <>
                --  l'
                -- m'
                --  r'
                let
                  (rh'', l'', _, _) = shuffle d rh l' Nothing Empty
                in
                  V (d <> d') l m (rt <> Rev (Cat.singleton rh'') <> Rev (revCat l'') <> (rel d (Rev (Cat.singleton m') <> r')))
              Right GT ->
                --   l
                --  m
                --   r
                -- <>
                --  l'
                -- m'
                --  r'
                let
                  (rh'', l'', _, _) = shuffle d rh l' Nothing Empty
                in
                  V (d <> d') (l <> Cat.singleton m <> revCat (runRev rt) <> Cat.singleton rh'' <> l'') (rel d m') (rel d r')

instance Monoid Layout where
  mempty = E 0
  mappend = (<>)
