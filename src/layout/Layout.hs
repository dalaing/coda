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

data LayoutMismatch = LayoutMismatch !Delta !Prefix !Prefix
  deriving (Eq, Show) -- this is for debugging the Layout Monoid

instance Relative LayoutMismatch where
  rel d (LayoutMismatch d' p q) = LayoutMismatch (d <> d') p q

-- The first Prefix is the lowest indent that covers the whole run
-- The second Prefix is the last indent we have seen as we have put this run together
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
  -- I have changed this so that the middle bit tracks Cat or Runs with the same indent.
  -- This is looking like it might be problematic in some cases (at least from a performance perspective),
  -- since I occasionally need to inspect either end of this Cat.
  | V {-# unpack #-} !Delta !(Cat Run) !(Cat Run) !(Rev Cat Run)
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

instance Semigroup Layout where
  E 0 <> xs = xs
  xs <> E 0 = xs
  E d <> E d' = E (d <> d')
  E d <> S d' (Run p ds ts es pr) = S (d <> d') $ Run p (rel d ds) (rel d ts) (rel d es) pr
  E d <> V d' l m r = V (d <> d') (rel d l) (rel d m) (rel d r)
  S d (Run p ds ts es pr) <> E d' = S (d <> d') $ Run p ds ts es pr
  S d lr@(Run p ds ts es pr) <> S d' rr@(Run p' ds' ts' es' pr') =
    case joinAndCompare pr p' of
      Left _ -> S (d <> d') $ Run p (ds <> rel d ds') (ts <> rel d ts') (snocCat es (LayoutMismatch d pr p') <> rel d es') pr' -- no common prefix
      Right _ -> case joinAndCompare p p' of
        Left _ -> S (d <> d') $ Run p (ds <> rel d ds') (ts <> rel d ts') (snocCat es (LayoutMismatch d pr p') <> rel d es') pr' -- no common prefix
        Right LT -- indent
          | boring ts -> S (d <> d') $ Run p (ds <> rel d ds') (ts <> rel d ts') (es <> rel d es') pr'
          | otherwise -> V (d <> d') Empty (Cat.singleton lr) $ Rev $ Cat.singleton (rel d rr)
        Right EQ -> V (d <> d') Empty (Cat.singleton lr <> Cat.singleton (rel d rr)) Empty
        Right GT -> V (d <> d') (Cat.singleton lr) (Cat.singleton $ rel d rr) Empty

  -- a
  -- fg h ji/Rij
  S d lr@(Run p ds ts es pr) <> V d' l m r =
    case preview _Cons m of
      Just (mh@(Run p' ds' ts' es' pr'), ht) ->
        case joinAndCompare pr (prefix mh) of
          Left _ -> error "boom 2"
          Right _ -> case joinAndCompare p (prefix mh) of
            Left _ -> error "boom 2a"
              -- a                -- a and fg might combine if ts is boring
              --     fg
              --   h
              --     ji/Rij
            Right LT -> case preview _Cons l of
              Nothing -> case preview _Snoc r of
                Nothing
                  | boring ts -> S (d <> d') $ Run p (ds <> rel d ds') (ts <> rel d ts') (es <> rel d es') pr'
                  | otherwise -> V (d <> d') Empty (Cat.singleton lr) (Rev (revCat (rel d m)) <> rel d r)
                _ -> V (d <> d') Empty (Cat.singleton lr) (Rev (revCat (rel d m)) <> rel d r)
              Just (lh@(Run p'' ds'' ts'' es'' pr''), lt)
                | boring ts -> V (d <> d') Empty (Cat.singleton (Run p (ds <> rel d ds'') (ts <> rel d ts'') (es <> rel d es'') pr'')) (Rev (revCat (rel d (lt <> m))) <> rel d r)
                | otherwise -> V (d <> d') Empty (Cat.singleton lr) (Rev (revCat (rel d (l <> m))) <> rel d r)
            -- a             -- this may combine with fg if ts is boring
            --   fg
            -- h
            --   ji/Rij
            Right EQ -> case preview _Cons l of
              Nothing -> V (d <> d') Empty (Cat.singleton lr <> rel d m) (rel d r)
              Just (lh@(Run p' ds' ts' es' pr'), lt)
                | boring ts -> V (d <> d') Empty (Cat.singleton (Run p (ds <> rel d ds') (ts <> rel d ts') (es <> rel d es') pr') <> rel d lt <> rel d m) (rel d r)
                | otherwise -> V (d <> d') Empty (Cat.singleton lr <> rel d l <> rel d m) (rel d r)
            --   a
            --   fg
            -- h
            --   ji/Rij
            Right GT -> V (d <> d') (Cat.singleton lr <> rel d l) (rel d m) (rel d r)
      Nothing -> error "should not be empty"

  V d l m r <> E d' = V (d <> d') l m r

  -- -- ab c ed/Rde
  -- -- f
  V d l m r@(Rev rr) <> S d' rr'@(Run p' ds' ts' es' pr') =
    case preview _Cons m of
      Just (mh, ht) ->
        case joinAndCompare (prefix mh) p' of
          Left _ -> error "boom 4"
        -- --   ab
        --    c
        --      ed/Rde -- last ed might combine with f
        -- --   f
          Right LT -> case preview _Snoc r of
            Nothing -> case preview _Cons (revCat m) of -- TODO this is really bad, do better than this
              Just (smh@(Run p ds ts es pr), sht)
                | boring ts -> V (d <> d') l (revCat $ review _Cons (Run p (ds <> rel d ds') (ts <> rel d ts') (es <> rel d es') pr', sht)) Empty
                | otherwise -> V (d <> d') l m (Rev . Cat.singleton . rel d $ rr')
              Nothing -> error "should not be empty"
            Just (rt, rh@(Run p ds ts es pr))
              | boring ts -> case joinAndCompare pr p' of
                  Left _ -> error "boom 4a"
                  Right _ -> case joinAndCompare p p' of
                    Left _ -> error "boom 4b"
                    Right LT -> V (d <> d') l m (review _Snoc (rt, Run p (ds <> rel d ds') (ts <> rel d ts') (es <> rel d es') pr'))
                    Right EQ -> V (d <> d') l m (r <> Rev (Cat.singleton (rel d rr')))
                    Right GT -> V (d <> d') l m (r <> Rev (Cat.singleton (rel d rr')))
              | otherwise -> V (d <> d') l m (r <> Rev (Cat.singleton (rel d rr')))
        -- --   ab
        --    c
        --      ed/Rde
        -- -- f
          Right EQ -> V (d <> d') l (m <> revCat rr <> Cat.singleton (rel d rr')) Empty
        -- --     ab
        --      c
        --        ed/Rde
        -- -- f
          Right GT -> V (d <> d') (l <> m <> revCat rr) (Cat.singleton (rel d rr')) Empty
      Nothing -> error "should not be empty"

  -- -- ab c
  -- --    h ji/Rij
  V d l m Empty <> V d' Empty m' r' =
    case (preview _Cons m, preview _Cons m') of
      (Just (mh, ht), Just (mh', mt')) ->
        case joinAndCompare (prefix mh) (prefix mh') of
          Left _ -> error "boom 5"
      -- --   ab
      --    c            -- this may combine with h if last c is boring?
      -- --   h
      -- --     ji/Rij
          Right LT -> V (d <> d') l m (Rev (revCat m') <> r')

      -- --   ab
      --    c
      -- -- h
      -- --   ji/Rij
          Right EQ -> V (d <> d') l (m <> rel d m') (rel d r')

      -- --     ab
      --      c
      -- -- h
      -- --   ji/Rij
          Right GT -> V (d <> d') (l <> m) (rel d m') (rel d r')
      _ -> error "should not be empty"

  -- -- ab c
  -- -- fg h ji/Rij
  V d l m Empty <> V d' l' m' r' =
    case (preview _Cons m, preview _Cons m') of
      (Just (mh, ht), Just (mh', mt')) ->
        case joinAndCompare (prefix mh) (prefix mh') of
          Left _ -> error "boom 6"
      -- --   ab
      --    c            -- this may combine with fg if last c is boring?
      -- --     fg
      --      h
      --        ji/Rij
          Right LT -> V (d <> d') l m (Rev (revCat (rel d (l' <> m'))) <> rel d r')


      -- --   ab
      --    c             -- this maybe combine with fg if last c is boring?
      -- --   fg
      --    h
      --      ji/Rij
          Right EQ -> V (d <> d') l (m <> rel d l' <> rel d m') (rel d r')

      -- --     ab
      --      c
      -- --   fg
      --    h
      --      ji/Rij
          Right GT -> V (d <> d') (l <> m <> rel d l') (rel d m') (rel d r')
      _ -> error "should not be empty"

  -- -- ab c ed/Rde
  -- --    h ji/Rij
  V d l m r@(Rev rr) <> V d' Empty m' r' =
    case (preview _Cons m, preview _Cons m') of
      (Just (mh, ht), Just (mh', mt')) ->
        case joinAndCompare (prefix mh) (prefix mh') of
          Left _ -> error "boom 7"
      -- --   ab
      --    c
      --      ed/Rde   -- last ed might combine with h
      -- --   h
      --        ji/Rij
          Right LT -> V (d <> d') l m (r <> Rev (revCat (rel d m')) <> rel d r')

      -- --   ab
      --    c
      --      ed/Rde
      -- -- h
      --      ji/Rij
          Right EQ -> V (d <> d') l (m <> revCat rr <> rel d m') (rel d r')

      -- --     ab
      --      c
      --        ed/Rde
      -- -- h
      --      ji/Rij
          Right GT -> V (d <> d') (l <> m <> revCat rr) (rel d m') (rel d r')
      _ -> error "should not be empty"

  -- -- ab c ed/Rde
  -- -- fg h ji/Rij
  V d l m r@(Rev rr) <> V d' l' m' r' =
    case (preview _Cons m, preview _Cons m') of
      (Just (mh, ht), Just (mh', mt')) ->
        case joinAndCompare (prefix mh) (prefix mh') of
          Left _ -> error "boom 8"
      -- --   ab
      --    c
      --      ed/Rde  -- do the relative positions of ed and h matter?
      -- --     fg
      --      h
      --        ji/Rij
          Right LT -> V (d <> d') l m (r <> Rev (revCat (rel d (l' <> m'))) <> rel d r')

      -- --   ab
      --    c
      --      ed/Rde -- might last ed and head fg join up?
      -- --   fg
      --    h
      --      ji/Rij
          Right EQ -> V (d <> d') l (m <> revCat rr <> rel d l' <> rel d m') (rel d r')

      -- --     ab
      --      c
      --        ed/Rde -- might last ed and head fg join up?
      -- --   fg
      --    h
      --      ji/Rij
          Right GT -> V (d <> d') (l <> m <> revCat rr <> rel d l') (rel d m') (rel d r')
      _ -> error "should not be empty"

instance Monoid Layout where
  mempty = E 0
  mappend = (<>)
