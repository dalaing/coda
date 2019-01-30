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

-- this double reverse is a bit worrying
--
-- if we append all of the things as we can, most things will get
-- put together during construction
--
-- the problem will happen when we have runs of tokens at the same indent
-- they get skewed down the right side of the V
-- if we then prepend a "do" at a lower indentation, we need to do this
-- to pull those out
shuffle :: Delta -> Run -> Run -> Rev Cat Run -> (Run, Rev Cat Run)
shuffle d m r (Rev rs) =
  let
    (r', rs') = shuffle' d m (review _Cons (r, revCat rs))
 in
    (r', Rev (revCat (rel d rs')))

shuffle' :: Delta -> Run -> Cat Run -> (Run, Cat Run)
shuffle' d r@(Run p ds ts es pr) cr =
  case preview _Cons cr of
    Nothing -> (r, Empty)
    Just (Run p' ds' ts' es' pr', rs) ->
      case joinAndCompare pr p' of
        -- if we add errors here, they end up doubled - this is weird, and we need to get to the bottom of this
        -- Left _ -> (r, review _Cons $ (Run p' ds' ts' (snocCat es' (LayoutMismatch 0 pr p')) pr', rs))
        Left _ -> (r, review _Cons $ (Run p' ds' ts' es' pr', rs))
        Right _ -> case joinAndCompare p p' of
          -- Left _ -> (r, review _Cons $ (Run p' ds' ts' (snocCat es' (LayoutMismatch 0 p p')) pr', rs))
          Left _ -> (r, review _Cons $ (Run p' ds' ts' es' pr', rs))
          -- TODO we should be accumulating into the d here? but we aren't, and it might be causing troubles
          Right LT | boring ts -> shuffle' d (Run p (ds <> rel d ds') (ts <> rel d ts') (es <> rel d es') pr') rs
          _ -> (r, cr)

{-
The recursive calls are operating with the wrong deltas.
It _might_ all work out in the end, but the burden on proof is on me if I'm going to rely on it.
-}

{-
The two prefixes need some thought
If we have boring indentation and p < p', we're extending a Run

The second check might be pr <= p' when p and pr don't match, and we're not handling this case.
We could wrap pr in a Maybe, and only add it in when it doesn't match p.

We might end up with different error information depending on which of these indentation comparisons fails to match.
That will be fun to deal with.
-}

checkPrefixes :: Prefix -> Prefix -> Run -> (Run -> Layout) -> (Ordering -> Layout) -> Layout
checkPrefixes pr p (Run p' ds' ts' es' pr') errFn successFn =
  case joinAndCompare pr p' of
    Left _ -> errFn (Run p' ds' ts' (snocCat es' (LayoutMismatch 0 pr p')) pr')
    Right _ -> case joinAndCompare p p' of
      Left _ -> errFn (Run p' ds' ts' (snocCat es' (LayoutMismatch 0 p p')) pr')
      Right c -> successFn c

instance Semigroup Layout where
  E 0 <> xs = xs
  xs <> E 0 = xs
  E d <> E d' = E (d <> d')
  E d <> S d' (Run p ds ts es pr) = S (d <> d') $ Run p (rel d ds) (rel d ts) (rel d es) pr
  E d <> V d' l m r = V (d <> d') (rel d l) (rel d m) (rel d r)
  S d (Run p ds ts es pr) <> E d' = S (d <> d') $ Run p ds ts es pr
  S d lr@(Run p ds ts es pr) <> S d' rr@(Run p' ds' ts' es' pr') =
    checkPrefixes pr p rr (V (d <> d') Empty lr . Rev . Cat.singleton . rel d) $ \case
      LT
        | boring ts -> S (d <> d') $ Run p (ds <> rel d ds') (ts <> rel d ts') (es <> rel d es') pr'
        | otherwise -> V (d <> d') Empty lr $ Rev $ Cat.singleton (rel d rr)
      EQ -> V (d <> d') Empty lr (Rev . Cat.singleton . rel d $ rr)
      GT -> V (d <> d') (Cat.singleton lr) (rel d rr) Empty

  -- a
  -- fg h ji/Rij
  S d lr@(Run p ds ts es pr) <> V d' l m@(Run p' ds' ts' es' pr') r =
      case joinAndCompare pr p' of
        Left _ ->
          case preview _Cons l of
            Nothing ->
              V (d <> d') (Cat.singleton lr) (rel d (Run p' ds' ts' (snocCat es' (LayoutMismatch 0 pr p')) pr')) (rel d r)
            Just (lh@(Run p'' ds'' ts'' es'' pr''), lt) ->
              V (d <> d') (Cat.singleton lr <> Cat.singleton (rel d (Run p'' ds'' ts'' (snocCat es'' (LayoutMismatch 0 pr p')) pr'')) <> rel d lt) (rel d m) (rel d r)
        Right _ -> case joinAndCompare p p' of
          Left _ ->
            case preview _Cons l of
              Nothing ->
                V (d <> d') (Cat.singleton lr) (rel d (Run p' ds' ts' (snocCat es' (LayoutMismatch 0 p p')) pr')) (rel d r)
              Just (lh@(Run p'' ds'' ts'' es'' pr''), lt) ->
                V (d <> d') (Cat.singleton lr <> Cat.singleton (rel d (Run p'' ds'' ts'' (snocCat es'' (LayoutMismatch 0 p p')) pr'')) <> rel d lt) (rel d m) (rel d r)
            -- a                -- a and fg might combine if ts is boring
            --     fg
            --   h
            --     ji/Rij
          Right LT -> case preview _Cons l of
            Nothing -> case preview _Snoc r of
              Nothing
                | boring ts -> S (d <> d') $ Run p (ds <> rel d ds') (ts <> rel d ts') (es <> rel d es') pr'
                | otherwise -> V (d <> d') Empty lr (Rev (Cat.singleton (rel d m)))
              _ ->
                let
                  (m', r') = shuffle d lr m r
                in
                  case preview _Snoc r' of
                    Nothing -> S (d <> d') m'
                    Just _ -> V (d <> d') Empty m' r'
            Just (lh@(Run p'' ds'' ts'' es'' pr''), lt) ->
              case joinAndCompare pr p'' of
                Left _ -> error "boom 2b"
                Right _ -> case joinAndCompare p p'' of
                  Left _ -> error "boom 2c"
                  Right _
                    | boring ts -> S d (Run p (ds <> rel d ds'') (ts <> rel d ts'') (es <> rel d es'') pr'') <> V d' lt m r
                    | otherwise -> V (d <> d') Empty lr (Rev (revCat (rel d (l <> Cat.singleton m))) <> rel d r)
          -- a             -- this may combine with fg if ts is boring
          --   fg
          -- h
          --   ji/Rij
          Right EQ -> case preview _Cons l of
            Nothing -> V (d <> d') Empty lr (Rev (Cat.singleton (rel d m)) <> rel d r)
            Just (lh@(Run p'' ds'' ts'' es'' pr''), lt)
              | not (Cat.null es'') -> V (d <> d') Empty lr (Rev (revCat (rel d l)) <> Rev (Cat.singleton (rel d m)) <> rel d r)
              | otherwise ->
                case joinAndCompare pr p'' of
                  Left _ ->
                    V (d <> d') Empty lr (rel d (Rev (Cat.singleton (Run p'' ds'' ts'' (snocCat es'' (LayoutMismatch 0 pr pr'')) pr'')) <> Rev (revCat lt) <> Rev (Cat.singleton m) <> r))
                  Right _ -> case joinAndCompare p p'' of
                    Left _ ->
                      V (d <> d') Empty lr (rel d (Rev (Cat.singleton (Run p'' ds'' ts'' (snocCat es'' (LayoutMismatch 0 p pr'')) pr'')) <> Rev (revCat lt) <> Rev (Cat.singleton m) <> r))
                    Right LT | boring ts -> S d (Run p (ds <> rel d ds'') (ts <> rel d ts'') (es <> rel d es'') pr'') <> V d' lt m r
                    _ -> V (d <> d') Empty lr (Rev (revCat (rel d l)) <> Rev (Cat.singleton (rel d m)) <> rel d r)
          --   a                -- this may combine with fg if ts is boring and the indents work out
          --     fg
          -- h
          --     ji/Rij
          Right GT -> case preview _Cons l of
            Nothing -> V (d <> d') (Cat.singleton lr) (rel d m) (rel d r)
            Just (lh@(Run p'' ds'' ts'' es'' pr''), lt) ->
              case joinAndCompare pr p'' of
                Left _ -> V (d <> d') (Cat.singleton lr <> Cat.singleton (rel d (Run p'' ds'' ts'' (snocCat es'' (LayoutMismatch 0 pr p'')) pr'')) <> rel d lt) (rel d m) (rel d r)
                Right _ -> case joinAndCompare p p'' of
                  Left _ -> V (d <> d') (Cat.singleton lr <> Cat.singleton (Run p'' (rel d ds'') (rel d ts'') (rel d $ snocCat es'' (LayoutMismatch 0 pr p'')) pr'') <> rel d lt) (rel d m) (rel d r)
                  Right LT | boring ts -> S d (Run p (ds <> rel d ds'') (ts <> rel d ts'') (es <> rel d es'') pr'') <> V d' lt m r
                  _ -> V (d <> d') (Cat.singleton lr <> rel d l) (rel d m) (rel d r)

  V d l m r <> E d' = V (d <> d') l m r

  -- -- ab c ed/Rde
  -- -- f
  V d l m@(Run p ds ts es pr) r@(Rev rr) <> S d' rr'@(Run p' ds' ts' es' pr') =
    case joinAndCompare pr p' of
      Left _ -> V (d <> d') l m (r <> Rev (Cat.singleton (rel d (Run p' ds' ts' (snocCat es' (LayoutMismatch 0 (prefix m) p')) pr'))))
      Right _ -> case joinAndCompare p p' of
        Left _ -> V (d <> d') l m (r <> Rev (Cat.singleton (rel d (Run p' ds' ts' (snocCat es' (LayoutMismatch 0 (prefix m) p')) pr'))))

      -- --   ab
      --    c
      --      ed/Rde -- last ed might combine with f
      -- --   f
        Right LT -> case preview _Snoc r of
          Nothing
            | boring ts -> V (d <> d') l (Run p (ds <> rel d ds') (ts <> rel d ts') (es <> rel d es') pr') Empty
            | otherwise -> V (d <> d') l m (Rev . Cat.singleton . rel d $ rr')
          Just (rt, rh@(Run p ds ts es pr))
            | boring ts -> case joinAndCompare pr p' of
                Left _ ->
                  V (d <> d') l m (Rev (Cat.singleton rh) <> rt <> Rev (Cat.singleton (rel d (Run p' ds' ts' (snocCat es' (LayoutMismatch 0 pr p')) pr'))))
                Right _ -> case joinAndCompare p p' of
                  Left _ ->
                    V (d <> d') l m (Rev (Cat.singleton rh) <> rt <> Rev (Cat.singleton (rel d (Run p' ds' ts' (snocCat es' (LayoutMismatch 0 p p')) pr'))))
                  Right LT -> V (d <> d') l m (review _Snoc (rt, Run p (ds <> rel d ds') (ts <> rel d ts') (es <> rel d es') pr'))
                  Right EQ -> V (d <> d') l m (r <> Rev (Cat.singleton (rel d rr')))
                  Right GT -> V (d <> d') l m (r <> Rev (Cat.singleton (rel d rr')))
            | otherwise -> V (d <> d') l m (r <> Rev (Cat.singleton (rel d rr')))
      -- --   ab
      --    c
      --      ed/Rde
      -- -- f
        Right EQ -> V (d <> d') l m (r <> Rev (Cat.singleton (rel d rr')))
      -- --     ab
      --      c
      --        ed/Rde
      -- -- f
        Right GT -> V (d <> d') (l <> Cat.singleton m <> revCat rr) (rel d rr') Empty

  -- -- ab c ed/Rde
  -- -- fg h ji/Rij
  V d l m@(Run p ds ts es pr) r@(Rev rr) <> V d' l' m'@(Run p' ds' ts' es' pr') r' =
    case joinAndCompare pr p' of
      Left _ -> error "boom 8"
      Right _ -> case joinAndCompare p p' of
        Left _ -> error "boom 8"
    -- --   ab
    --    c
    --      ed/Rde  -- do the relative positions of head ed and h matter? yes
    -- --     fg
    --      h
    --        ji/Rij
        Right LT -> case (preview _Snoc r, preview _Cons l') of
          (Nothing, Nothing)
              | boring ts ->
                let
                  (m'', r'') = shuffle d m m' r'
                in
                  V (d <> d') l m'' r''
              | otherwise -> V (d <> d') l m (Rev (Cat.singleton (rel d m')) <> rel d r')
          (Just (rt, rh@(Run p'' ds'' ts'' es'' pr'')), Nothing) ->
            case joinAndCompare pr'' p' of
              Left _ -> error "boom 8b"
              Right _ -> case joinAndCompare p'' p' of
                Left _ -> error "boom 8b"
                Right LT | boring ts'' ->
                  let
                    (m'', r'') = shuffle d rh m' r'
                  in
                    V (d <> d') l m (rt <> Rev (Cat.singleton m'') <> r'')
                _ -> V (d <> d') l m (r <> Rev (revCat (Cat.singleton (rel d m'))) <> rel d r')
          (Nothing, Just (lh@(Run p''' ds''' ts''' es''' pr'''), lt)) ->
            case joinAndCompare pr p''' of
              Left _ -> error "boom 8b"
              Right _ -> case joinAndCompare p p''' of
                Left _ -> error "boom 8b"
                Right _
                  | boring ts -> (V d l (Run p (ds <> rel d ds''') (ts <> rel d ts''') (es <> rel d es''') pr''') Empty) <> (V d' lt m' r')
                  | otherwise -> V (d <> d') l m (Rev (revCat (rel d (l' <> Cat.singleton m'))) <> rel d r')
          (Just (rt, rh@(Run p'' ds'' ts'' es'' pr'')), Just (lh@(Run p''' ds''' ts''' es''' pr'''), lt)) ->
            case joinAndCompare pr'' p''' of
              Left _ -> error "boom 8d"
              Right _ -> case joinAndCompare p'' p''' of
                Left _ -> error "boom 8e"
                Right LT | boring ts'' -> (V d l m (review _Snoc (rt, Run p'' (ds'' <> rel d ds''') (ts'' <> rel d ts''') (es'' <> rel d es''') pr'''))) <> (V d' lt m' r')
                _ -> V (d <> d') l m (r <> Rev (revCat (rel d (l' <> Cat.singleton m'))) <> rel d r')

    -- --   ab
    --    c
    --      ed/Rde -- might last ed and head fg join up?
    -- --   fg
    --    h
    --      ji/Rij
        Right EQ -> case (preview _Snoc r, preview _Cons l') of
          (Nothing, Nothing) ->
            V (d <> d') l m (Rev (Cat.singleton (rel d m')) <> rel d r')
          (Just (rt, rh@(Run p'' ds'' ts'' es'' pr'')), Nothing) ->
            V (d <> d') l m (r <> Rev (Cat.singleton (rel d m')) <> rel d r')
          (Nothing, Just (lh@(Run p''' ds''' ts''' es''' pr'''), lt)) ->
            case joinAndCompare pr p''' of
              Left _ -> error "boom 8d"
              Right _ -> case joinAndCompare p p''' of
                Left _ -> error "boom 8e"
                Right _
                  | boring ts -> (V d l (Run p (ds <> rel d ds''') (ts <> rel d ts''') (es <> rel d es''') pr''') Empty) <> (V d' lt m' r')
                  | otherwise -> V (d <> d') l m (Rev (revCat (rel d l')) <> Rev (Cat.singleton (rel d m')) <> rel d r')
          (Just (rt, rh@(Run p'' ds'' ts'' es'' pr'')), Just (lh@(Run p''' ds''' ts''' es''' pr'''), lt)) ->
            case joinAndCompare pr'' p''' of
              Left _ -> error "boom 8d"
              Right _ -> case joinAndCompare p'' p''' of
                Left _ -> error "boom 8e"
                Right LT | boring ts'' -> (V d l m (review _Snoc (rt, Run p'' (ds'' <> rel d ds''') (ts'' <> rel d ts''') (es'' <> rel d es''') pr'''))) <> (V d' lt m' r')
                _ -> V (d <> d') l m (r <> Rev (rel d (revCat l')) <> Rev (Cat.singleton (rel d m')) <> rel d r')

    -- --     ab
    --      c
    --        ed/Rde -- might last ed and head fg join up?
    -- --   fg
    --    h
    --      ji/Rij
        Right GT -> case (preview _Snoc r, preview _Cons l') of
          (Nothing, Nothing) ->
            V (d <> d') (l <> Cat.singleton m) (rel d m') (rel d r')
          (Just (rt, rh@(Run p'' ds'' ts'' es'' pr'')), Nothing) ->
            V (d <> d') (l <> Cat.singleton m <> revCat rr) (rel d m') (rel d r')
          (Nothing, Just (lh@(Run p''' ds''' ts''' es''' pr'''), lt)) ->
            checkPrefixes pr p lh (\_ -> error "boom B") $ \case
              LT | boring ts -> (V d l (Run p (ds <> rel d ds''') (ts <> rel d ts''') (es <> rel d es''') pr''') Empty) <> V d' lt m' r'
              _ -> V (d <> d') (l <> Cat.singleton m <> rel d l') (rel d m') (rel d r')
          (Just (Rev rt, rh@(Run p'' ds'' ts'' es'' pr'')), Just (lh@(Run p''' ds''' ts''' es''' pr'''), lt)) ->
            checkPrefixes pr'' p'' lh (\_ -> error "boom A") $ \case
              LT | boring ts'' -> (V d l m (review _Snoc (Rev rt, Run p'' (ds'' <> rel d ds''') (ts'' <> rel d ts''') (es'' <> rel d es''') pr'''))) <> (V d' lt m' r')
              _ -> V (d <> d') (l <> Cat.singleton m <> revCat rr <> rel d l') (rel d m') (rel d r')

instance Monoid Layout where
  mempty = E 0
  mappend = (<>)
