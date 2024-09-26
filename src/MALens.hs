{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# HLINT ignore "Use tuple-section" #-}
{-# OPTIONS_GHC -Wno-missing-export-lists #-}
{-# OPTIONS_GHC -Wno-redundant-constraints #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

module MALens where

import Control.Category
import Prelude hiding (id, (.))

import Debug.Trace (trace)
import GHC.Stack (HasCallStack, callStack, getCallStack)

import Data.Coerce (coerce)
import Domain
import Err

data MALens a b = MALens {get :: a -> b, put :: a -> b -> Err a}
data Galois a b = Galois {leftAdjoint :: a -> Err b, rightAdjoint :: b -> Err a}

-- When Galois a b is a pair of isomorphism (invertible homomorphisms), then it can be
-- inverted
invert :: Galois a b -> Galois b a
invert (Galois f g) = Galois g f

idL :: MALens a a
idL = MALens id (\_ b -> pure b)

instance Category MALens where
  id = idL

  l2 . l1 = MALens (get l2 . get l1) p
    where
      p a c = do
        let b = get l1 a
        b' <- put l2 b c
        put l1 a b'

(***) :: MALens a c -> MALens b d -> MALens (a, b) (c, d)
l1 *** l2 = MALens g p
  where
    g ~(a, b) = (get l1 a, get l2 b)
    p ~(a, b) ~(c, d) = liftA2 (,) (put l1 a c) (put l2 b d)

first :: MALens a c -> MALens (a, d) (c, d)
first l = l *** id
second :: MALens b d -> MALens (c, b) (c, d)
second l = id *** l

swapL :: MALens (a, b) (b, a)
swapL = MALens sw (const $ pure . sw)
  where
    sw ~(x, y) = (y, x)

swapM :: MALens (M (a, b)) (M (b, a))
swapM = liftGalois $ Galois sw sw
  where
    sw ~(x, y) = pure (y, x)

assocToRightL :: MALens ((a, b), c) (a, (b, c))
assocToRightL = MALens f g
  where
    f ~(~(a, b), c) = (a, (b, c))
    g _ ~(a, ~(b, c)) = pure ((a, b), c)

assocToLeftL :: MALens (a, (b, c)) ((a, b), c)
assocToLeftL = MALens f g
  where
    f ~(a, ~(b, c)) = ((a, b), c)
    g _ ~(~(a, b), c) = pure (a, (b, c))

fstL :: (LowerBounded b) => MALens (a, b) a
fstL = MALens fst (\_ a -> pure (a, least))

fstL' :: MALens (a, b) a
fstL' = second eraseL >>> fstL

sndL' :: MALens (a, b) b
sndL' = first eraseL >>> sndL

sndL :: (LowerBounded a) => MALens (a, b) b
sndL = MALens snd (\_ a -> pure (least, a))

eraseL :: MALens a ()
eraseL = MALens (const ()) (\s _ -> pure s)

eraseUnspecL :: (LowerBounded a) => MALens a ()
eraseUnspecL = MALens (const ()) (const $ const $ pure least)

dup :: (Lub a) => MALens a (a, a)
dup = MALens (\a -> (a, a)) (\_ ~(a1, a2) -> lub a1 a2)

dupW :: WitLub a -> MALens a (a, a)
dupW w = MALens (\a -> (a, a)) (\_ ~(a1, a2) -> lubWith w a1 a2)

merge :: (Glb a) => MALens (a, a) a
merge = MALens (\ ~(a1, a2) -> glb a1 a2) (\_ a -> pure (a, a))

mergeW :: WitGlb a -> MALens (a, a) a
mergeW w = MALens (\ ~(a1, a2) -> glbWith w a1 a2) (\_ a -> pure (a, a))

-- >>> get (merge >>> dup) (Some 1 :: M Int, Some 1)
-- >>> get (merge >>> dup) (Some 1 :: M Int, Some 2)
-- >>> get (merge >>> dup) (Some 1 :: M Int, None)
-- (Some 1,Some 1)
-- (NoneWith ["glb': no glb for diffrent elements in a discrete domain."],NoneWith ["glb': no glb for diffrent elements in a discrete domain."])
-- (NoneWith [],NoneWith [])
-- >>> put (merge >>> dup) undefined (Some 1 :: M Int, Some 1)
-- >>> put (merge >>> dup) undefined (Some 1 :: M Int, Some 2)
-- >>> put (merge >>> dup) undefined (Some 1 :: M Int, None)
-- Ok (Some 1,Some 1)
-- Err ["lub: no lub for different elements in a disrete domain."]
-- Ok (Some 1,Some 1)

-- >>> get (dup >>> merge) None
-- >>> get (dup >>> merge) (Some 1 :: M Int)
-- NoneWith []
-- Some 1

-- >>> put (dup >>> merge) undefined None
-- >>> put (dup >>> merge) undefined (Some 1 :: M Int)
-- Ok (NoneWith [])
-- Ok (Some 1)

liftGalois :: Galois b a -> MALens (M a) (M b)
liftGalois galois = MALens g p
  where
    g (NoneWith s) = NoneWith s
    g (Some y) =
      case rightAdjoint galois y of
        Ok x -> Some x
        Err s -> NoneWith s

    p _ None = pure None
    p _ (Some x) = Some <$> leftAdjoint galois x

leftLflat :: MALens a (Either a b)
leftLflat = MALens g p
  where
    g = Left
    p _ (Left a) = pure a
    p _ (Right _) = err "leftLflat: updated to right"

rightLflat :: MALens b (Either a b)
rightLflat = MALens g p
  where
    g = Right
    p _ (Right a) = pure a
    p _ (Left _) = err "rightLflat: updated to left"

dist :: MALens (M (Either a b, c)) (M (Either (a, c) (b, c)))
dist = liftGalois $ Galois g f
  where
    f ~(x, c) = case x of
      Left a -> pure $ Left (a, c)
      Right b -> pure $ Right (b, c)

    g (Left ~(a, c)) = pure (Left a, c)
    g (Right ~(b, c)) = pure (Right b, c)

leftL :: MALens (M a) (M (Either a b))
leftL = liftGalois $ Galois fromLeft toLeft
  where
    fromLeft (Left a) = pure a
    fromLeft (Right _) = err "fromLeft: got right"

    toLeft a = pure $ Left a

rightL :: MALens (M b) (M (Either a b))
rightL = liftGalois $ Galois fromRight toRight
  where
    fromRight (Left _) = err "fromRight: got left"
    fromRight (Right a) = pure a

    toRight = pure . Right

constLunit :: (Eq a, Discrete a) => a -> MALens (M ()) (M a)
constLunit c = liftGalois $ Galois g f
  where
    f _ = pure c
    g x
      | x == c = pure ()
      | otherwise = err "constLunit: update on constant"

constLns :: (Eq a, Discrete a) => a -> MALens (M ()) (M a)
constLns c = MALens g p
  where
    g _ = pure c
    p s (Some v)
      | c == v = pure s
      | otherwise = err "constLns: updated on constant"
    p s None = pure s

constL :: (Eq b, Discrete b, LowerBounded a) => b -> MALens a b
constL b = MALens g p
  where
    g _ = b
    p a b'
      | b' == b = pure a
      | otherwise = err "constL: update on constant"

-- >>> get (assertEqL (1 :: Int)) (Some 1)
-- >>> get (assertEqL (1 :: Int)) (Some 2)
-- >>> get (assertEqL (1 :: Int)) None
-- Some ()
-- NoneWith ["assertEqL: update on constant"]
-- NoneWith []

-- >>> put (assertEqL (1 :: Int)) undefined None
-- >>> put (assertEqL (1 :: Int)) undefined (Some ())
-- Ok (NoneWith [])
-- Ok (Some 1)

assertEqL :: (Eq a) => a -> MALens (M a) (M ())
assertEqL c = liftGalois $ Galois f g
  where
    f _ = pure c
    g x
      | x == c = pure ()
      | otherwise = err "assertEqL: update on constant"

inspectL :: (Show a) => String -> MALens a a
inspectL s =
  MALens
    (\x -> trace ("fwd" <> ss <> ": " <> show x) x)
    (const $ \x -> trace ("bwd" <> ss <> ": " <> show x) (pure x))
  where
    ss = if null s then "" else "[" ++ s ++ "]"

pairM :: MALens (M a, M b) (M (a, b))
pairM = MALens g p
  where
    g ~(a, b) = liftA2 (,) a b
    p _ (Some ~(a, b)) = pure (Some a, Some b)
    p _ None = pure (None, None)

introM :: (Templatable a) => MALens a (M a)
introM = MALens Some $ \s v -> case v of
  Some a -> pure a
  None -> pure (template s)

introMd :: (Discrete a) => MALens a (M a)
introMd = MALens Some $ \s v -> case v of
  Some a -> pure a
  None -> pure s

introMl :: (LowerBounded a) => MALens a (M a)
introMl = MALens Some $ \_ v -> case v of
  Some a -> pure a
  None -> pure least

joinM :: (CheckLeast a) => MALens (M a) a
joinM = letM least id

letMWith ::
  (CheckLeast b) =>
  (b -> Err a)
  -> MALens a b
  -> MALens (M a) b
letMWith adj l = MALens g p
  where
    g (Some a) = get l a
    g (NoneWith s) = leastWith s

    p s v
      | isLeast v = pure None
      | otherwise = do
          a_adjusted <- case s of None -> adj v; Some a -> pure a
          Some <$> put l a_adjusted v

letM :: (CheckLeast b) => a -> MALens a b -> MALens (M a) b
letM def = letMWith (const $ pure def)

-- A variant of letM whose put fails when the original source is missing.
letM' :: (CheckLeast b) => MALens a b -> MALens (M a) b
letM' = letMWith (const $ err "letM': source is missing")

bindMWith :: (t -> Err a) -> MALens a (M t) -> MALens (M a) (M t)
bindMWith adj = letMWith (\v -> case v of None -> err "Cannot happen."; Some b -> adj b)

-- A specialized version of sndL (recall that () is an instance of LowerBounded)
-- Also, sndL can be defined via deleteUnit as:
--
-- prop> sndL == (eraseUnspecL *** id) >>> deleteUnit

deleteUnit :: MALens ((), a) a
deleteUnit = MALens snd (const $ \a -> pure ((), a))

deleteUnitM :: MALens (M ((), b)) (M b)
deleteUnitM = liftGalois $ Galois (\a -> pure ((), a)) (\(_, a) -> pure a)

introUnit :: MALens a ((), a)
introUnit = MALens (\a -> ((), a)) (const $ pure . snd)

snapshot :: (Discrete c) => (c -> MALens a b) -> MALens (a, c) (b, c)
snapshot k = MALens g p
  where
    g ~(a, c) = (get (k c) a, c)
    p ~(a, _) ~(b, c) = do
      a' <- put (k c) a b
      pure (a', c)

newtype OrderInd a b = OrderInd {runOrderInd :: a -> b}

snapshotO :: OrderInd c (MALens a b) -> MALens (a, c) (b, c)
snapshotO k = MALens g p
  where
    g ~(a, c) = (get (runOrderInd k c) a, c)
    p ~(a, _) ~(b, c) = do
      a' <- put (runOrderInd k c) a b
      pure (a', c)

snapshotM ::
  (Discrete c) =>
  (c -> MALens a b)
  -> MALens (M (a, M c)) (M (b, c))
snapshotM k = MALens g p
  where
    g None = None
    g (Some ~(a, y)) = case y of
      None -> None
      Some c -> Some (get (k c) a, c)

    p _ None = pure None
    p (Some ~(a, _)) (Some ~(b, c)) = do
      a' <- put (k c) a b
      pure $ Some (a', Some c)
    p None (Some ~(_, _)) = err "Error: put snapshotM None (Some _)"

depLens :: (Discrete c) => MALens a c -> (c -> MALens d b) -> MALens (a, d) (c, b)
depLens l k = first l >>> swapL >>> snapshot k >>> swapL

liftMWith :: (b -> Err a) -> MALens a b -> MALens (M a) (M b)
liftMWith adj l = MALens g p
  where
    g (Some x) = Some (get l x)
    g (NoneWith s) = NoneWith s

    p _ None = pure None
    p s (Some v) = do
      a_adjusted <- case s of None -> adj v; Some a -> pure a
      Some <$> put l a_adjusted v

liftMissing :: (HasCallStack) => MALens a b -> MALens (M a) (M b)
liftMissing = liftMWith (const $ err $ "put liftMissing: None (Some _)\n" ++ show (getCallStack callStack))

liftMissingDefault :: a -> MALens a b -> MALens (M a) (M b)
liftMissingDefault a0 = liftMWith (const $ pure a0)

newtype Monotone a b = EnsureMonotone {applyMonotone :: a -> b}

monoFromDisc :: (Discrete a, Discrete b) => (a -> b) -> Monotone a b
monoFromDisc = EnsureMonotone

unTag :: Monotone a Bool -> MALens (M (Either a a)) (M a)
unTag phi = MALens g p
  where
    g (Some (Left a)) = if applyMonotone phi a then Some a else NoneWith ["unTag: postcondition check failed (got False, expected True)"]
    g (Some (Right b)) = if applyMonotone phi b then NoneWith ["unTag: postcondition check failed (got True, expected False)"] else Some b
    g (NoneWith s) = NoneWith s

    p _ None = pure None
    p _ (Some v) =
      pure $ Some $ if applyMonotone phi v then Left v else Right v

unTagS :: MALens (Either a a) a
unTagS = MALens g p
  where
    g = either id id

    p (Left _) = pure . Left
    p (Right _) = pure . Right

sumM :: MALens (Either (M a) (M b)) (M (Either a b))
sumM = MALens g p
  where
    g (Left None) = None
    g (Left (Some a)) = Some (Left a)
    g (Right None) = None
    g (Right (Some b)) = Some (Right b)

    p _ (Some (Left a)) = pure $ Left $ Some a
    p _ (Some (Right b)) = pure $ Right $ Some b
    p s None = case s of
      Left _ -> pure $ Left None
      Right _ -> pure $ Right None

mapSumL ::
  MALens a c
  -> MALens b d
  -> (b -> c -> Err a)
  -> (a -> d -> Err b)
  -> MALens (Either a b) (Either c d)
mapSumL l1 l2 r1 r2 = MALens g p
  where
    g (Left a) = Left $ get l1 a
    g (Right b) = Right $ get l2 b

    p (Left a) (Left c) = Left <$> put l1 a c
    p (Left a) (Right d) = do
      b <- r2 a d
      Right <$> put l2 b d
    p (Right b) (Left c) = do
      a <- r1 b c
      Left <$> put l1 a c
    p (Right b) (Right d) = Right <$> put l2 b d

scond :: MALens a c -> MALens b c -> MALens (Either a b) c
scond l1 l2 = mapSumL l1 l2 r r >>> unTagS
  where
    r _ _ = err "scond: cannot switch branches."

cond ::
  MALens a (M c)
  -> (Maybe b -> c -> Err a)
  -> MALens b (M c)
  -> (Maybe a -> c -> Err b)
  -> Monotone c Bool
  -> MALens (M (Either a b)) (M c)
cond l1 r1 l2 r2 p = bindMWith adj (mapSumL l1 l2 r1' r2' >>> sumM) >>> unTag p
  where
    adj (Left c) = Left <$> r1 Nothing c
    adj (Right c) = Right <$> r2 Nothing c

    r1' _ None = err "cond: cannot determine branch" -- cannot happen, as bindMWith adj l bypasses l when the updated view is None
    r1' b (Some c) = r1 (Just b) c

    r2' _ None = err "cond: cannot determine branch" -- cannot happen (ditto)
    r2' b (Some c) = r2 (Just b) c

condD ::
  (Discrete c) =>
  MALens a (M c)
  -> (Maybe b -> c -> Err a)
  -> MALens b (M c)
  -> (Maybe a -> c -> Err b)
  -> (c -> Bool)
  -> MALens (M (Either a b)) (M c)
condD l1 r1 l2 r2 p = cond l1 r1 l2 r2 (monoFromDisc p)
