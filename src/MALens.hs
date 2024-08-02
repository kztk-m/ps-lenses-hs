{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DerivingVia #-}
{-# HLINT ignore "Use tuple-section" #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

module MALens where

import Control.Applicative (liftA2)
import Control.Category
import Prelude hiding (id, (.))

import Control.Monad (zipWithM)
import Data.Map qualified as M
import Debug.Trace (trace)
import GHC.Stack (HasCallStack, callStack, getCallStack)

import Control.Arrow qualified
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

sndL :: (LowerBounded a) => MALens (a, b) b
sndL = MALens snd (\_ a -> pure (least, a))

eraseL :: MALens a ()
eraseL = MALens (const ()) (\s _ -> pure s)

eraseUnspecL :: (LowerBounded a) => MALens a ()
eraseUnspecL = MALens (const ()) (const $ const $ pure least)

dup :: (Lub a) => MALens a (a, a)
dup = MALens (\a -> (a, a)) (\_ ~(a1, a2) -> lub a1 a2)

merge :: (Glb a) => MALens (a, a) a
merge = MALens (\ ~(a1, a2) -> glb a1 a2) (\_ a -> pure (a, a))

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

constL :: (Eq b, Discrete b, LowerBounded a) => b -> MALens a b
constL b = MALens g p
  where
    g _ = b
    p a b'
      | b' == b = pure a
      | otherwise = err "constL: update on constant"

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

letM :: (CheckLeast b) => a -> MALens a b -> MALens (M a) b
letM def l = MALens g p
  where
    g (Some a) = get l a
    g (NoneWith s) = leastWith s

    p s v
      | isLeast v = pure None
      | otherwise = Some <$> put l (case s of None -> def; Some a -> a) v

-- >>> get (letMd undefined introMl) (Some $ Some "a")
-- >>> get (letMd undefined introMl) (Some None)
-- >>> get (letMd undefined introMl) None
-- Some (Some "a")
-- Some (NoneWith [])
-- NoneWith []
-- >>> put (letMd undefined introMl) undefined None
-- >>> put (letMd undefined introMl) undefined (Some None)
-- >>> put (letMd undefined introMl) undefined (Some $ Some "A")
-- Ok (NoneWith [])
-- Ok (Some (NoneWith []))
-- Ok (Some (Some "A"))

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
    p None (Some ~(b, c)) = err "Error: put snapshotM None (Some _)"

depLens :: (Discrete c) => MALens a c -> (c -> MALens d b) -> MALens (a, d) (c, b)
depLens l k = first l >>> swapL >>> snapshot k >>> swapL

liftMissing :: (HasCallStack) => MALens a b -> MALens (M a) (M b)
liftMissing l = MALens g p
  where
    g (Some x) = Some (get l x)
    g (NoneWith s) = NoneWith s

    p _ None = pure None
    p (Some s) (Some v) = Some <$> put l s v
    p None (Some _) = err $ "put liftMissing: None (Some _)\n" ++ show (getCallStack callStack)

liftMissingDefault :: a -> MALens a b -> MALens (M a) (M b)
liftMissingDefault a0 l = MALens g p
  where
    g (Some x) = Some (get l x)
    g (NoneWith s) = NoneWith s

    p _ None = pure None
    p (Some s) (Some v) = Some <$> put l s v
    p None (Some v) = Some <$> put l a0 v

-- assertEqL :: (Eq a, Discrete a) => a -> MALens (M a) (M ())
-- assertEqL a0 = MALens g p
--   where
--     g (Some a) | a == a0 = Some ()
--     g _ = None

--     p _ (Some _) = pure (Some a0)
--     p _ None = pure None

cond ::
  (Discrete c) =>
  MALens a (M c)
  -> (Maybe b -> c -> Err a)
  -> MALens b (M c)
  -> (Maybe a -> c -> Err b)
  -> (c -> Bool)
  -> MALens (M (Either a b)) (M c)
cond l1 r1 l2 r2 p = MALens getCond putCond
  where
    check phi (Some a) | phi a = Some a
    check _ _ = None

    getCond (Some (Left a)) =
      check p (get l1 a)
    getCond (Some (Right b)) =
      check (not . p) (get l2 b)
    getCond None = None
    putCond _ None = pure None
    putCond s (Some c)
      | p c = do
          src <- case s of
            Some (Left a) -> pure a
            Some (Right b) -> r1 (Just b) c
            None -> r1 Nothing c
          a' <- put l1 src (Some c)
          pure (Some (Left a'))
      | otherwise = do
          src <- case s of
            Some (Left a) -> r2 (Just a) c
            Some (Right b) -> pure b
            None -> r2 Nothing c
          b' <- put l2 src (Some c)
          pure (Some (Right b'))
