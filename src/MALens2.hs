{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

{-# HLINT ignore "Use tuple-section" #-}

module MALens2 where

import Control.Applicative (liftA2)
import Control.Category
import Prelude hiding (id, (.))

import Control.Monad (zipWithM)
import qualified Data.Map as M
import Debug.Trace (trace)
import GHC.Stack (HasCallStack, callStack, getCallStack)

import Control.Monad.Reader

import Domain
import Err

data Galois a b = Galois {leftAdjoint :: a -> Err b, rightAdjoint :: b -> Err a}

data MALens a b = MALens {get :: a -> b, putM :: b -> ReaderT (Maybe a) Err a}

getOrig :: ReaderT (Maybe a) Err a
getOrig = do
  m <- ask
  case m of
    Just a -> pure a
    Nothing -> lift $ err "the original source is unavailable here"

put :: MALens a b -> a -> b -> Err a
put l a b = runReaderT (putM l b) (Just a)

unget :: MALens a b -> b -> Err a
unget l b = runReaderT (putM l b) Nothing

-- When Galois a b is a pair of isomorphism (invertible homomorphisms), then it can be
-- inverted
invert :: Galois a b -> Galois b a
invert (Galois f g) = Galois g f

idL :: MALens a a
idL = MALens id pure

instance Category MALens where
  id = idL

  (.) :: forall a b c. MALens b c -> MALens a b -> MALens a c
  l2 . l1 = MALens (get l2 . get l1) p
    where
      p :: c -> ReaderT (Maybe a) Err a
      p c = do
        b' <- withReaderT (fmap (get l1)) $ putM l2 c
        putM l1 b'

liftMissing :: forall a b. (HasCallStack) => MALens a b -> MALens (M a) (M b)
liftMissing l = MALens g p
  where
    g (NoneWith s) = NoneWith s
    g (Some a) = Some $ get l a

    ext :: Maybe (M a) -> Maybe a
    ext x =
      x >>= \case
        Some a -> pure a
        _ -> Nothing

    p :: M b -> ReaderT (Maybe (M a)) Err (M a)
    p None = pure None
    p (Some b) =
      fmap Some
        $ withReaderT ext
        $ putM l b

-- >>> put (liftMissing id) None (Some 1)
-- Ok (Some 1)

(***) :: MALens a c -> MALens b d -> MALens (a, b) (c, d)
l1 *** l2 = MALens g p
  where
    g (a, b) = (get l1 a, get l2 b)
    p (c, d) =
      let r1 = withReaderT (fmap fst) $ putM l1 c
          r2 = withReaderT (fmap snd) $ putM l2 d
      in  liftA2 (,) r1 r2

first :: MALens a c -> MALens (a, d) (c, d)
first l = l *** id
second :: MALens b d -> MALens (c, b) (c, d)
second l = id *** l

swapL :: MALens (a, b) (b, a)
swapL = MALens sw (pure . sw)
  where
    sw (x, y) = (y, x)

assocToRightL :: MALens ((a, b), c) (a, (b, c))
assocToRightL = MALens f g
  where
    f ((a, b), c) = (a, (b, c))
    g (a, (b, c)) = pure ((a, b), c)

assocToLeftL :: MALens (a, (b, c)) ((a, b), c)
assocToLeftL = MALens f g
  where
    f (a, (b, c)) = ((a, b), c)
    g ((a, b), c) = pure (a, (b, c))

fstL :: (LowerBounded b) => MALens (a, b) a
fstL = MALens fst (\a -> pure (a, least))

sndL :: (LowerBounded a) => MALens (a, b) b
sndL = MALens snd (\a -> pure (least, a))

dup :: (Lub a) => MALens a (a, a)
dup = MALens (\a -> (a, a)) (\(a1, a2) -> lift $ lub a1 a2)

liftGalois :: Galois b a -> MALens (M a) (M b)
liftGalois galois = MALens g p
  where
    g (NoneWith s) = NoneWith s
    g (Some y) =
      case rightAdjoint galois y of
        Ok x -> Some x
        Err s -> NoneWith s

    p None = pure None
    p (Some x) = lift $ Some <$> leftAdjoint galois x

leftLflat :: MALens a (Either a b)
leftLflat = MALens g p
  where
    g = Left
    p (Left a) = pure a
    p (Right _) = lift $ err "leftLflat: updated to right"

rightLflat :: MALens b (Either a b)
rightLflat = MALens g p
  where
    g = Right
    p (Right a) = pure a
    p (Left _) = lift $ err "rightLflat: updated to left"

dist :: MALens (M (Either a b, c)) (M (Either (a, c) (b, c)))
dist = liftGalois $ Galois g f
  where
    f (Left a, c) = pure $ Left (a, c)
    f (Right b, c) = pure $ Right (b, c)

    g (Left (a, c)) = pure (Left a, c)
    g (Right (b, c)) = pure (Right b, c)

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
    p b'
      | b' == b = getOrig
      | otherwise = lift $ err "constL: update on constant"

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
    (\x -> trace ("bwd" <> ss <> ": " <> show x) (pure x))
  where
    ss = if null s then "" else "[" ++ s ++ "]"

pairM :: MALens (M a, M b) (M (a, b))
pairM = MALens g p
  where
    g (a, b) = liftA2 (,) a b
    p (Some (a, b)) = pure (Some a, Some b)
    p None = pure (None, None)

introM :: (Discrete a) => MALens a (M a)
introM = MALens Some $ \case
  Some a -> pure a
  None -> getOrig

defaultL :: (Discrete a) => MALens a (M a)
defaultL = introM

introMLb :: (LowerBounded a) => MALens a (M a)
introMLb = MALens Some $ \case
  Some a -> pure a
  None -> pure least

joinM :: (CheckLeast a) => MALens (M a) a
joinM = MALens g p
  where
    g (Some a) = a
    g None = least
    p a
      | isLeast a = pure None
      | otherwise = pure $ Some a

deleteUnit :: MALens ((), a) a
deleteUnit = MALens snd (\a -> pure ((), a))

introUnit :: MALens a ((), a)
introUnit = MALens (\a -> ((), a)) (pure . snd)

snapshot :: (Discrete c) => (c -> MALens a b) -> MALens (a, c) (b, c)
snapshot k = MALens g p
  where
    g (a, c) = (get (k c) a, c)
    p (b, c) = do
      a' <- withReaderT (fmap fst) $ putM (k c) b
      pure (a', c)

snapshotMissing ::
  forall a b c.
  (Discrete c) =>
  (c -> MALens a b)
  -> MALens (M (a, M c)) (M (b, c))
snapshotMissing k = MALens g p
  where
    g (NoneWith s) = NoneWith s
    g (Some (_, NoneWith s)) = NoneWith s
    g (Some (a, Some c)) = Some (get (k c) a, c)

    ext :: Maybe (M (a, M c)) -> Maybe a
    ext x =
      x >>= \case
        Some (a, _) -> Just a
        _ -> Nothing

    p :: M (b, c) -> ReaderT (Maybe (M (a, M c))) Err (M (a, M c))
    p None = pure None
    p (Some (b, c)) = do
      a' <- withReaderT ext $ putM (k c) b
      pure (Some (a', Some c))