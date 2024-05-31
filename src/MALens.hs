{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

{-# HLINT ignore "Use tuple-section" #-}

module MALens where

import Control.Applicative (liftA2)
import Control.Category
import Prelude hiding (id, (.))

import Control.Monad (zipWithM)
import qualified Data.Map as M
import Debug.Trace (trace)

data Err a = Err [String] | Ok a deriving (Show)

err :: String -> Err a
err s = Err [s]

instance Functor Err where
  fmap _ (Err s) = Err s
  fmap f (Ok a) = Ok (f a)

instance Applicative Err where
  pure = Ok
  Err s <*> Err t = Err (s ++ t)
  Err s <*> Ok _ = Err s
  Ok _ <*> Err t = Err t
  Ok f <*> Ok v = Ok (f v)

instance Monad Err where
  return = pure
  Err s >>= _ = Err s
  Ok a >>= f = f a

class LowerBounded a where
  least :: a

class (LowerBounded a) => CheckLeast a where
  isLeast :: a -> Bool

class Lub a where
  lub :: a -> a -> Err a

instance Lub () where
  lub _ _ = pure ()

instance (Lub a, Lub b) => Lub (a, b) where
  lub (a1, b1) (a2, b2) = liftA2 (,) (lub a1 a2) (lub b1 b2)

instance (Lub a, Lub b) => Lub (Either a b) where
  lub (Left a) (Left a') = Left <$> lub a a'
  lub (Right b) (Right b') = Right <$> lub b b'
  lub _ _ = err "lub: expects elements with the same tags"

instance (Lub a) => Lub [a] where
  lub xs ys
    | length xs == length ys = zipWithM lub xs ys
    | otherwise = err "lub: lists with different lengths"

instance (Lub a) => Lub (M a) where
  lub None m = pure m
  lub m None = pure m
  lub (Some a) (Some b) = Some <$> lub a b

newtype EqDisc a = EqDisc a deriving (Eq)

instance (Discrete a, Eq a) => Lub (EqDisc a) where
  lub a b = if a == b then pure a else err "lub: failed"
deriving via EqDisc Int instance Lub Int
deriving via EqDisc Double instance Lub Double
deriving via EqDisc Bool instance Lub Bool
deriving via EqDisc Char instance Lub Char

class Discrete a

instance Discrete ()
instance Discrete Int
instance Discrete Double
instance Discrete Bool
instance Discrete Char
instance (Discrete a, Discrete b) => Discrete (Either a b)
instance (Discrete a, Discrete b) => Discrete (a, b)
instance (Discrete a) => Discrete [a]
instance (Discrete k, Discrete v) => Discrete (M.Map k v)

-- Another name of Maybe
data M a = None | Some a deriving (Show, Eq, Functor)

instance Applicative M where
  pure = Some
  Some f <*> Some a = Some (f a)
  _ <*> _ = None

instance LowerBounded () where
  least = ()

instance CheckLeast () where
  isLeast _ = True

instance LowerBounded (M a) where
  least = None
instance CheckLeast (M a) where
  isLeast None = True
  isLeast _ = False

instance (LowerBounded a, LowerBounded b) => LowerBounded (a, b) where
  least = (least, least)

instance (CheckLeast a, CheckLeast b) => CheckLeast (a, b) where
  isLeast (a, b) = isLeast a && isLeast b

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
    g (a, b) = (get l1 a, get l2 b)
    p (a, b) (c, d) = liftA2 (,) (put l1 a c) (put l2 b d)

first :: MALens a c -> MALens (a, d) (c, d)
first l = l *** id
second :: MALens b d -> MALens (c, b) (c, d)
second l = id *** l

swapL :: MALens (a, b) (b, a)
swapL = MALens sw (const $ pure . sw)
  where
    sw (x, y) = (y, x)

assocToRightL :: MALens ((a, b), c) (a, (b, c))
assocToRightL = MALens f g
  where
    f ((a, b), c) = (a, (b, c))
    g _ (a, (b, c)) = pure ((a, b), c)

assocToLeftL :: MALens (a, (b, c)) ((a, b), c)
assocToLeftL = MALens f g
  where
    f (a, (b, c)) = ((a, b), c)
    g _ ((a, b), c) = pure (a, (b, c))

fstL :: (LowerBounded b) => MALens (a, b) a
fstL = MALens fst (\_ a -> pure (a, least))

sndL :: (LowerBounded a) => MALens (a, b) b
sndL = MALens snd (\_ a -> pure (least, a))

dup :: (Lub a) => MALens a (a, a)
dup = MALens (\a -> (a, a)) (\_ (a1, a2) -> lub a1 a2)

liftGalois :: Galois b a -> MALens (M a) (M b)
liftGalois galois = MALens g p
  where
    g None = None
    g (Some y) =
      case rightAdjoint galois y of
        Ok x -> Some x
        Err _ -> None

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

-- Check: do we need Discrete a?
constL :: (Eq a) => a -> MALens (M ()) (M a)
constL c = liftGalois $ Galois g f
  where
    f _ = pure c
    g x
      | x == c = pure ()
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
    g (a, b) = liftA2 (,) a b
    p _ (Some (a, b)) = pure (Some a, Some b)
    p _ None = pure (None, None)

introM :: (Discrete a) => MALens a (M a)
introM = MALens Some $ \s v -> case v of
  Some a -> pure a
  None -> pure s

introMLb :: (LowerBounded a) => MALens a (M a)
introMLb = MALens Some $ \_ v -> case v of
  Some a -> pure a
  None -> pure least

joinM :: (CheckLeast a) => MALens (M a) a
joinM = MALens g p
  where
    g (Some a) = a
    g None = least
    p _ a
      | isLeast a = pure None
      | otherwise = pure $ Some a

deleteUnit :: MALens ((), a) a
deleteUnit = MALens snd (const $ \a -> pure ((), a))

introUnit :: MALens a ((), a)
introUnit = MALens (\a -> ((), a)) (const $ pure . snd)

snapshot :: (Discrete c) => (c -> MALens a b) -> MALens (a, c) (b, c)
snapshot k = MALens g p
  where
    g (a, c) = (get (k c) a, c)
    p (a, _) (b, c) = do
      a' <- put (k c) a b
      pure (a', c)

snapshotMissing ::
  (Discrete c, LowerBounded a) =>
  (c -> MALens a b)
  -> MALens (a, M c) (M (b, c))
snapshotMissing k = MALens g p
  where
    g (_, None) = None
    g (a, Some c) = Some (get (k c) a, c)

    p (_, _) None = pure (least, None)
    p (a, _) (Some (b, c)) = do
      a' <- put (k c) a b
      pure (a', Some c)

depLens :: (Discrete c) => MALens a c -> (c -> MALens d b) -> MALens (a, d) (c, b)
depLens l k = first l >>> swapL >>> snapshot k >>> swapL

liftMissing :: MALens a b -> MALens (M a) (M b)
liftMissing l = MALens g p
  where
    g (Some x) = Some (get l x)
    g None = None

    p _ None = pure None
    p (Some s) (Some v) = Some <$> put l s v
    p None (Some _) = err "put liftMissing: None (Some _)"

liftMissingDefault :: a -> MALens a b -> MALens (M a) (M b)
liftMissingDefault a0 l = MALens g p
  where
    g (Some x) = Some (get l x)
    g None = None

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
