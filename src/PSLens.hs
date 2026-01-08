{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# HLINT ignore "Use tuple-section" #-}
{-# OPTIONS_GHC -Wno-missing-export-lists #-}
{-# OPTIONS_GHC -Wno-redundant-constraints #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

module PSLens where

import Control.Category
import Prelude hiding (id, (.))

import Debug.Trace (trace)

import Control.Monad ((<=<))
import Domain
import Err

-- | ps-lens (without laws)
data PSLens a b = PSLens {get :: a -> Err b, put :: a -> b -> Err a}

-- | Galois connections (without laws)
data Galois a b = Galois {leftAdjoint :: a -> Err b, rightAdjoint :: b -> Err a}

-- | The identity lens
idL :: PSLens a a
idL = PSLens pure (\_ b -> pure b)

-- Technically, for a ps-lens to be a category, it must satisfy:
--
-- put s v == Just _ ==> get s == Just _
--
-- We can replace `b <- get l1 a` with
--
--   b <- Just $ case get l1 a of { Just res -> res ; Nothing -> undefined }
--
-- to make ps-lens unconditionally form a category, but we ignore this.
--
-- Or, we can use a bit different definition.
--
-- data PSLens a b = PSLens (a -> Err (b, b -> Err a))

instance Category PSLens where
  id = idL

  l2 . l1 = PSLens (get l2 <=< get l1) p
    where
      p a c = do
        b <- get l1 a
        b' <- put l2 b c
        put l1 a b'

-- In the paper, this operator is written as \times
(***) :: PSLens a c -> PSLens b d -> PSLens (a, b) (c, d)
l1 *** l2 = PSLens g p
  where
    g ~(a, b) = liftA2 (,) (get l1 a) (get l2 b)
    p ~(a, b) ~(c, d) = liftA2 (,) (put l1 a c) (put l2 b d)

first :: PSLens a c -> PSLens (a, d) (c, d)
first l = l *** id
second :: PSLens b d -> PSLens (c, b) (c, d)
second l = id *** l

-- Lenses for pairs
swapL :: PSLens (a, b) (b, a)
swapL = PSLens sw (const sw)
  where
    sw ~(x, y) = pure (y, x)

assocToRightL :: PSLens ((a, b), c) (a, (b, c))
assocToRightL = PSLens f g
  where
    f ~(~(a, b), c) = pure (a, (b, c))
    g _ ~(a, ~(b, c)) = pure ((a, b), c)

assocToLeftL :: PSLens (a, (b, c)) ((a, b), c)
assocToLeftL = PSLens f g
  where
    f ~(a, ~(b, c)) = pure ((a, b), c)
    g _ ~(~(a, b), c) = pure (a, (b, c))

fstL :: (LowerBounded b) => PSLens (a, b) a
fstL = PSLens (pure . fst) (\_ a -> pure (a, least))

fstL' :: PSLens (a, b) a
fstL' = second eraseL >>> fstL

sndL' :: PSLens (a, b) b
sndL' = first eraseL >>> sndL

sndL :: (LowerBounded a) => PSLens (a, b) b
sndL = PSLens (pure . snd) (\_ a -> pure (least, a))

eraseL :: PSLens a ()
eraseL = PSLens (const $ pure ()) (\s _ -> pure s)

--- Special case of the constant lens
eraseUnspecL :: (LowerBounded a) => PSLens a ()
eraseUnspecL = PSLens (const $ pure ()) (const $ const $ pure least)

eraseTemplateL :: (Templatable a) => PSLens a ()
eraseTemplateL = PSLens (const $ pure ()) (const . pure . template)

constL :: (LowerBounded s, CheckIdentical a) => a -> PSLens s a
constL a =
  PSLens
    { get = pure . const a
    , put = const $ \case
        v
          | identicalAt v a -> pure least
          | otherwise -> err "constL: non identical update on a constant."
    }

-- | The duplication lens
dup :: (Lub a) => PSLens a (a, a)
dup = PSLens (\a -> pure (a, a)) (\_ ~(a1, a2) -> lub a1 a2)

dupW :: WitLub a -> PSLens a (a, a)
dupW w = PSLens (\a -> pure (a, a)) (\_ ~(a1, a2) -> lubWith w a1 a2)

{-
Several lens primitives and combinators.

Most of them are NOT mentioned in our ESOP 2026 paper except unTagS.
-}

-- | The dual of the duplication lens. This is not useful as `dup`. The fact
-- that put-then-get is enough for synchronization means that we are not able to
-- source-to-source update propagation---if both are allowed, we are not able to
-- bound the number of round-trips.
merge :: (Glb a) => PSLens (a, a) a
merge = PSLens (\ ~(a1, a2) -> pure $ glb a1 a2) (\_ a -> pure (a, a))

mergeW :: WitGlb a -> PSLens (a, a) a
mergeW w = PSLens (\ ~(a1, a2) -> pure $ glbWith w a1 a2) (\_ a -> pure (a, a))

-- >>> get (merge >>> dup) (Some 1 :: M Int, Some 1)
-- >>> get (merge >>> dup) (Some 1 :: M Int, Some 2)
-- >>> get (merge >>> dup) (Some 1 :: M Int, None)
-- Ok (Some 1,Some 1)
-- Ok (NoneWith ["no glb for different elements in a disrete domain."],NoneWith ["no glb for different elements in a disrete domain."])
-- Ok (NoneWith [],NoneWith [])
-- >>> put (merge >>> dup) undefined (Some 1 :: M Int, Some 1)
-- >>> put (merge >>> dup) undefined (Some 1 :: M Int, Some 2)
-- >>> put (merge >>> dup) undefined (Some 1 :: M Int, None)
-- Prelude.undefined
-- Prelude.undefined
-- Prelude.undefined

-- >>> get (dup >>> merge) None
-- >>> get (dup >>> merge) (Some 1 :: M Int)
-- Ok (NoneWith [])
-- Ok (Some 1)

-- >>> put (dup >>> merge) undefined None
-- >>> put (dup >>> merge) undefined (Some 1 :: M Int)
-- Ok (NoneWith [])
-- Ok (Some 1)

leftLflat :: PSLens a (Either a b)
leftLflat = PSLens g p
  where
    g = pure . Left
    p _ (Left a) = pure a
    p _ (Right _) = err "leftLflat: updated to right"

rightLflat :: PSLens b (Either a b)
rightLflat = PSLens g p
  where
    g = pure . Right
    p _ (Right a) = pure a
    p _ (Left _) = err "rightLflat: updated to left"

-- For debugging
withInspect :: (Show a, Show b) => PSLens a b -> String -> PSLens a b
withInspect l str =
  PSLens
    (\s -> trace ("fwd" <> ss <> ": " <> show s) $ get l s)
    (\s v -> trace ("bwd" <> ss <> ": " <> show s <> " | " <> show v) $ put l s v)
  where
    ss = if null str then "" else "[" ++ str ++ "]"

inspectL :: (Show a) => String -> PSLens a a
inspectL st =
  PSLens
    (\x -> trace ("fwd" <> ss <> ": " <> show x) (pure x))
    (\s v -> trace ("bwd" <> ss <> ": " <> show s <> " | " <> show v) (pure v))
  where
    ss = if null st then "" else "[" ++ st ++ "]"

-- Lenses for M a (a poset with the fresh least element)

pairM :: PSLens (M a, M b) (M (a, b))
pairM = PSLens g p
  where
    g ~(a, b) = pure $ liftA2 (,) a b
    p _ (Some ~(a, b)) = pure (Some a, Some b)
    p _ None = pure (None, None)

introM :: (Templatable a) => PSLens a (M a)
introM = PSLens (pure . Some) $ \s v -> case v of
  Some a -> pure a
  None -> pure (template s)

-- This is not a "join" for a monad. In particular, joinM >>> introM is not idL.
joinM :: (CheckLeast a) => PSLens (M a) a
joinM = PSLens g p
  where
    g (Some a) = pure a
    g None = pure least

    p _ v
      | isLeast v = pure None
      | otherwise = pure $ Some v

letM' :: (CheckLeast a) => PSLens a b -> PSLens (M a) b
letM' l = joinM >>> l

-- A specialized version of sndL (recall that () is an instance of LowerBounded)
-- Also, sndL can be defined via deleteUnit as:
--
-- prop> sndL == (eraseUnspecL *** id) >>> deleteUnit

deleteUnit :: PSLens ((), a) a
deleteUnit = PSLens (pure . snd) (const $ \a -> pure ((), a))

introUnit :: PSLens a ((), a)
introUnit = PSLens (\a -> pure ((), a)) (const $ pure . snd)

snapshot :: (Discrete c) => (c -> PSLens a b) -> PSLens (a, c) (b, c)
snapshot k = PSLens g p
  where
    g ~(a, c) = do
      b <- get (k c) a
      pure (b, c)
    p ~(a, _) ~(b, c) = do
      a' <- put (k c) a b
      pure (a', c)

newtype OrderInd a b = OrderInd {runOrderInd :: a -> b}

snapshotO :: OrderInd c (PSLens a b) -> PSLens (a, c) (b, c)
snapshotO k = PSLens g p
  where
    g ~(a, c) = do
      b <- get (runOrderInd k c) a
      pure (b, c)
    p ~(a, _) ~(b, c) = do
      a' <- put (runOrderInd k c) a b
      pure (a', c)

depLens :: (Discrete c) => PSLens a c -> (c -> PSLens d b) -> PSLens (a, d) (c, b)
depLens l k = first l >>> swapL >>> snapshot k >>> swapL

newtype Monotone a b = EnsureMonotone {applyMonotone :: a -> b}

monoFromDisc :: (Discrete a, Discrete b) => (a -> b) -> Monotone a b
monoFromDisc = EnsureMonotone

unTag :: Monotone a Bool -> PSLens (Either a a) a
unTag phi = PSLens g p
  where
    g (Left a)
      | applyMonotone phi a = pure a
      | otherwise = err "Invariant check failed (got False, expected True)"
    g (Right a)
      | applyMonotone phi a = err "Invariant check failed (got True, expected False)"
      | otherwise = pure a
    p _ a
      | applyMonotone phi a = pure (Left a)
      | otherwise = pure (Right a)

unTagS :: PSLens (Either a a) a
unTagS = PSLens g p
  where
    g = pure . either id id

    p (Left _) = pure . Left
    p (Right _) = pure . Right

sumM :: PSLens (Either (M a) (M b)) (M (Either a b))
sumM = PSLens g p
  where
    g (Left None) = pure $ None
    g (Left (Some a)) = pure $ Some (Left a)
    g (Right None) = pure $ None
    g (Right (Some b)) = pure $ Some (Right b)

    p _ (Some (Left a)) = pure $ Left $ Some a
    p _ (Some (Right b)) = pure $ Right $ Some b
    p s None = case s of
      Left _ -> pure $ Left None
      Right _ -> pure $ Right None

mapSumL ::
  PSLens a c
  -> PSLens b d
  -> (b -> c -> Err a)
  -> (a -> d -> Err b)
  -> PSLens (Either a b) (Either c d)
mapSumL l1 l2 r1 r2 = PSLens g p
  where
    g (Left a) = Left <$> get l1 a
    g (Right b) = Right <$> get l2 b

    p (Left a) (Left c) = Left <$> put l1 a c
    p (Left a) (Right d) = do
      b <- r2 a d
      Right <$> put l2 b d
    p (Right b) (Left c) = do
      a <- r1 b c
      Left <$> put l1 a c
    p (Right b) (Right d) = Right <$> put l2 b d

scond :: PSLens a c -> PSLens b c -> PSLens (Either a b) c
scond l1 l2 = mapSumL l1 l2 r r >>> unTagS
  where
    r _ _ = err "scond: cannot switch branches."

cond :: PSLens a d -> (b -> d -> Err a) -> PSLens b d -> (a -> d -> Err b) -> Monotone d Bool -> PSLens (Either a b) d
cond l1 r1 l2 r2 p = mapSumL l1 l2 r1 r2 >>> unTag p
