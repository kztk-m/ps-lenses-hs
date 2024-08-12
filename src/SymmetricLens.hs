{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}

module SymmetricLens where

import Control.Category
import Data.Dynamic
import Data.Maybe (fromJust)
import Data.Typeable (Typeable)
import Domain
import Err
import MALens
import MALensTH
import Prelude hiding (id, (.))

{- |
A pair of lenses to mimic symmetric lens. The following additional
properties need to be satisfied for this to behave as symmetric lens.

For 'MkPair left right':
spec> put left s (just a) == just s' ===> get right s' /= nothing
spec> get right s (just b) == just s' ===> get left s' /= nothing
spec> get left (ma , mb , c) == just a ===> ma == just a
spec> get right (ma , mb , c) == just b ===> mb == just b
-}
data LensPair a b where
  MkPair ::
    forall c a b.
    (Typeable c, Eq c) =>
    c
    -> MALens ((M a, M b), c) (M a)
    -> MALens ((M a, M b), c) (M b)
    -> LensPair a b

data SymmetricLensComp c a b
  = MkComp
  { initComplement :: c
  , putr :: (a, c) -> Err (b, c)
  , putl :: (b, c) -> Err (a, c)
  }

data SymmetricLens a b = forall c. (Typeable c, Eq c) => ExC (SymmetricLensComp c a b)

idLensPair :: (Discrete a, Eq a) => LensPair a a
idLensPair = MkPair () l l
  where
    l :: (Discrete a, Eq a) => MALens ((M a, M a), ()) (M a)
    l = first (mergeW witGlbD) >>> fstL

composeLensPair :: forall a1 a2 a3. (Typeable a2, Eq a2, Discrete a2) => LensPair a1 a2 -> LensPair a2 a3 -> LensPair a1 a3
composeLensPair (MkPair c0_ left12_ right12_) (MkPair d0_ left23_ right23_) = mkPair c0_ d0_ left12_ right12_ left23_ right23_
  where
    mkPair ::
      forall c d.
      (Typeable c, Typeable d, Eq c, Eq d) =>
      c
      -> d
      -> MALens ((M a1, M a2), c) (M a1)
      -> MALens ((M a1, M a2), c) (M a2)
      -> MALens ((M a2, M a3), d) (M a2)
      -> MALens ((M a2, M a3), d) (M a3)
      -> LensPair a1 a3
    mkPair c0 d0 left12 right12 left23 right23 = MkPair @(M a2, (c, d)) (least, (c0, d0)) left right
      where
        rearr ::
          MALens
            ((M a1, M a3), (M a2, (c, d)))
            ( ((M a1, M a2), c)
            , ((M a2, M a3), d)
            )
        rearr =
          second (first $ dupW (witLubM witLubD))
            >>> $(arrP [|\((a1, a3), ((a2, a2'), (c, d))) -> (((a1, a2), c), ((a2', a3), d))|])

        left :: MALens ((M a1, M a3), (M a2, (c, d))) (M a1)
        left =
          rearr
            >>> second left23
            >>> $(arrP [|\(((a1, a2), c), a2') -> ((a1, (a2, a2')), c)|])
            >>> first (second $ mergeW witGlbD)
            >>> left12

        right :: MALens ((M a1, M a3), (M a2, (c, d))) (M a3)
        right =
          rearr
            >>> first right12
            >>> $(arrP [|\(a2, ((a2', a3), d)) -> (((a2, a2'), a3), d)|])
            >>> first (first $ mergeW witGlbD)
            >>> right23

flip :: LensPair a b -> LensPair b a
flip (MkPair c0 left right) = MkPair c0 (first swapL >>> right) (first swapL >>> left)

fromSymmetric :: (Eq a, Eq b) => SymmetricLens a b -> LensPair a b
fromSymmetric (ExC (MkComp c0 putr_ putl_)) =
  MkPair c0 (mkLens putr_ putl_) (first swapL >>> mkLens putl_ putr_)
  where
    mkLens pr pl = MALens g p
      where
        g ((Some a, Some b), c)
          | Ok (a', c') <- pl (b, c)
          , a == a'
          , c == c' =
              Some a
        g _ = NoneWith ["original source is not in a consistent state"]
        p (_, c) None = pure ((None, None), c)
        p (_, c) (Some a) = do
          (b, c') <- pr (a, c)
          pure ((Some a, Some b), c')

-- This is not lawful as it allows the complement to be a smaller value. This
-- will not be a problem if any primitives uses concrete (non M) values as
-- complement.
toSymmetric :: LensPair a b -> SymmetricLens a b
toSymmetric (MkPair c0 left right) = ExC $ MkComp c0 putr_ putl_
  where
    unSome (Some a) = a
    unSome (NoneWith s) = error $ "Impossible happend: " ++ show s

    putr_ (a', c) = do
      s' <- put left (least, c) (Some a')
      pure (unSome $ get right s', snd s')

    putl_ (b', c) = do
      s' <- put right (least, c) (Some b')
      pure (unSome $ get left s', snd s')

toSymmetricD :: LensPair a b -> (Dynamic, (a, Dynamic) -> Err (b, Dynamic), (b, Dynamic) -> Err (a, Dynamic))
toSymmetricD lp = case toSymmetric lp of
  ExC (MkComp c0 pr pl) ->
    ( toDyn c0
    , \(ma, d) -> do (mb, c') <- pr (ma, fromJust $ fromDynamic d); pure (mb, toDyn c')
    , \(mb, d) -> do (ma, c') <- pl (mb, fromJust $ fromDynamic d); pure (ma, toDyn c')
    )

term :: (Eq a, Discrete a, Typeable a) => a -> LensPair a ()
term a0 = MkPair a0 left right
  where
    -- careful definitions to fulfill the laws of LensPair
    left :: (Eq a, Discrete a) => MALens ((M a, M ()), a) (M a)
    left =
      $(arrP [|\((ma, mt), a) -> ((ma, a), mt)|])
        >>> first (second introMd >>> mergeW witGlbD)
        >>> pairM
        >>> swapM
        >>> deleteUnitM

    right :: (Eq a, Discrete a) => MALens ((M a, M ()), a) (M ())
    right =
      $(arrP [|\((ma, mt), a) -> ((ma, a), mt)|])
        -- check whether the `c` is in the valid state
        >>> first (snapshot assertEqL)
        >>> $(arrP [|\((ma, a), mt) -> ((ma, mt), a)|])
        -- distribute (Some ()) in put
        >>> first (pairM >>> deleteUnitM)
        >>> second introMd
        >>> fstL

-- >>> (c0, pr, pl) = toSymmetricD (term (1 :: Int))
-- >>> fromDynamic c0 :: Maybe Int
-- Just 1
-- >>> let Ok (mb , c) = pr (2, c0)
-- >>> mb
-- >>> fromDyn c undefined :: Int
-- ()
-- 2
-- >>> let Ok (ma , c') = pl ((), c)
-- >>> ma
-- >>> fromDyn c' undefined :: Int
-- 2
-- 2

-- >>> (c0 , pr, pl) = toSymmetricD (term (1 :: Int) `composeLensPair` SymmetricLens.flip (term "X"))
-- >>> fromDyn c0 undefined :: (M (), (Int , String))
-- (NoneWith [],(1,"X"))
-- >>> let Ok (b , c) = pl ("Hello", c0)
-- >>> b
-- >>> fromDyn c undefined :: (M (), (Int , String))
-- 1
-- (Some (),(1,"Hello"))
-- >>> let Ok (a , c') = pr (2333, c)
-- >>> a
-- >>> fromDyn c' undefined :: (M (), (Int , String))
-- "Hello"
-- (Some (),(2333,"Hello"))

-- idLensPair :: forall a. (Lub a, Glb' a, Typeable a) => LensPair a a
-- idLensPair = MkPair l1 l2
--   where
--     l1, l2 :: MALens ((M a, M a), ()) (M a)
--     l1 = $(arrP [|\((a, b), ()) -> (a, b)|]) >>> fstL
--     l2 = $(arrP [|\((a, b), ()) -> (a, b)|]) >>> sndL

-- -- inject :: forall a b. (Glb' a, Glb' b, Typeable a, Typeable b, Lub a, Lub b) => LensPair a (Either a b)
-- -- inject = fromSymmetric $ ExC $ MkComp pr pl
-- --   where
-- --     pr (None, c) = pure (None, c)
-- --     pr (Some x, (_, None)) = pure (Some (Left x), (Some x, Some Nothing))
-- --     pr (Some x, (_, Some Nothing)) = pure (Some (Left x), (Some x, Some Nothing))
-- --     pr (Some x, (_, Some (Just y))) = pure (Some (Right y), (Some x, Some (Just y)))

-- --     pl (None, c) = pure (None, c)
-- --     pl (Some (Left x), _) = pure (Some x, (Some x, Some Nothing))
-- --     pl (Some (Right y), (Some x, _)) = pure (Some x, (Some x, Some (Just y)))
-- --     pl (Some (Right _), (None, _)) = err "NNN"

-- -- inject :: forall a b. (Glb' a, Glb' b, Typeable a, Typeable b, Lub a, Lub b) => LensPair a (Either a b)
-- -- inject = MkPair @(M a, M b) l1 l2
-- --   where
-- --     l1 :: MALens ((M a, M (Either a b)), (M a, M b)) (M a)
-- --     l1 = _
-- --     l2 :: MALens ((M a, M (Either a b)), (M a, M b)) (M (Either a b))
-- --     l2 = _

-- composeLensPair :: forall a1 a2 a3. LensPair a1 a2 -> LensPair a2 a3 -> LensPair a1 a3
-- composeLensPair (MkPair l1_ l2_) (MkPair l1'_ l2'_) =
--   let (ll1, ll2) = conv l1_ l2_ l1'_ l2'_
--   in  MkPair ll1 ll2
--   where
--     conv ::
--       MALens ((M a1, M a2), c) (M a1)
--       -> MALens ((M a1, M a2), c) (M a2)
--       -> MALens ((M a2, M a3), d) (M a2)
--       -> MALens ((M a2, M a3), d) (M a3)
--       -> ( MALens ((M a1, M a3), ((M a2, M a2), (c, d))) (M a1)
--          , MALens ((M a1, M a3), ((M a2, M a2), (c, d))) (M a3)
--          )
--     conv l1 l2 l1' l2' = (ll1, ll2)
--       where
--         split = $(arrP [|\((a1, a3), ((a2, a2'), (c, d))) -> (((a1, a2), c), ((a2', a3), d))|])
--         ll1 =
--           split
--             >>> second l1'
--             >>> $(arrP [|\(((a1, a2), c), a2') -> ((a1, (a2, a2')), c)|])
--             >>> first (second merge)
--             >>> l1
--         ll2 =
--           split
--             >>> first l2
--             >>> $(arrP [|\(a2, ((a2', a3), d)) -> (((a2, a2'), a3), d)|])
--             >>> first (first merge)
--             >>> l2'

-- toSymmetric :: LensPair a b -> SymmetricLens (M a) (M b)
-- toSymmetric (MkPair l1 l2) = ExC $ MkComp putr_ putl_
--   where
--     l = dup >>> (l1 *** l2)
--     putr_ (a', s) = do
--       s' <- put l s (a', None)
--       pure (snd $ get l s', s')

--     putl_ (b', s) = do
--       s' <- put l s (None, b')
--       pure (fst $ get l s', s')

-- fromSymmetric :: (Glb' a, Glb' b, Typeable a, Typeable b, Lub a, Lub b) => SymmetricLens (M a) (M b) -> LensPair a b
-- fromSymmetric (ExC (MkComp pr pl)) = MkPair l1 l2
--   where
--     l1 = MALens (\((a, _), _) -> a) (\((_, _), c) a' -> do (b', c') <- pr (a', c); pure ((a', b'), c'))
--     l2 = MALens (\((_, b), _) -> b) (\((_, _), c) b' -> do (a', c') <- pl (b', c); pure ((a', b'), c'))
