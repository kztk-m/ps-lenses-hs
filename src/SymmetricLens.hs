{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}

module SymmetricLens where

import Control.Category
import Data.Typeable (Typeable)
import Domain
import Err
import MALens
import MALensTH
import Prelude hiding (id, (.))

data LensPair a b where
  MkPair ::
    forall c a b.
    (Lub a, Lub b, Glb' a, Glb' b, Typeable a, Typeable b, Lub c, LowerBounded c, Typeable c) =>
    MALens ((M a, M b), c) (M a)
    -> MALens ((M a, M b), c) (M b)
    -> LensPair a b

data SymmetricLensComp c a b
  = MkComp
  { putr :: (a, c) -> Err (b, c)
  , putl :: (b, c) -> Err (a, c)
  }

data SymmetricLens a b = forall c. (Typeable c, Lub c, LowerBounded c) => ExC (SymmetricLensComp c a b)

idLensPair :: forall a. (Lub a, Glb' a, Typeable a) => LensPair a a
idLensPair = MkPair l1 l2
  where
    l1, l2 :: MALens ((M a, M a), ()) (M a)
    l1 = $(arrP [|\((a, b), ()) -> (a, b)|]) >>> fstL
    l2 = $(arrP [|\((a, b), ()) -> (a, b)|]) >>> sndL

-- inject :: forall a b. (Glb' a, Glb' b, Typeable a, Typeable b, Lub a, Lub b) => LensPair a (Either a b)
-- inject = fromSymmetric $ ExC $ MkComp pr pl
--   where
--     pr (None, c) = pure (None, c)
--     pr (Some x, (_, None)) = pure (Some (Left x), (Some x, Some Nothing))
--     pr (Some x, (_, Some Nothing)) = pure (Some (Left x), (Some x, Some Nothing))
--     pr (Some x, (_, Some (Just y))) = pure (Some (Right y), (Some x, Some (Just y)))

--     pl (None, c) = pure (None, c)
--     pl (Some (Left x), _) = pure (Some x, (Some x, Some Nothing))
--     pl (Some (Right y), (Some x, _)) = pure (Some x, (Some x, Some (Just y)))
--     pl (Some (Right _), (None, _)) = err "NNN"

-- inject :: forall a b. (Glb' a, Glb' b, Typeable a, Typeable b, Lub a, Lub b) => LensPair a (Either a b)
-- inject = MkPair @(M a, M b) l1 l2
--   where
--     l1 :: MALens ((M a, M (Either a b)), (M a, M b)) (M a)
--     l1 = _
--     l2 :: MALens ((M a, M (Either a b)), (M a, M b)) (M (Either a b))
--     l2 = _

composeLensPair :: forall a1 a2 a3. LensPair a1 a2 -> LensPair a2 a3 -> LensPair a1 a3
composeLensPair (MkPair l1_ l2_) (MkPair l1'_ l2'_) =
  let (ll1, ll2) = conv l1_ l2_ l1'_ l2'_
  in  MkPair ll1 ll2
  where
    conv ::
      MALens ((M a1, M a2), c) (M a1)
      -> MALens ((M a1, M a2), c) (M a2)
      -> MALens ((M a2, M a3), d) (M a2)
      -> MALens ((M a2, M a3), d) (M a3)
      -> ( MALens ((M a1, M a3), ((M a2, M a2), (c, d))) (M a1)
         , MALens ((M a1, M a3), ((M a2, M a2), (c, d))) (M a3)
         )
    conv l1 l2 l1' l2' = (ll1, ll2)
      where
        split = $(arrP [|\((a1, a3), ((a2, a2'), (c, d))) -> (((a1, a2), c), ((a2', a3), d))|])
        ll1 =
          split
            >>> second l1'
            >>> $(arrP [|\(((a1, a2), c), a2') -> ((a1, (a2, a2')), c)|])
            >>> first (second merge)
            >>> l1
        ll2 =
          split
            >>> first l2
            >>> $(arrP [|\(a2, ((a2', a3), d)) -> (((a2, a2'), a3), d)|])
            >>> first (first merge)
            >>> l2'

toSymmetric :: LensPair a b -> SymmetricLens (M a) (M b)
toSymmetric (MkPair l1 l2) = ExC $ MkComp putr_ putl_
  where
    l = dup >>> (l1 *** l2)
    putr_ (a', s) = do
      s' <- put l s (a', None)
      pure (snd $ get l s', s')

    putl_ (b', s) = do
      s' <- put l s (None, b')
      pure (fst $ get l s', s')

fromSymmetric :: (Glb' a, Glb' b, Typeable a, Typeable b, Lub a, Lub b) => SymmetricLens (M a) (M b) -> LensPair a b
fromSymmetric (ExC (MkComp pr pl)) = MkPair l1 l2
  where
    l1 = MALens (\((a, _), _) -> a) (\((_, _), c) a' -> do (b', c') <- pr (a', c); pure ((a', b'), c'))
    l2 = MALens (\((_, b), _) -> b) (\((_, _), c) b' -> do (a', c') <- pl (b', c); pure ((a', b'), c'))
