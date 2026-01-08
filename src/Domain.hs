{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# OPTIONS_GHC -Wno-redundant-constraints #-}

module Domain (
  LowerBounded (..),
  CheckLeast (..),
  Discrete,
  Lub (..),
  Glb (..),
  Glb' (..),
  M (..),
  POrd (..),
  CheckIdentical (..),
  pattern None,
  Templatable (..),

  -- * Explicit Witness
  WitGlb,
  glbWith,
  WitGlb',
  glb'With,
  WitLub,
  lubWith,
  witGlb,
  witGlb',
  witLub,
  witLubD,
  witLubM,
  witGlbD,
  witGlb'D,
) where

import qualified Data.Map as M

import Err

import Data.Coerce (coerce)
import qualified GHC.Generics as Gen

-- | 'POrd' is used when want to refer to specifiedness ordering in computation.
-- We do not reuse the existing Ord type class, as they are often conflicting.
-- For example, we have 1 <= 2 but they are both incomparable proper states in
-- the usual sense.
class (Eq a) => POrd a where
  (<=%) :: a -> a -> Bool
  default (<=%) :: (Gen.Generic a, GPOrd (Gen.Rep a)) => a -> a -> Bool
  x <=% y = genLE (Gen.from x) (Gen.from y)

-- | Similarly to 'POrd', but 'CheckIdentical' provides 'identicalAt' to check
-- the I relation in the paper.
class (Eq a) => CheckIdentical a where
  -- prop> identicalAt a b ===> a <=% b
  identicalAt :: a -> a -> Bool
  default identicalAt :: (Gen.Generic a, GCheckIdentical (Gen.Rep a)) => a -> a -> Bool
  identicalAt x y = gIdenticalAt (Gen.from x) (Gen.from y)

-- | A class prepared for generic |POrd| instances.
class GPOrd f where
  genLE :: f a -> f a -> Bool

instance GPOrd Gen.V1 where
  genLE x y =
    case x of {} `seq` case y of {}

instance GPOrd Gen.U1 where
  genLE _ _ = True

instance (GPOrd a, GPOrd b) => GPOrd (a Gen.:*: b) where
  genLE (x Gen.:*: y) (x' Gen.:*: y') = genLE x x' && genLE y y'

instance (GPOrd a, GPOrd b) => GPOrd (a Gen.:+: b) where
  genLE (Gen.L1 x) (Gen.L1 x') = genLE x x'
  genLE (Gen.R1 x) (Gen.R1 x') = genLE x x'
  genLE _ _ = False

instance (GPOrd f) => GPOrd (Gen.M1 i t f) where
  genLE (Gen.M1 c) (Gen.M1 c') = genLE c c'
instance (POrd c) => GPOrd (Gen.K1 i c) where
  genLE (Gen.K1 c) (Gen.K1 c') = c <=% c'

instance POrd ()
instance (POrd a, POrd b) => POrd (a, b)
instance (POrd a, POrd b, POrd c) => POrd (a, b, c)
instance (POrd a, POrd b) => POrd (Either a b)

-- | A class prepared for generic 'CheckIdentical' instances.
class GCheckIdentical f where
  gIdenticalAt :: f a -> f a -> Bool

instance GCheckIdentical Gen.V1 where
  gIdenticalAt x y =
    case x of {} `seq` case y of {}

instance GCheckIdentical Gen.U1 where
  gIdenticalAt _ _ = True

instance (GCheckIdentical a, GCheckIdentical b) => GCheckIdentical (a Gen.:*: b) where
  gIdenticalAt (x Gen.:*: y) (x' Gen.:*: y') = gIdenticalAt x x' && gIdenticalAt y y'

instance (GCheckIdentical a, GCheckIdentical b) => GCheckIdentical (a Gen.:+: b) where
  gIdenticalAt (Gen.L1 x) (Gen.L1 x') = gIdenticalAt x x'
  gIdenticalAt (Gen.R1 x) (Gen.R1 x') = gIdenticalAt x x'
  gIdenticalAt _ _ = False

instance (GCheckIdentical f) => GCheckIdentical (Gen.M1 i t f) where
  gIdenticalAt (Gen.M1 c) (Gen.M1 c') = gIdenticalAt c c'
instance (CheckIdentical c) => GCheckIdentical (Gen.K1 i c) where
  gIdenticalAt (Gen.K1 c) (Gen.K1 c') = identicalAt c c'

instance CheckIdentical ()
instance (CheckIdentical a, CheckIdentical b) => CheckIdentical (a, b)
instance (CheckIdentical a, CheckIdentical b, CheckIdentical c) => CheckIdentical (a, b, c)
instance (CheckIdentical a, CheckIdentical b) => CheckIdentical (Either a b)

instance (Eq a, Discrete a) => CheckIdentical (EqDisc a) where
  identicalAt (EqDisc a) (EqDisc b) = a == b

deriving via EqDisc Int instance CheckIdentical Int
deriving via EqDisc Double instance CheckIdentical Double
deriving via EqDisc Bool instance CheckIdentical Bool
deriving via EqDisc Char instance CheckIdentical Char

-- | Lowerbounded i-posets (ordering is implicit in Haskell implementation)
class LowerBounded a where
  least :: a
  least = leastWith []
  leastWith :: [String] -> a
  leastWith _ = least

-- | A sub class of |LowerBound| with a method to check if a given element is
-- the least element or not.
class (LowerBounded a) => CheckLeast a where
  isLeast :: a -> Bool

-- | A type class for generic instances of 'Lub'
class GLub f where
  glub :: f a -> f a -> Err (f a)

instance GLub Gen.V1 where
  glub x y =
    case x of {} `seq` case y of {}

instance GLub Gen.U1 where
  glub _ _ = pure Gen.U1

instance (GLub a, GLub b) => GLub (a Gen.:*: b) where
  glub (x Gen.:*: y) (x' Gen.:*: y') =
    liftA2 (Gen.:*:) (glub x x') (glub y y')

instance (GLub a, GLub b) => GLub (a Gen.:+: b) where
  glub (Gen.L1 x) (Gen.L1 x') = Gen.L1 <$> glub x x'
  glub (Gen.R1 x) (Gen.R1 x') = Gen.R1 <$> glub x x'
  glub _ _ = err "lub: expects elements with the same tag"

instance (GLub f) => GLub (Gen.M1 i t f) where
  glub (Gen.M1 c) (Gen.M1 c') = Gen.M1 <$> glub c c'
instance (Lub c) => GLub (Gen.K1 i c) where
  glub (Gen.K1 c) (Gen.K1 c') = Gen.K1 <$> lub c c'

-- | Provides 'lub', which should implement the join operation soundly.
-- This class corresponds to "Duplicable" in the paper.
class Lub a where
  lub :: a -> a -> Err a
  default lub :: (Gen.Generic a, GLub (Gen.Rep a)) => a -> a -> Err a
  lub x y = Gen.to <$> glub (Gen.from x) (Gen.from y)

instance Lub ()
instance (Lub a, Lub b) => Lub (a, b)
instance (Lub a, Lub b, Lub c) => Lub (a, b, c)
instance (Lub a, Lub b, Lub c, Lub d) => Lub (a, b, c, d)
instance (Lub a, Lub b) => Lub (Either a b)
instance (Lub a) => Lub [a]
instance (Lub a) => Lub (Maybe a)

instance (Lub a) => Lub (M a) where
  lub None m = pure m
  lub m None = pure m
  lub (Some a) (Some b) = Some <$> lub a b

-- | A class provides 'glb', a dual of 'lub'.
class Glb a where
  -- Unlike 'lub', we require glb as it is assumed to be used in get
  glb :: a -> a -> a

-- | A class for generic instances of 'Glb''
class GGlb' f where
  gglb' :: f a -> f a -> Err (f a)

instance GGlb' Gen.V1 where
  gglb' x y =
    case x of {} `seq` case y of {}

instance GGlb' Gen.U1 where
  gglb' _ _ = pure Gen.U1

instance (GGlb' a, GGlb' b) => GGlb' (a Gen.:*: b) where
  gglb' (x Gen.:*: y) (x' Gen.:*: y') =
    liftA2 (Gen.:*:) (gglb' x x') (gglb' y y')

instance (GGlb' a, GGlb' b) => GGlb' (a Gen.:+: b) where
  gglb' (Gen.L1 x) (Gen.L1 x') = Gen.L1 <$> gglb' x x'
  gglb' (Gen.R1 x) (Gen.R1 x') = Gen.R1 <$> gglb' x x'
  gglb' _ _ = err "lub: expects elements with the same tag"

instance (GGlb' f) => GGlb' (Gen.M1 i t f) where
  gglb' (Gen.M1 c) (Gen.M1 c') = Gen.M1 <$> gglb' c c'
instance (Glb' c) => GGlb' (Gen.K1 i c) where
  gglb' (Gen.K1 c) (Gen.K1 c') = Gen.K1 <$> glb' c c'

-- | A variant of 'Glb' that provides 'glb''. Unlike 'glb' in 'Glb', 'glb'' can
-- be (observably) partial.
class Glb' a where
  glb' :: a -> a -> Err a
  default glb' :: (Gen.Generic a, GGlb' (Gen.Rep a)) => a -> a -> Err a
  glb' x y = Gen.to <$> gglb' (Gen.from x) (Gen.from y)

instance Glb () where
  glb = const $ const ()
instance (Glb a, Glb b) => Glb (a, b) where
  glb (a, b) (a', b') = (glb a a', glb b b')

instance (Glb' a) => Glb (M a) where
  glb (NoneWith s) _ = NoneWith s
  glb _ (NoneWith s) = NoneWith s
  glb (Some a) (Some a') =
    case glb' a a' of
      Ok r -> Some r
      Err s -> NoneWith s

instance Glb' ()
instance (Glb' a, Glb' b) => Glb' (a, b)
instance (Glb' a, Glb' b, Glb' c) => Glb' (a, b, c)
instance (Glb' a, Glb' b, Glb' c, Glb' d) => Glb' (a, b, c, d)
instance (Glb' a, Glb' b) => Glb' (Either a b)
instance (Glb' a) => Glb' [a]
instance (Glb' a) => Glb' (Maybe a)

-- | A newtype wrapper to be used with @DerivingVia@.
newtype EqDisc a = EqDisc a deriving newtype (Eq)

instance (Discrete a, Eq a) => Lub (EqDisc a) where
  lub = coerce @(a -> a -> Err a) @(EqDisc a -> EqDisc a -> Err (EqDisc a)) (lubWith witLubD)

deriving via EqDisc Int instance Lub Int
deriving via EqDisc Double instance Lub Double
deriving via EqDisc Bool instance Lub Bool
deriving via EqDisc Char instance Lub Char

instance (Discrete a, Eq a) => Glb' (EqDisc a) where
  glb' = coerce @(a -> a -> Err a) @(EqDisc a -> EqDisc a -> Err (EqDisc a)) (glb'With witGlb'D)

deriving via EqDisc Int instance Glb' Int
deriving via EqDisc Double instance Glb' Double
deriving via EqDisc Bool instance Glb' Bool
deriving via EqDisc Char instance Glb' Char

instance (Discrete a, Eq a) => POrd (EqDisc a) where
  a <=% b = a == b

deriving via EqDisc Int instance POrd Int
deriving via EqDisc Double instance POrd Double
deriving via EqDisc Bool instance POrd Bool
deriving via EqDisc Char instance POrd Char

-- A class to ensure @a@ is discrete. The class has no method intentionally.
class Discrete a

instance Discrete ()
instance Discrete Int
instance Discrete Double
instance Discrete Bool
instance Discrete Char
instance (Discrete a, Discrete b) => Discrete (Either a b)
instance (Discrete a, Discrete b) => Discrete (a, b)
instance (Discrete a, Discrete b, Discrete c) => Discrete (a, b, c)
instance (Discrete a, Discrete b, Discrete c, Discrete d) => Discrete (a, b, c, d)
instance (Discrete a) => Discrete [a]
instance (Discrete a) => Discrete (Maybe a)
instance (Discrete k, Discrete v) => Discrete (M.Map k v)

-- | Another name of Maybe, except we have @None <=% Some _@.
data M a = NoneWith [String] | Some a deriving stock (Show, Eq, Functor)

pattern None :: M a
pattern None <- NoneWith _
  where
    None = NoneWith []

{-# COMPLETE None, Some #-}

instance Applicative M where
  pure = Some
  Some f <*> Some a = Some (f a)
  Some _ <*> NoneWith s = NoneWith s
  NoneWith s <*> Some _ = NoneWith s
  NoneWith s <*> NoneWith s' = NoneWith (s <> s')

instance LowerBounded () where
  least = ()

instance CheckLeast () where
  isLeast _ = True

instance LowerBounded (M a) where
  least = None
  leastWith = NoneWith
instance CheckLeast (M a) where
  isLeast None = True
  isLeast _ = False

instance (LowerBounded a, LowerBounded b) => LowerBounded (a, b) where
  least = (least, least)
  leastWith s = (leastWith s, leastWith s)

instance (LowerBounded a, LowerBounded b, LowerBounded c) => LowerBounded (a, b, c) where
  least = (least, least, least)
  leastWith s = (leastWith s, leastWith s, leastWith s)

instance (CheckLeast a, CheckLeast b) => CheckLeast (a, b) where
  isLeast (a, b) = isLeast a && isLeast b

instance (CheckLeast a, CheckLeast b, CheckLeast c) => CheckLeast (a, b, c) where
  isLeast (a, b, c) = isLeast a && isLeast b && isLeast c

-- |
-- Explicit witness types, sometimes suitable for expresson
-- subclass relations explicitly that Haskell does not handle well.
newtype WitGlb a = WitGlb {glbWith :: a -> a -> a}

newtype WitGlb' a = WitGlb' {glb'With :: a -> a -> Err a}

newtype WitLub a = WitLub {lubWith :: a -> a -> Err a}

witGlb :: (Glb a) => WitGlb a
witGlb = WitGlb glb

witLub :: (Lub a) => WitLub a
witLub = WitLub lub

witGlb' :: (Glb' a) => WitGlb' a
witGlb' = WitGlb' glb'

witGlbD :: (Eq a, Discrete a) => WitGlb (M a)
witGlbD = WitGlb f
  where
    f (Some a) (Some b) | a == b = Some a
    f _ _ = None

witLubD :: (Eq a, Discrete a) => WitLub a
witLubD = WitLub f
  where
    f :: (Eq a, Discrete a) => a -> a -> Err a
    f a b
      | a == b = pure a
      | otherwise = err "no lub for different elements in a disrete domain."

witLubM :: WitLub a -> WitLub (M a)
witLubM w = WitLub f
  where
    f None m = pure m
    f (Some a) None = pure $ Some a
    f (Some a) (Some b) = Some <$> lubWith w a b

witGlb'D :: (Eq a, Discrete a) => WitGlb' a
witGlb'D = WitGlb' f
  where
    f a b
      | a == b = pure a
      | otherwise = err "no glb for different elements in a disrete domain."

-- | A typeclass for generic |Temptable| instances.
class GenTemplatable f where
  gtemplate :: f a -> f a

instance GenTemplatable Gen.V1 where
  gtemplate x = case x of {}

instance GenTemplatable Gen.U1 where
  gtemplate Gen.U1 = Gen.U1

instance (GenTemplatable f, GenTemplatable g) => GenTemplatable (f Gen.:*: g) where
  gtemplate (a Gen.:*: b) = (gtemplate a Gen.:*: gtemplate b)

instance (GenTemplatable f, GenTemplatable g) => GenTemplatable (f Gen.:+: g) where
  gtemplate (Gen.L1 a) = Gen.L1 (gtemplate a)
  gtemplate (Gen.R1 b) = Gen.R1 (gtemplate b)

instance (Templatable c) => GenTemplatable (Gen.K1 i c) where
  gtemplate (Gen.K1 c) = Gen.K1 $ template c

instance (GenTemplatable f) => GenTemplatable (Gen.M1 i t f) where
  gtemplate (Gen.M1 x) = Gen.M1 $ gtemplate x

-- | 'Templable a' is a weaker version of 'LowerBounded', where we can pick the
-- relative smallest element. (Not in the part of our ESOP 2026 paper)
class Templatable a where
  -- | @template a@ returns the smallest (in terms of specifiedness) element that are comparable with @a@.
  --
  -- spec> template x <=% y ==> template x <=% template y
  -- spec> x <=% y ==> template y <=% x
  -- spec> identicalAt (template x) x
  template :: a -> a
  default template :: (Gen.Generic a, GenTemplatable (Gen.Rep a)) => a -> a
  template = Gen.to . gtemplate . Gen.from

instance Templatable Int where template = id
instance Templatable Double where template = id
instance Templatable Char where template = id
instance Templatable Bool where template = id
instance Templatable () where template = id
instance (Templatable a) => Templatable (Maybe a) where template = fmap template
instance (Templatable a) => Templatable [a] where template = fmap template

instance (Templatable a, Templatable b) => Templatable (a, b)
instance (Templatable a, Templatable b, Templatable c) => Templatable (a, b, c)
instance (Templatable a, Templatable b, Templatable c, Templatable d) => Templatable (a, b, c, d)
instance (Templatable a, Templatable b) => Templatable (Either a b)

instance (Discrete k, Templatable a) => Templatable (M.Map k a) where
  template = fmap template

instance Templatable (M a) where
  template _ = least
