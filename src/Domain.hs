{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE StandaloneDeriving #-}
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
  pattern None,
) where

import qualified Data.Map as M

import Err

import qualified GHC.Generics as Gen

class LowerBounded a where
  least :: a
  least = leastWith []
  leastWith :: [String] -> a
  leastWith _ = least

class (LowerBounded a) => CheckLeast a where
  isLeast :: a -> Bool

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

class Glb a where
  -- Unlike 'lub', we require glb as it is assumed to be used in get
  glb :: a -> a -> a

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

newtype EqDisc a = EqDisc a deriving newtype (Eq)

instance (Discrete a, Eq a) => Lub (EqDisc a) where
  lub a b = if a == b then pure a else err "lub: no lub for different elements in a disrete domain."
deriving via EqDisc Int instance Lub Int
deriving via EqDisc Double instance Lub Double
deriving via EqDisc Bool instance Lub Bool
deriving via EqDisc Char instance Lub Char

instance (Discrete a, Eq a) => Glb' (EqDisc a) where
  glb' a b = if a == b then pure a else err "glb': no glb for diffrent elements in a discrete domain."

deriving via EqDisc Int instance Glb' Int
deriving via EqDisc Double instance Glb' Double
deriving via EqDisc Bool instance Glb' Bool
deriving via EqDisc Char instance Glb' Char

class Discrete a

-- no method, intentionally

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

-- Another name of Maybe
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

instance (CheckLeast a, CheckLeast b) => CheckLeast (a, b) where
  isLeast (a, b) = isLeast a && isLeast b