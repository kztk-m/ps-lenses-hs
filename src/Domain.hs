{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE StandaloneDeriving #-}

module Domain where

import qualified Data.Map as M

import Control.Applicative (liftA2)
import Control.Monad (zipWithM)
import Err

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
data M a = NoneWith [String] | Some a deriving (Show, Eq, Functor)

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
instance CheckLeast (M a) where
  isLeast None = True
  isLeast _ = False

instance (LowerBounded a, LowerBounded b) => LowerBounded (a, b) where
  least = (least, least)

instance (CheckLeast a, CheckLeast b) => CheckLeast (a, b) where
  isLeast (a, b) = isLeast a && isLeast b