{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Err (
  Err (..),
  err,
) where

import Control.Monad.Except (MonadError (..))

data Err a = Err ![String] | Ok !a deriving stock (Show)

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

instance MonadError [String] Err where
  throwError = Err

  catchError (Err s) f = f s
  catchError (Ok a) _ = Ok a

instance MonadFail Err where
  fail = err