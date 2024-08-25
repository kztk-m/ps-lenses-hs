{-# LANGUAGE TemplateHaskell #-}

module MALens.Example.M where

import Control.Category
import Prelude hiding (id, (.))

import MALens
import MALensTH

import Domain
import Err

example :: MALens (M (String, String, Int)) (M (String, Int))
example =
  letM
    ("", "", 0 :: Int)
    ( $(arrP [|\(x, y, z) -> ((x, z), y)|])
        >>> (introMd *** introMd)
        >>> fstL
    )

mapList :: MALens (M a) b -> MALens [a] [b]
mapList l = MALens g p
  where
    g = map (get l . Some)

    p _ [] = pure []
    p [] (y : ys) = do
      x' <- put l least y
      (x' :) <$> p [] ys
    p (x : xs) (y : ys) = do
      x' <- put l (Some x) y
      (x' :) <$> p xs ys
