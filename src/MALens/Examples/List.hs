{-# LANGUAGE TypeApplications #-}

module MALens.Examples.List where

import Control.Category
import Prelude hiding (id, (.))

import Domain
import Err
import MALens

inListG :: Galois (Either () (a, [a])) [a]
inListG = Galois (pure . f) (pure . g)
  where
    f (Left _) = []
    f (Right (a, as)) = a : as

    g [] = Left ()
    g (a : as) = Right (a, as)

outListG :: Galois [a] (Either () (a, [a]))
outListG = invert inListG

inListL :: MALens (M (Either () (a, [a]))) (M [a])
inListL = liftGalois outListG

outListL :: MALens (M [a]) (M (Either () (a, [a])))
outListL = liftGalois inListG

consL :: MALens (M (a, [a])) (M [a])
consL = rightL >>> inListL

nilL :: MALens (M ()) (M [a])
nilL = leftL >>> inListL

mapL ::
  (Discrete a, Discrete b) =>
  a
  -> MALens a (M b)
  -> MALens (M [a]) (M [b])
mapL a0 elemL =
  outListL
    >>> cond (introMl >>> nilL) recon1 consCaseL recon2 (null @[])
  where
    consCaseL =
      (elemL *** (introMd >>> mapL a0 elemL))
        >>> pairM
        >>> consL

    recon1 :: Maybe (a, [a]) -> [b] -> Err ()
    recon1 _ _ = pure ()

    recon2 _ _ = pure (a0, [])
