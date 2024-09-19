{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}

module MALens.Examples.List where

import Control.Category
import Prelude hiding (id, (.))

import Domain
import Err
import MALens
import MALensTH

inListG :: Galois (Either () (a, [a])) [a]
inListG = Galois (pure . f) (pure . g)
  where
    f (Left _) = []
    f (Right (a, as)) = a : as

    g [] = Left ()
    g (a : as) = Right (a, as)

outListG :: Galois [a] (Either () (a, [a]))
outListG = invert inListG

inListL' :: MALens (Either () (a, [a])) [a]
inListL' = MALens g p
  where
    g (Left _) = []
    g (Right (a, as)) = a : as

    p _ [] = pure $ Left ()
    p _ (a : as) = pure $ Right (a, as)

outListL' :: MALens [a] (Either () (a, [a]))
outListL' = MALens g p
  where
    g [] = Left ()
    g (a : as) = Right (a, as)

    p _ (Left ()) = pure $ []
    p _ (Right (a, as)) = pure $ a : as

inListL :: MALens (M (Either () (a, [a]))) (M [a])
inListL = liftGalois outListG

outListL :: MALens (M [a]) (M (Either () (a, [a])))
outListL = liftGalois inListG

consL :: MALens (M (a, [a])) (M [a])
consL = rightL >>> inListL

nilL :: MALens (M ()) (M [a])
nilL = leftL >>> inListL

-- mapL :: _
mapL :: a1 -> MALens a1 a2 -> MALens [a1] [a2]
mapL a0 elemL =
  outListL'
    >>> mapSumL id (elemL *** mapL a0 elemL) (\_ _ -> pure ()) (\_ (_, vs) -> pure (a0, replicate (length vs) a0))
    >>> inListL'

introMListD :: (Discrete a1) => a1 -> MALens [a1] [M a1]
introMListD a0 = mapL a0 introMd

sequenceL :: MALens [M a] (M [a])
sequenceL =
  outListL'
    >>> mapSumL introMd (second sequenceL >>> pairM) (\_ _ -> pure ()) r
    >>> sumM
    >>> inListL
  where
    r :: () -> M (a, [a]) -> Err (M a, [M a])
    r _ None = pure (None, [])
    r _ (Some (_, vs)) = pure (None, replicate (length vs) None)

-- >>> get sequenceL [None, Some 1]
-- NoneWith []

-- >>> put sequenceL [] None
-- Ok []
-- >>> put sequenceL [None, Some 1] None
-- Ok [NoneWith [],NoneWith []]
-- >>> put sequenceL [None, Some 1] (Some [3,4,5])
-- Ok [Some 3,Some 4,Some 5]

pNameScore :: MALens (String, String, Int) (String, Int)
pNameScore =
  $(arrP [|\(a, b, c) -> ((a, c), b)|])
    >>> fstL'

pNameScoreM :: MALens (M (String, String, Int)) (M (String, Int))
pNameScoreM = liftMissingDefault ("", "", 0) pNameScore

example1 :: MALens [(String, String, Int)] (M [(String, Int)])
example1 =
  introMListD ("", "", 0)
    >>> mapL least pNameScoreM
    >>> sequenceL

-- >>> get example1 [("Alice", "CS", 80)]
-- Some [("Alice",80)]

-- >>> put example1 [("Alice", "CS", 80)] (Some [("Alice",60)])
-- Ok [("Alice","CS",60)]
-- >>> put example1 [("Alice", "CS", 80)] (Some [("Alice",60), ("Bob", 90)])
-- Ok [("Alice","CS",60),("Bob","",90)]
