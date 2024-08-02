{-# LANGUAGE NoMonomorphismRestriction #-}

module MALens.Examples.Dup where

import Control.Category
import Domain
import MALens
import Prelude hiding (id, (.))

{-

      +--------
      |
------+
      |
      +---+
          |
          +-----
          |
      +---+
      |
------+
      |
      +---------

-}

example1 :: (Lub a, Glb' a) => MALens (M a, M a) (M a, (M a, M a))
example1 =
  (dup *** dup)
    >>> assocToRightL
    >>> second assocToLeftL
    >>> second (first merge)

-- >>> get (example1 @Int) (Some 1, Some 1)
-- >>> get (example1 @Int) (Some 1, Some 2)
-- >>> get (example1 @Int) (Some 1, None)
-- >>> get (example1 @Int) (None, Some 2)
-- (Some 1,(Some 1,Some 1))
-- (Some 1,(NoneWith ["glb': no glb for diffrent elements in a discrete domain."],Some 2))
-- (Some 1,(NoneWith [],NoneWith []))
-- (NoneWith [],(NoneWith [],Some 2))

-- >>> put (example1 @Int) undefined (Some 1, (Some 1, Some 1))
-- >>> put (example1 @Int) undefined (Some 1, (None, Some 1))
-- >>> put (example1 @Int) undefined (Some 1, (None, None))
-- >>> put (example1 @Int) undefined (None, (Some 1, None))
-- >>> put (example1 @Int) undefined (None, (None, Some 1))
-- Ok (Some 1,Some 1)
-- Ok (Some 1,Some 1)
-- Ok (Some 1,NoneWith [])
-- Ok (Some 1,Some 1)
-- Ok (NoneWith [],Some 1)

example2 :: (Discrete b, Lub b, Glb' b) => MALens (b, b) (M b, (M b, M b))
example2 = (introMd *** introMd) >>> example1

-- >>> get (example2 @Int) (1, 1)
-- >>> get (example2 @Int) (1, 2)
-- (Some 1,(Some 1,Some 1))
-- (Some 1,(NoneWith ["glb': no glb for diffrent elements in a discrete domain."],Some 2))
--
-- >>> put (example2 @Int) (1, 1) (Some 2, (None, None))
-- >>> put (example2 @Int) (1, 1) (None, (Some 2, None))
-- >>> put (example2 @Int) (1, 1) (None, (None, Some 2))
-- Ok (2,1)
-- Ok (2,2)
-- Ok (1,2)
-- >>> put (example2 @Int) (1, 2) (Some 2, (None, Some 3))
-- Ok (2,3)
