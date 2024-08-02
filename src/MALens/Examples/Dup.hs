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

repair :: (Discrete a, Discrete b) => (a, b) -> MALens (M a, M b) (M a, M b)
repair def = pairM >>> letM def (introMd *** introMd)

-- >>> get (repair (1 :: Int , 2 :: Int)) (Some 1 , Some 2)
-- >>> get (repair (1 :: Int , 2 :: Int)) (Some 1 , None)
-- (Some 1,Some 2)
-- (NoneWith [],NoneWith [])
-- >>> put (repair (1 :: Int , 2 :: Int)) undefined (Some 3, Some 4)
-- >>> put (repair (1 :: Int , 2 :: Int)) (Some 5, Some 6) (Some 3, None)
-- >>> put (repair (1 :: Int , 2 :: Int)) (Some 5, None) (Some 3, None)
-- >>> put (repair (1 :: Int , 2 :: Int)) (None, None) (Some 3, None)
-- Ok (Some 3,Some 4)
-- Ok (Some 3,Some 6)
-- Ok (Some 3,Some 2)
-- Ok (Some 3,Some 2)

example3 :: (Lub a, Glb' a, Discrete a, Num a) => MALens (M a, M a) (M a, (M a, M a))
example3 = example1 >>> second (repair (0, 0)) >>> assocToLeftL >>> first (repair (0, 0)) >>> assocToRightL

-- >>> get (example3 @Int) (Some 1,  Some 1)
-- >>> get (example3 @Int) (Some 1,  Some 2)
-- >>> get (example3 @Int) (Some 1,  None)
-- (Some 1,(Some 1,Some 1))
-- (NoneWith ["glb': no glb for diffrent elements in a discrete domain."],(NoneWith ["glb': no glb for diffrent elements in a discrete domain."],NoneWith ["glb': no glb for diffrent elements in a discrete domain."]))
-- (NoneWith [],(NoneWith [],NoneWith []))

-- >>> put (example3 @Int) (Some 1, Some 1) (Some 2, (None, None))
-- >>> put (example3 @Int) (Some 1, Some 1) (Some 2, (Some 2, None))
-- >>> put (example3 @Int) (Some 1, Some 1) (Some 2, (Some 2, Some 2))
-- Err ["lub: no lub for different elements in a disrete domain."]
-- Err ["lub: no lub for different elements in a disrete domain."]
-- Ok (Some 2,Some 2)
-- >>> put (example3 @Int) (Some 0, Some 0) (Some 2, (None, None))
-- >>> put (example3 @Int) (Some 0, Some 0) (Some 2, (Some 2, None))
-- >>> put (example3 @Int) (Some 0, Some 0) (Some 2, (Some 2, Some 2))
-- Err ["lub: no lub for different elements in a disrete domain."]
-- Err ["lub: no lub for different elements in a disrete domain."]
-- Ok (Some 2,Some 2)

repair1 :: (Discrete a, Discrete b) => a -> MALens (M a, M b) (M a, M b)
repair1 a0 = second introMl >>> pairM >>> letM (a0, least) (first introMd)

-- >>> get (repair1 @Int @Int 0) (Some 1, Some 2)
-- >>> get (repair1 @Int @Int 0) (Some 1, None)
-- >>> get (repair1 @Int @Int 0) (None, Some 2)
-- (Some 1,Some 2)
-- (Some 1,NoneWith [])
-- (NoneWith [],NoneWith [])

-- >>> put (repair1 @Int @Int 0) undefined (Some 3, Some 4)
-- >>> put (repair1 @Int @Int 0) undefined (Some 3, None)
-- >>> put (repair1 @Int @Int 0) (Some 1, undefined) (None, Some 4)
-- >>> put (repair1 @Int @Int 0) (None, undefined) (None, Some 4)
-- >>> put (repair1 @Int @Int 0) (Some 1, undefined) (None, None)
-- >>> put (repair1 @Int @Int 0) (None, undefined) (None, None)
-- Ok (Some 3,Some 4)
-- Ok (Some 3,NoneWith [])
-- Ok (Some 1,Some 4)
-- Ok (Some 0,Some 4)
-- Ok (NoneWith [],NoneWith [])
-- Ok (NoneWith [],NoneWith [])

repair2 :: (Discrete a, Discrete b) => a -> MALens (M b, M a) (M b, M a)
repair2 b0 = swapL >>> repair1 b0 >>> swapL

example4 :: (Lub a, Glb' a, Discrete a, Num a) => MALens (M a, M a) (M a, (M a, M a))
example4 = example1 >>> second (repair1 0) >>> assocToLeftL >>> first (repair2 0) >>> assocToRightL

-- >>> get (example4 @Int) (Some 1,  Some 1)
-- >>> get (example4 @Int) (Some 1,  Some 2)
-- >>> get (example4 @Int) (Some 1,  None)
-- (Some 1,(Some 1,Some 1))
-- (NoneWith ["glb': no glb for diffrent elements in a discrete domain."],(NoneWith ["glb': no glb for diffrent elements in a discrete domain."],NoneWith ["glb': no glb for diffrent elements in a discrete domain."]))
-- (NoneWith [],(NoneWith [],NoneWith []))

-- >>> put (example4 @Int) (Some 1, Some 1) (Some 2, (None, None))
-- >>> put (example4 @Int) (Some 1, Some 1) (None, (Some 2, None))
-- >>> put (example4 @Int) (Some 1, Some 1) (None, (None, Some 2))
-- Err ["lub: no lub for different elements in a disrete domain."]
-- Ok (Some 2,Some 2)
-- Err ["lub: no lub for different elements in a disrete domain."]

-- >>> put (example4 @Int) (Some 1, Some 1) (None, (Some 2, Some 2))
-- >>> put (example4 @Int) (Some 1, Some 1) (Some 2, (None, Some 2))
-- >>> put (example4 @Int) (Some 1, Some 1) (Some 2, (Some 2, None))
-- Ok (Some 2,Some 2)
-- Err ["lub: no lub for different elements in a disrete domain.","lub: no lub for different elements in a disrete domain."]
-- Ok (Some 2,Some 2)

-- >>> put (example4 @Int) (Some 1, Some 1) (Some 2, (Some 2, Some 2))
-- Ok (Some 2,Some 2)

-- >>> put (example4 @Int) (Some 0, Some 0) (Some 0, (None, Some 0))
-- Ok (Some 0,Some 0)

example5 :: (Lub a, Glb' a, Discrete a, Num a) => MALens (M a, M a) (M a, (M a, M a))
example5 = example1 >>> second (repair2 0) >>> assocToLeftL >>> first (repair1 0) >>> assocToRightL

-- >>> get (example5 @Int) (Some 1,  Some 1)
-- >>> get (example5 @Int) (Some 1,  Some 2)
-- >>> get (example5 @Int) (Some 1,  None)
-- (Some 1,(Some 1,Some 1))
-- (Some 1,(NoneWith ["glb': no glb for diffrent elements in a discrete domain."],Some 2))
-- (Some 1,(NoneWith [],NoneWith []))

-- >>> put (example5 @Int) (Some 1, Some 1) (Some 2, (None, None))
-- >>> put (example5 @Int) (Some 1, Some 1) (None, (Some 2, None))
-- >>> put (example5 @Int) (Some 1, Some 1) (None, (None, Some 2))
-- Ok (Some 2,NoneWith [])
-- Err ["lub: no lub for different elements in a disrete domain.","lub: no lub for different elements in a disrete domain."]
-- Ok (NoneWith [],Some 2)

-- >>> put (example5 @Int) (Some 1, Some 1) (None, (Some 2, Some 2))
-- >>> put (example5 @Int) (Some 1, Some 1) (Some 2, (None, Some 2))
-- >>> put (example5 @Int) (Some 1, Some 1) (Some 2, (Some 2, None))
-- Err ["lub: no lub for different elements in a disrete domain."]
-- Ok (Some 2,Some 2)
-- Err ["lub: no lub for different elements in a disrete domain."]
