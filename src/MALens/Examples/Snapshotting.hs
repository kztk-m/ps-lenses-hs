{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ViewPatterns #-}

module MALens.Examples.Snapshotting where

import Control.Category
import Prelude hiding (id, (.))

import MALens

import Domain
import Err

import Data.Bits (Bits (..), (.&.))
import qualified Data.Char
import qualified Data.Map as M
import Data.Maybe (fromJust)
import Data.Word
import MALensTH

-- Examples

validateCheckSum :: MALens (Int, [Int]) (M [Int])
validateCheckSum =
  ((introMd @Int >>> introMl) *** introMd @[Int])
    >>> pairM
    >>> liftMissing (snapshot (\a -> assertEqL (sum a)) >>> second introMd >>> pairM)
    >>> joinM
    >>> liftMissingDefault ((), []) deleteUnit

validateCheckSum' :: MALens (Int, [Int]) (M [Int])
validateCheckSum' =
  snapshot (\a -> introMd >>> assertEqL (sum a))
    >>> second introMd
    >>> pairM
    >>> liftMissingDefault ((), []) deleteUnit

validateCheckSum'' :: MALens (Int, [Int]) (M [Int])
validateCheckSum'' =
  (introMd *** introMd)
    >>> introMl
    >>> snapshotM (\xs -> assertEqL (sum xs))
    >>> letM (least, []) (introMl *** introMd)
    -- >>> unpairMld []
    >>> first joinM
    --    >>> letMd undefined (second introMd)
    >>> pairM
    >>> deleteUnitM

validateCheckSumM :: MALens (M (Int, [Int])) (M [Int])
validateCheckSumM =
  letM (0, []) (introMd *** introMd)
    >>> introMl
    >>> snapshotM (\xs -> assertEqL (sum xs))
    >>> letM (least, []) (introMl *** introMd)
    >>> first joinM
    --    >>> letMd (None, []) (second introMd)
    >>> pairM
    >>> deleteUnitM

-- >>> get validateCheckSum (10,[1,2,3,4])
-- >>> get validateCheckSum (9,[1,2,3,4])
-- Some [1,2,3,4]
-- NoneWith ["assertEqL: update on constant"]

-- >>> put validateCheckSum (10,[1,2,3,4]) (Some [1,2,3,4,5])
-- >>> put validateCheckSum (9,[1,2,3,4]) (Some [1,2,3,4,5])
-- Ok (15,[1,2,3,4,5])
-- Ok (15,[1,2,3,4,5])

-- >>> get validateCheckSum' (10,[1,2,3,4])
-- >>> get validateCheckSum' (9,[1,2,3,4])
-- Some [1,2,3,4]
-- NoneWith ["assertEqL: update on constant"]

-- >>> put validateCheckSum' (10,[1,2,3,4]) (Some [1,2,3,4,5])
-- >>> put validateCheckSum' (9,[1,2,3,4]) (Some [1,2,3,4,5])
-- Ok (15,[1,2,3,4,5])
-- Ok (15,[1,2,3,4,5])

-- >>> get validateCheckSum'' (10,[1,2,3,4])
-- >>> get validateCheckSum'' (9,[1,2,3,4])
-- Some [1,2,3,4]
-- NoneWith ["assertEqL: update on constant"]

-- >>> put validateCheckSum'' (10,[1,2,3,4]) (Some [1,2,3,4,5])
-- >>> put validateCheckSum'' (9,[1,2,3,4]) (Some [1,2,3,4,5])
-- Ok (15,[1,2,3,4,5])
-- Ok (15,[1,2,3,4,5])

-- >>> put validateCheckSumM (Some (10,[1,2,3,4])) (Some [1,2,3,4,5])
-- >>> put validateCheckSumM (Some (9,[1,2,3,4])) (Some [1,2,3,4,5])
-- >>> put validateCheckSumM None (Some [1,2,3,4,5])
-- Ok (Some (15,[1,2,3,4,5]))
-- Ok (Some (15,[1,2,3,4,5]))
-- Ok (Some (15,[1,2,3,4,5]))

instance Discrete Word8

assertByte :: Word8 -> MALens (M Word8) (M ())
assertByte = assertEqL

-- >>> get (assertEqL 2) (Some 2)
-- >>> get (assertEqL 2) (Some 3)
-- Some ()
-- NoneWith ["assertEqL: update on constant"]
-- >>> put (assertEqL 2) undefined None
-- >>> put (assertEqL 2) undefined (Some ())
-- Ok (NoneWith [])
-- Ok (Some 2)

-- >>> get (assertEqL 2 >>> joinM) (Some 2)
-- >>> get (assertEqL 2 >>> joinM) (Some 3)
-- ()
-- ()
-- >>> put (assertEqL 2 >>> joinM) undefined ()
-- Ok (NoneWith [])

-- >>> get (introMd >>> assertEqL 2) 2
-- >>> get (introMd >>> assertEqL 2) 3
-- Some ()
-- NoneWith ["assertEqL: update on constant"]

-- >>> put (introMd >>> assertEqL 2) 3 None
-- >>> put (introMd >>> assertEqL 2) 3 (Some ())
-- Ok 3.0
-- Ok 2.0

-- concrete hash is not important here
hash :: (String, String, Int) -> (Word8, Word8)
hash (s1, s2, n) =
  let i = hashStr s1 `xor` hashStr s2 `xor` n
      b1 = fromIntegral (i .&. 0xff) :: Word8
      b2 = fromIntegral ((i .&. 0xff00) `shiftR` 8) :: Word8
  in  (b1, b2)

hashStr :: [Char] -> Int
hashStr = foldr (\c -> xor (rotateL (Data.Char.ord c) 13)) 0

removeH :: MALens ((Word8, Word8), (String, String, Int)) (M (String, String, Int))
removeH =
  snapshot
    ( \x -> case hash x of
        (b1, b2) -> ((introMd >>> assertByte b1) *** (introMd >>> assertByte b2)) >>> pairM >>> $(arrPM [|\((), ()) -> ()|])
    )
    >>> second introMd
    >>> pairM
    >>> $(arrPM [|\((), a) -> a|])

-- >>> put removeH undefined (Some ("Brown", "CS", 90))
-- Ok ((90,192),("Brown","CS",90))
-- >>> get removeH ((90,192),("Brown","CS",90))
-- Some ("Brown","CS",90)
-- >>> get removeH ((220,16),("Brown","CS",90))
-- NoneWith ["assertEqL: update on constant","assertEqL: update on constant"]

-- >>> put removeH undefined (Some ("Brown", "CS", 880))
-- Ok ((112,195),("Brown","CS",880))

removeH' :: MALens ((Word8, Word8), (String, String, Int)) (M (String, String, Int))
removeH' =
  snapshot
    ( \x -> case hash x of
        (b1, b2) ->
          first (introMd >>> assertByte b1)
            >>> second introMd
            >>> pairM
            >>> deleteUnitM
            >>> assertByte b2
    )
    >>> second introMd
    >>> pairM
    >>> $(arrPM [|\((), a) -> a|])

-- >>> let pt = put (introMd >>> assertEqL (0 :: Int) >>> constLunit (0 :: Int))
-- >>> pt 0 None
-- >>> pt 0 (Some 2)
-- >>> pt 0 (Some 0)
-- Ok 0
-- Err ["constLunit: update on constant"]
-- Ok 0

removeH'' :: (Eq b, Discrete s, Discrete b, Show b, Show s) => (s -> b) -> MALens (b, s) (M s)
removeH'' h =
  snapshot
    ( \x ->
        let bs = h x
        in  introMd >>> assertEqL bs
    )
    >>> second introMd
    >>> pairM
    >>> liftMissing id
    >>> $(arrPM [|\((), a) -> a|])

-- introUnit
--   >>> $(arrP [|\(u, (b, s)) -> ((u, s), b)|])
--   >>> first (snapshot (\x -> constL (h x)))
--   >>> $(arrP [|\((b1, s), b2) -> ((b1, b2), s)|])
--   >>> first (snapshot (\b -> introMd >>> assertEqL b))
--   >>> $(arrP [|\((u1, b2), s) -> ((b2, s), u1)|])
--   >>> inspectL "H"
--   >>> first (snapshot (\x -> introMd >>> assertEqL (h x)))
--   >>> inspectL "HH"
--   >>> $(arrP [|\((u2, s), u1) -> ((u1, u2), s)|])
--   >>> (pairM *** introMd)
--   >>> pairM
--   >>> $(arrPM [|\(((), ()), s) -> s|])

-- >>> get (removeH'' sum) (6, [1,2,3 :: Int])
-- >>> get (removeH'' sum) (6, [1,2])
-- Some [1,2,3]
-- NoneWith ["assertEqL: update on constant"]

-- >>> put (removeH'' sum) (6, [1,2,3]) (Some [1,2,3,4 :: Int])
-- >>> put (removeH'' sum) (6, [1,2]) (Some [1,2,3,4 :: Int])
-- Ok (10,[1,2,3,4])
-- Err ["put liftMissing: None (Some _)\n[(\"liftMissing\",SrcLoc {srcLocPackage = \"malens-0.1.0.0-inplace\", srcLocModule = \"MALens.Examples.Snapshotting\", srcLocFile = \"/Users/kztk/work/lens_for_missing_values_hs/src/MALens/Examples/Snapshotting.hs\", srcLocStartLine = 197, srcLocStartCol = 9, srcLocEndLine = 197, srcLocEndCol = 20})]"]

assertNilL :: MALens (M [a]) (M ())
assertNilL = liftGalois $ Galois f g
  where
    f _ = pure []
    g [] = pure ()
    g _ = err "assertNilL: expect []"

assertConsL :: MALens (M [a]) (M (a, [a]))
assertConsL = liftGalois $ Galois f g
  where
    f (a, as) = pure (a : as)
    g (a : as) = pure (a, as)
    g _ = err "assertConsL: expect non-empty list"

removeHList :: forall s. (Discrete s) => (s -> [Word8]) -> MALens ([Word8], s) (M s)
removeHList h =
  snapshot k
    >>> second introMd
    >>> pairM
    >>> $(arrPM [|\((), a) -> a|])
  where
    k :: s -> MALens [Word8] (M ())
    k s = introMd >>> go (h s)
      where
        go :: [Word8] -> MALens (M [Word8]) (M ())
        go [] = assertNilL
        go (b : bs) =
          assertConsL
            >>> letM (0, []) (((introMd >>> assertByte b) *** (introMd >>> go bs)) >>> pairM >>> $(arrPM [|\((), ()) -> ()|]))

-- >>> get (removeHList id) ([1,2,3,4], [1,2,3,4])
-- >>> get (removeHList id) ([1,2,3,4], [1,2,3,4,5])
-- >>> get (removeHList id) ([1,2,3,4], [1,2,3])
-- Some [1,2,3,4]
-- NoneWith ["assertConsL: expect non-empty list"]
-- NoneWith ["assertNilL: expect []"]

-- >>> put (removeHList id) ([1,2,3], [1,2,3]) (Some [1,2,3,4])
-- Ok ([1,2,3,4],[1,2,3,4])
-- >>> put (removeHList id) ([1,2,3], [1,2,3]) (Some [1,2])
-- Ok ([1,2],[1,2])
-- >>> put (removeHList id) ([1,2,3], [11,2,3]) (Some [1,2])
-- Ok ([1,2],[1,2])

-- Check: v needs not to be discrete
insertG ::
  (Ord k, Discrete k) => k -> Galois (v, M.Map k v) (M.Map k v)
insertG k = Galois f g
  where
    f (v, m)
      | M.member k m = err "insertG: The map shouldn't contain the key"
      | otherwise = pure $ M.insert k v m
    g m = case M.lookup k m of
      Just v -> pure (v, M.delete k m)
      Nothing -> err "insertG: no-key in the given map"

tryExtractG ::
  (Ord k, Discrete k) =>
  k
  -> Galois (M.Map k v) (Either (M.Map k v) (v, M.Map k v))
tryExtractG k = Galois f g
  where
    f m = case M.lookup k m of
      Nothing -> pure (Left m)
      Just v -> pure (Right (v, M.delete k m))
    g (Left m)
      | not (M.member k m) = pure m
      | otherwise = err "tryExtractG: m of Left m shouldn't contain the given key"
    g (Right (v, m))
      | not (M.member k m) = pure (M.insert k v m)
      | otherwise = err "tryExtractG: m of Right (_,m) shouldn't contain the given key"

insertL :: (Ord k, Discrete k) => k -> MALens (M (v, M.Map k v)) (M (M.Map k v))
insertL k = liftGalois (invert $ insertG k)

extractL :: (Ord k, Discrete k) => k -> MALens (M (M.Map k v)) (M (v, M.Map k v))
extractL k = liftGalois (insertG k)

tryExtractL ::
  (Discrete k, Ord k) =>
  k
  -> MALens (M (M.Map k v)) (M (Either (M.Map k v) (v, M.Map k v)))
tryExtractL k = liftGalois (invert $ tryExtractG k)

-- We don't need the constraint (Discrete k, Discrete a) here, as
-- the empty map can no elements of type k or a---nothing can be missing.
assertEmptyG :: Galois (M.Map k a) ()
assertEmptyG = Galois f g
  where
    f m
      | M.null m = pure ()
      | otherwise = err "checkEmptyG: expects the empty"
    g () = pure M.empty

assertEmptyL :: (Discrete k, Discrete v) => MALens (M (M.Map k v)) (M ())
assertEmptyL = liftGalois (invert assertEmptyG)

emptyL :: MALens (M ()) (M (M.Map k a))
emptyL = liftGalois assertEmptyG

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

toContainer ::
  forall k a.
  (Ord k, Discrete a, Discrete k) =>
  MALens (M [(k, a)]) (M (M.Map k a, [k]))
toContainer =
  outListL
    >>> condD nilCase r1 consCase r2 (null . snd)
  where
    nilCase :: MALens () (M (M.Map k a, [k]))
    nilCase = introMd >>> dup >>> (emptyL *** nilL) >>> pairM

    r1 :: Maybe ((k, a), [(k, a)]) -> (M.Map k a, [k]) -> Err ()
    r1 _ _ = pure ()

    consCase :: MALens ((k, a), [(k, a)]) (M (M.Map k a, [k]))
    consCase =
      second (introMd >>> toContainer)
        >>> assocToRightL
        >>> swapL
        >>> snapshot
          ( \k ->
              first introMd
                >>> pairM
                >>> liftMissing (assocToLeftL >>> first (introMd >>> insertL k) >>> second introMd >>> pairM)
                >>> joinM
          )
        >>> second introMd
        >>> pairM
        >>> liftMissing (assocToRightL >>> second (swapL >>> (introMd *** introMd) >>> pairM >>> consL) >>> first introMd >>> pairM)
        >>> joinM

    r2 :: Maybe () -> (M.Map k a, [k]) -> Err ((k, a), [(k, a)])
    r2 _ (m, ks) =
      -- ks must be a non-empty list
      let res = [(kk, vv) | kk <- ks, let !vv = fromJust (M.lookup kk m)]
      in  pure (head res, tail res)

toContainer' ::
  forall k a.
  (Ord k, Discrete a, Discrete k) =>
  MALens (M [(k, a)]) (M (M.Map k a, [k]))
toContainer' =
  outListL
    >>> condD nilCase r1 consCase r2 (null . snd)
  where
    nilCase :: MALens () (M (M.Map k a, [k]))
    nilCase = introMd >>> dup >>> (emptyL *** nilL) >>> pairM

    r1 :: Maybe ((k, a), [(k, a)]) -> (M.Map k a, [k]) -> Err ()
    r1 _ _ = pure ()

    consCase :: MALens ((k, a), [(k, a)]) (M (M.Map k a, [k]))
    consCase =
      second (introMd >>> toContainer)
        >>> assocToRightL
        >>> swapL
        >>> (first introMd *** introMd)
        >>> introMl
        >>> snapshotM
          ( \k ->
              second (letM (M.empty, []) (introMd *** introMd)) -- second (introMinMfst M.empty >>> introMinMsnd [] >>> joinM)
                >>> assocToLeftL
                >>> first (pairM >>> insertL k)
          )
        >>> liftMissing (second introMd) -- we don't want to provide the default value for k
        >>> joinM
        >>> assocToRightL
        >>> second (swapL >>> pairM >>> consL)
        >>> pairM

    r2 :: Maybe () -> (M.Map k a, [k]) -> Err ((k, a), [(k, a)])
    r2 _ (m, ks) =
      -- ks must be a non-empty list
      let res = [(kk, vv) | kk <- ks, let !vv = fromJust (M.lookup kk m)]
      in  pure (head res, tail res)

-- >>> get toContainer (Some [("a",0 :: Int),("b",1)])
-- Some (fromList [("a",0),("b",1)],["a","b"])

-- >>> put toContainer None $ Some (M.fromList [("a",0 :: Int),("b",1)],["a","b"])
-- Ok (Some [("a",0),("b",1)])

-- >>> get toContainer' (Some [("a",0 :: Int),("b",1)])
-- Some (fromList [("a",0),("b",1)],["a","b"])

-- >>> put toContainer' None $ Some (M.fromList [("a",0 :: Int),("b",1)],["a","b"])
-- Ok (Some [("a",0),("b",1)])

fromContainer ::
  forall k a.
  (Show k, Show a) =>
  (Ord k, Discrete k, Discrete a) =>
  MALens (M (M.Map k a, [k])) (M [(k, a)])
fromContainer =
  liftMissingDefault
    (M.empty, [])
    ( introMd
        *** (introMd >>> outListL)
        >>> swapL
        >>> pairM
        >>> dist
        >>> inspectL "1-cond"
        >>> condD lCase lRec rCase rRec null
    )
    >>> joinM
  where
    lCase :: MALens ((), M.Map k a) (M [(k, a)])
    lCase = introMd *** (introMd >>> assertEmptyL) >>> pairM >>> liftMissing deleteUnit >>> nilL

    lRec :: Maybe ((k, [k]), M.Map k a) -> [(k, a)] -> Err ((), M.Map k a)
    lRec (Just (_, m)) _ = pure ((), m)
    lRec Nothing vs = pure ((), M.fromList vs)

    rRec :: Maybe ((), M.Map k a) -> [(k, a)] -> Err ((k, [k]), M.Map k a)
    rRec (Just (_, m)) ((k, _) : _) = pure ((k, []), m)
    rRec _ vs@((k, _) : _) = pure ((k, []), M.fromList vs)
    -- rRec Nothing vs@((k, _) : _) = pure ((k, []), M.fromList vs)
    rRec _ _ = err "Cannot happen?"

    rCase :: MALens ((k, [k]), M.Map k a) (M [(k, a)])
    rCase =
      assocToRightL
        >>> swapL
        >>> snapshot
          ( \k ->
              (introMd *** (introMd >>> tryExtractL k))
                >>> swapL
                >>> pairM
                >>> dist
                >>> condD br1 rec1 (br2 k) (rec2 k) (notElem k . map fst)
          )
        >>> inspectL "after-ss"
        >>> second introMd
        >>> swapL
        >>> introMl
        >>> snapshotM
          ( \case
              [] -> constL () >>> introMd
              (k, _) : _ -> assertEqL k
          )
        >>> inspectL "after-erasing-k"
        >>> liftMissingDefault (None, []) (second introMd >>> pairM >>> liftMissingDefault ((), []) deleteUnit)
        >>> inspectL "h1"
        >>> joinM
      where
        -- >>> second introM
        -- >>> swapL
        -- >>> pairM
        -- >>> liftMissing (snapshot (\xs -> introM >>> assertEqL (fst $ head xs)) >>> second introM >>> pairM)
        -- >>> joinM
        -- >>> liftMissingDefault ((), []) deleteUnit

        br1 :: MALens (M.Map k a, [k]) (M [(k, a)])
        br1 = inspectL "br1" >>> introMd >>> fromContainer

        rec1 :: Maybe ((a, M.Map k a), [k]) -> [(k, a)] -> Err (M.Map k a, [k])
        rec1 _ v = pure (M.fromList v, map fst v)

        br2 :: k -> MALens ((a, M.Map k a), [k]) (M [(k, a)])
        br2 k =
          assocToRightL
            >>> (introMd *** (introMd >>> fromContainer))
            >>> introUnit
            >>> first (introMd >>> constL k >>> introMd)
            >>> assocToLeftL
            >>> first pairM
            >>> pairM
            >>> consL

        rec2 :: k -> Maybe (M.Map k a, [k]) -> [(k, a)] -> Err ((a, M.Map k a), [k])
        rec2 k _ v = pure ((fromJust (Prelude.lookup k v), M.delete k (M.fromList v)), map fst v)

fromContainer' ::
  forall k a.
  (Show k, Show a) =>
  (Ord k, Discrete k, Discrete a) =>
  MALens (M (M.Map k a, [k])) (M [(k, a)])
fromContainer' =
  liftMissingDefault
    (M.empty, [])
    ( introMd
        *** (introMd >>> outListL)
        >>> swapL
        >>> pairM
        >>> dist
        >>> inspectL "1-cond"
        >>> condD lCase lRec rCase rRec null
    )
    >>> joinM
  where
    lCase :: MALens ((), M.Map k a) (M [(k, a)])
    lCase = introMd *** (introMd >>> assertEmptyL) >>> pairM >>> deleteUnitM >>> nilL

    lRec :: Maybe ((k, [k]), M.Map k a) -> [(k, a)] -> Err ((), M.Map k a)
    lRec (Just (_, m)) _ = pure ((), m)
    lRec Nothing vs = pure ((), M.fromList vs)

    rRec :: Maybe ((), M.Map k a) -> [(k, a)] -> Err ((k, [k]), M.Map k a)
    rRec (Just (_, m)) ((k, _) : _) = pure ((k, []), m)
    rRec _ vs@((k, _) : _) = pure ((k, []), M.fromList vs)
    -- rRec Nothing vs@((k, _) : _) = pure ((k, []), M.fromList vs)
    rRec _ _ = err "Cannot happen?"

    rCase :: MALens ((k, [k]), M.Map k a) (M [(k, a)])
    rCase =
      assocToRightL
        >>> swapL
        >>> ((introMd *** introMd) *** introMd)
        >>> introMl
        >>> snapshotM
          ( \k ->
              second (tryExtractL k)
                >>> swapL
                >>> pairM
                >>> dist
                >>> condD br1 rec1 (br2 k) (rec2 k) (notElem k . map fst)
          )
        >>> inspectL "after-ss"
        >>> liftMissing (second introMd) -- we don't want to give a default value for k
        >>> swapM
        >>> snapshotM
          ( \case
              [] -> constL () >>> introMd
              (k, _) : _ -> assertEqL k
          )
        >>> inspectL "after-erasing-k"
        >>> (liftMissing (second introMd) >>> joinM >>> pairM >>> deleteUnitM)
        --         >>> liftMissingDefault (None, []) (second introM >>> pairM >>> liftMissingDefault ((), []) deleteUnit)
        >>> inspectL "h1"
      where
        -- >>> second introM
        -- >>> swapL
        -- >>> pairM
        -- >>> liftMissing (snapshot (\xs -> introM >>> assertEqL (fst $ head xs)) >>> second introM >>> pairM)
        -- >>> joinM
        -- >>> liftMissingDefault ((), []) deleteUnit

        br1 :: MALens (M.Map k a, [k]) (M [(k, a)])
        br1 = inspectL "br1" >>> introMd >>> fromContainer

        rec1 :: Maybe ((a, M.Map k a), [k]) -> [(k, a)] -> Err (M.Map k a, [k])
        rec1 _ v = pure (M.fromList v, map fst v)

        br2 :: k -> MALens ((a, M.Map k a), [k]) (M [(k, a)])
        br2 k =
          assocToRightL
            >>> (introMd *** (introMd >>> fromContainer))
            >>> introUnit
            >>> first (introMd >>> constL k >>> introMd)
            >>> assocToLeftL
            >>> first pairM
            >>> pairM
            >>> consL

        rec2 :: k -> Maybe (M.Map k a, [k]) -> [(k, a)] -> Err ((a, M.Map k a), [k])
        rec2 k _ v = pure ((fromJust (Prelude.lookup k v), M.delete k (M.fromList v)), map fst v)

-- >>> get fromContainer $ Some (M.fromList [("a",0 :: Int),("b",1)],["a","b"])
-- Some [("a",0),("b",1)]

-- >>> get fromContainer $ Some (M.fromList [("b",1)], [])
-- NoneWith []

-- >>> put fromContainer (Some (M.fromList [], [])) $ Some [("a",0),("b",1)]
-- Ok (Some (fromList [("a",0.0),("b",1.0)],["a","b"]))

-- >>> put fromContainer None $ Some [("a",0),("b",1)]
-- Ok (Some (fromList [("a",0.0),("b",1.0)],["a","b"]))

-- >>> get fromContainer' $ Some (M.fromList [("a",0 :: Int),("b",1)],["a","b"])
-- Some [("a",0),("b",1)]

-- >>> get fromContainer' $ Some (M.fromList [("b",1)], [])
-- NoneWith []

-- >>> put fromContainer' (Some (M.fromList [], [])) $ Some [("a",0),("b",1)]
-- Ok (Some (fromList [("a",0.0),("b",1.0)],["a","b"]))

-- >>> put fromContainer' None $ Some [("a",0),("b",1)]
-- Ok (Some (fromList [("a",0.0),("b",1.0)],["a","b"]))

mapKeyBody ::
  forall k a b.
  (Ord k, Discrete k, Discrete a, Discrete b) =>
  a
  -> MALens (M a) (M b)
  -> MALens (M (M.Map k a), [k]) (M (M.Map k b), [k])
mapKeyBody def f =
  snapshot
    ( foldr
        ( \k l ->
            tryExtractL k
              >>> condD
                (introMd >>> l)
                recon1
                (first (introMd >>> f) >>> second (introMd >>> l) >>> pairM >>> insertL k)
                recon2
                (not . M.member k)
        )
        (emptyL . assertEmptyL)
    )
  where
    recon1 :: Maybe (a, M.Map k a) -> M.Map k b -> Err (M.Map k a)
    recon1 (Just (_, m)) _ = pure m
    recon1 Nothing _ = err "recon1: expects the source value"
    recon2 :: Maybe (M.Map k a) -> M.Map k b -> Err (a, M.Map k a)
    recon2 (Just m) _ = pure (def, m)
    recon2 Nothing _ = err "recon2: expects the source value"

testL :: (Ord k, Discrete k) => MALens (M (M.Map k (Int, String)), [k]) (M (M.Map k Int), [k])
testL = mapKeyBody (0 :: Int, "") (liftMissing (second introMd >>> fstL))

--- >>> get testL (None, ["Alice","Bob","Cecil"])
-- (NoneWith [],["Alice","Bob","Cecil"])

--- >>> get testL (Some $ M.fromList [("Alice",(0,"Hey")), ("Bob",(1,"Bbb")), ("Cecil",(2,"Cxx"))], ["Alice","Bob","Cecil"])
-- (Some (fromList [("Alice",0),("Bob",1),("Cecil",2)]),["Alice","Bob","Cecil"])

--- >>> put testL (Some $ M.fromList [("Alice",(0,"Hey")), ("Bob",(1,"Bbb")), ("Cecil",(2,"Cxx"))], ["Alice","Bob","Cecil"]) (Some $ M.fromList [], [])
-- Ok (Some (fromList []),[])

--- >>> put testL (Some $ M.fromList [("Alice",(0,"Hey")), ("Bob",(1,"Bbb")), ("Cecil",(2,"Cxx"))], ["Alice","Bob","Cecil"]) (Some $ M.fromList [("Bob",99), ("David",100)], ["Bob", "David"])
-- Ok (Some (fromList [("Bob",(99,"Bbb")),("David",(100,""))]),["Bob","David"])

mapKeyBody' ::
  forall k a b.
  (Show k, Show a) =>
  (Ord k, Discrete k, Discrete a, Discrete b) =>
  a
  -> MALens (M a) (M b)
  -> MALens (M (M.Map k a, [k])) (M (M.Map k b, [k]))
mapKeyBody' def f =
  letM (M.empty, []) (introMd *** introMd) -- (introMinMfst M.empty >>> introMinMsnd [])
    >>> introMl
    >>> inspectL "mapKeyBody'"
    >>> snapshotM
      ( foldr
          ( \k l ->
              tryExtractL k
                >>> condD
                  (introMd >>> l)
                  recon1
                  (first (introMd >>> f) >>> second (introMd >>> l) >>> pairM >>> insertL k)
                  recon2
                  (not . M.member k)
          )
          (emptyL . assertEmptyL)
      )
    >>> letM (least, []) (second introMd >>> pairM)
  where
    -- >>> letM (least, []) (introMl *** introMd)
    -- >>> first joinM
    -- >>> pairM

    -- >>> introMinMsnd []
    -- >>> joinM
    -- >>> pairM

    recon1 :: Maybe (a, M.Map k a) -> M.Map k b -> Err (M.Map k a)
    recon1 (Just (_, m)) _ = pure m
    recon1 Nothing _ = err "recon1: expects the source value"
    recon2 :: Maybe (M.Map k a) -> M.Map k b -> Err (a, M.Map k a)
    recon2 (Just m) _ = pure (def, m)
    recon2 Nothing _ = pure (def, M.empty) -- err "recon2: expects the source value"

mapKeyBody'' ::
  forall k a b.
  (Show k, Show a) =>
  (Ord k, Discrete k, Discrete a) =>
  a
  -> MALens (M a) (M b)
  -> MALens (M (M.Map k a, [k])) (M (M.Map k b, [k]))
mapKeyBody'' def f =
  letM (M.empty, []) $
    snapshot
      ( foldr
          ( \k l ->
              introMd
                >>> tryExtractL k
                >>> cond
                  l
                  recon1
                  (first (introMd >>> f) >>> second l >>> pairM >>> insertL k)
                  recon2
                  (EnsureMonotone $ not . M.member k)
          )
          (introMd >>> emptyL . assertEmptyL)
      )
      >>> second introMd
      >>> pairM
  where
    -- letM (M.empty, []) (introMd *** introMd) -- (introMinMfst M.empty >>> introMinMsnd [])
    --   >>> introMl
    --   >>> inspectL "mapKeyBody'"
    --   >>> snapshotM
    --     ( foldr
    --         ( \k l ->
    --             tryExtractL k
    --               >>> condD
    --                 (introMd >>> l)
    --                 recon1
    --                 (first (introMd >>> f) >>> second (introMd >>> l) >>> pairM >>> insertL k)
    --                 recon2
    --                 (not . M.member k)
    --         )
    --         (emptyL . assertEmptyL)
    --     )
    --   >>> letM (least, []) (second introMd >>> pairM)

    -- >>> letM (least, []) (introMl *** introMd)
    -- >>> first joinM
    -- >>> pairM

    -- >>> introMinMsnd []
    -- >>> joinM
    -- >>> pairM

    recon1 :: Maybe (a, M.Map k a) -> M.Map k b -> Err (M.Map k a)
    recon1 _ _ = err "Never called."
    -- recon1 (Just (_, m)) _ = pure m
    -- recon1 Nothing _ = err "recon1: expects the source value"
    recon2 :: Maybe (M.Map k a) -> M.Map k b -> Err (a, M.Map k a)
    recon2 (Just m) _ = pure (def, m)
    recon2 Nothing _ = pure (def, M.empty) -- err "recon2: expects the source value"

-- testL' :: (Ord k, Discrete k, SHo wk) => MALens (M (M.Map k (Int, String), [k])) (M (M.Map k Int, [k]))
-- testL' = mapKeyBody' (0 :: Int, "") (liftMissing (second introM >>> fstL))

mapKeyBodyNoCase ::
  forall k a b.
  (Show k, Show a) =>
  (Ord k, Discrete k, Discrete a) =>
  a
  -> MALens (M a) (M b)
  -> MALens (M (M.Map k a, [k])) (M (M.Map k b, [k]))
mapKeyBodyNoCase def f =
  letM (M.empty, []) $
    snapshot
      ( foldr
          ( \k l ->
              introMd
                >>> extractL k
                >>> letM (def, M.empty) (((introMd >>> f) *** l) >>> pairM >>> insertL k)
          )
          (introMd >>> emptyL . assertEmptyL)
      )
      >>> second introMd
      >>> pairM

mapKey ::
  (Ord k, Discrete a, Discrete k, Discrete b, Show k, Show b) =>
  a
  -> MALens (M a) (M b)
  -> MALens (M [(k, a)]) (M [(k, b)])
mapKey def f =
  toContainer
    >>> liftMissingDefault (M.empty, []) (first introMd >>> mapKeyBody def f >>> second introMd >>> pairM)
    >>> joinM
    >>> fromContainer

mapKey' ::
  (Ord k, Discrete a, Discrete k, Discrete b, Show k, Show a, Show b) =>
  a
  -> MALens (M a) (M b)
  -> MALens (M [(k, a)]) (M [(k, b)])
mapKey' def f =
  toContainer'
    >>> mapKeyBody'' def f
    -- >>> letM (M.empty, []) (introMd >>> mapKeyBody' def f)
    >>> fromContainer'

testMK :: (Ord k, Discrete k, Show k) => MALens (M [(k, (Int, String))]) (M [(k, Int)])
testMK = mapKey (0 :: Int, "") (liftMissing (second introMd >>> fstL))

testMK' :: (Ord k, Discrete k, Show k) => MALens (M [(k, (Int, String))]) (M [(k, Int)])
testMK' = mapKey' (0 :: Int, "") (liftMissing (second introMd >>> fstL))

-- >>> get testMK (Some [("Alice",(0,"Hey")), ("Bob",(1,"Bbb")), ("Cecil",(2,"Cxx"))])
-- Some [("Alice",0),("Bob",1),("Cecil",2)]

-- >>> put testMK (Some [("Alice",(0,"Hey")), ("Bob",(1,"Bbb")), ("Cecil",(2,"Cxx"))]) (Some [("Bob",1),("David",2),("Alice",99)])
-- Ok (Some [("Bob",(1,"Bbb")),("David",(2,"")),("Alice",(99,"Hey"))])

-- >>> put testMK None (Some [("Bob",1),("David",2),("Alice",99)])
-- Ok (Some [("Bob",(1,"")),("David",(2,"")),("Alice",(99,""))])

-- >>> get testMK' (Some [("Alice",(0,"Hey")), ("Bob",(1,"Bbb")), ("Cecil",(2,"Cxx"))])
-- Some [("Alice",0),("Bob",1),("Cecil",2)]

-- >>> put testMK' (Some [("Alice",(0,"Hey")), ("Bob",(1,"Bbb")), ("Cecil",(2,"Cxx"))]) (Some [("Bob",1),("David",2),("Alice",99)])
-- Ok (Some [("Bob",(1,"Bbb")),("David",(2,"")),("Alice",(99,"Hey"))])

-- >>> put testMK' None (Some [("Bob",1),("David",2),("Alice",99)])
-- Ok (Some [("Bob",(1,"")),("David",(2,"")),("Alice",(99,""))])
