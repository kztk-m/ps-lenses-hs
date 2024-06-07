{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

module MALens.Examples where

import Control.Category
import Prelude hiding (id, (.))

import MALens

import Domain
import Err

import qualified Data.Map as M
import Data.Maybe (fromJust)

-- Examples

validateCheckSum :: MALens (Int, [Int]) (M [Int])
validateCheckSum =
  ((introM @Int >>> introMLb) *** introM @[Int])
    >>> pairM
    >>> liftMissing (snapshot (\a -> assertEqL (sum a)) >>> second introM >>> pairM)
    >>> joinM
    >>> liftMissingDefault ((), []) deleteUnit

validateCheckSum' :: MALens (Int, [Int]) (M [Int])
validateCheckSum' =
  snapshot (\a -> introM >>> assertEqL (sum a))
    >>> second introM
    >>> pairM
    >>> liftMissingDefault ((), []) deleteUnit

-- >>> get validateCheckSum (10,[1,2,3,4])
-- >>> get validateCheckSum (9,[1,2,3,4])
-- Some [1,2,3,4]
-- None

-- >>> put validateCheckSum (10,[1,2,3,4]) (Some [1,2,3,4,5])
-- >>> put validateCheckSum (9,[1,2,3,4]) (Some [1,2,3,4,5])
-- Ok (15,[1,2,3,4,5])
-- Ok (15,[1,2,3,4,5])

-- >>> get validateCheckSum' (10,[1,2,3,4])
-- >>> get validateCheckSum' (9,[1,2,3,4])
-- Some [1,2,3,4]
-- None

-- >>> put validateCheckSum' (10,[1,2,3,4]) (Some [1,2,3,4,5])
-- >>> put validateCheckSum' (9,[1,2,3,4]) (Some [1,2,3,4,5])
-- Ok (15,[1,2,3,4,5])
-- Ok (15,[1,2,3,4,5])

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
    >>> cond nilCase r1 consCase r2 (null . snd)
  where
    nilCase :: MALens () (M (M.Map k a, [k]))
    nilCase = introM >>> dup >>> (emptyL *** nilL) >>> pairM

    r1 :: Maybe ((k, a), [(k, a)]) -> (M.Map k a, [k]) -> Err ()
    r1 _ _ = pure ()

    consCase :: MALens ((k, a), [(k, a)]) (M (M.Map k a, [k]))
    consCase =
      second (introM >>> toContainer)
        >>> assocToRightL
        >>> swapL
        >>> snapshot
          ( \k ->
              first introM
                >>> pairM
                >>> liftMissing (assocToLeftL >>> first (introM >>> insertL k) >>> second introM >>> pairM)
                >>> joinM
          )
        >>> second introM
        >>> pairM
        >>> liftMissing (assocToRightL >>> second (swapL >>> (introM *** introM) >>> pairM >>> consL) >>> first introM >>> pairM)
        >>> joinM

    r2 :: Maybe () -> (M.Map k a, [k]) -> Err ((k, a), [(k, a)])
    r2 _ (m, ks) =
      -- ks must be a non-empty list
      let res = [(kk, vv) | kk <- ks, let !vv = fromJust (M.lookup kk m)]
      in  pure (head res, tail res)

-- >>> get toContainer (Some [("a",0 :: Int),("b",1)])
-- Some (fromList [("a",0),("b",1)],["a","b"])

-- >>> put toContainer None $ Some (M.fromList [("a",0 :: Int),("b",1)],["a","b"])
-- Ok (Some [("a",0),("b",1)])

fromContainer ::
  forall k a.
  (Show k, Show a) =>
  (Ord k, Discrete k, Discrete a) =>
  MALens (M (M.Map k a, [k])) (M [(k, a)])
fromContainer =
  liftMissingDefault
    (M.empty, [])
    ( introM
        *** (introM >>> outListL)
        >>> swapL
        >>> pairM
        >>> dist
        >>> inspectL "1-cond"
        >>> cond lCase lRec rCase rRec null
    )
    >>> joinM
  where
    lCase :: MALens ((), M.Map k a) (M [(k, a)])
    lCase = introM *** (introM >>> assertEmptyL) >>> pairM >>> liftMissing deleteUnit >>> nilL

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
              (introM *** (introM >>> tryExtractL k))
                >>> swapL
                >>> pairM
                >>> dist
                >>> cond br1 rec1 (br2 k) (rec2 k) (notElem k . map fst)
          )
        >>> inspectL "after-ss"
        >>> second introM
        >>> swapL
        >>> snapshotMissing
          ( \case
              [] -> constL () >>> introM
              (k, _) : _ -> assertEqL k
          )
        >>> inspectL "after-erasing-k"
        >>> liftMissingDefault (None, []) (second introM >>> pairM >>> liftMissingDefault ((), []) deleteUnit)
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
        br1 = inspectL "br1" >>> introM >>> fromContainer

        rec1 :: Maybe ((a, M.Map k a), [k]) -> [(k, a)] -> Err (M.Map k a, [k])
        rec1 _ v = pure (M.fromList v, map fst v)

        br2 :: k -> MALens ((a, M.Map k a), [k]) (M [(k, a)])
        br2 k =
          assocToRightL
            >>> (introM *** (introM >>> fromContainer))
            >>> introUnit
            >>> first (introM >>> constL k >>> introM)
            >>> assocToLeftL
            >>> first pairM
            >>> pairM
            >>> consL

        rec2 :: k -> Maybe (M.Map k a, [k]) -> [(k, a)] -> Err ((a, M.Map k a), [k])
        rec2 k _ v = pure ((fromJust (Prelude.lookup k v), M.delete k (M.fromList v)), map fst v)

-- >>> get fromContainer $ Some (M.fromList [("a",0 :: Int),("b",1)],["a","b"])
-- Some [("a",0),("b",1)]

-- >>> get fromContainer $ Some (M.fromList [("b",1)], [])
-- None

-- >>> put fromContainer (Some (M.fromList [], [])) $ Some [("a",0),("b",1)]
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
              >>> cond
                (introM >>> l)
                recon1
                (first (introM >>> f) >>> second (introM >>> l) >>> pairM >>> insertL k)
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
testL = mapKeyBody (0 :: Int, "") (liftMissing (second introM >>> fstL))

--- >>> get testL (None, ["Alice","Bob","Cecil"])
-- (None,["Alice","Bob","Cecil"])

--- >>> get testL (Some $ M.fromList [("Alice",(0,"Hey")), ("Bob",(1,"Bbb")), ("Cecil",(2,"Cxx"))], ["Alice","Bob","Cecil"])
-- (Some (fromList [("Alice",0),("Bob",1),("Cecil",2)]),["Alice","Bob","Cecil"])

--- >>> put testL (Some $ M.fromList [("Alice",(0,"Hey")), ("Bob",(1,"Bbb")), ("Cecil",(2,"Cxx"))], ["Alice","Bob","Cecil"]) (Some $ M.fromList [], [])
-- Ok (Some (fromList []),[])

--- >>> put testL (Some $ M.fromList [("Alice",(0,"Hey")), ("Bob",(1,"Bbb")), ("Cecil",(2,"Cxx"))], ["Alice","Bob","Cecil"]) (Some $ M.fromList [("Bob",99), ("David",100)], ["Bob", "David"])
-- Ok (Some (fromList [("Bob",(99,"Bbb")),("David",(100,""))]),["Bob","David"])

mapKey ::
  (Ord k, Discrete a, Discrete k, Discrete b, Show k, Show b) =>
  a
  -> MALens (M a) (M b)
  -> MALens (M [(k, a)]) (M [(k, b)])
mapKey def f =
  toContainer
    >>> liftMissingDefault (M.empty, []) (first introM >>> mapKeyBody def f >>> second introM >>> pairM)
    >>> joinM
    >>> fromContainer

testMK :: (Ord k, Discrete k, Show k) => MALens (M [(k, (Int, String))]) (M [(k, Int)])
testMK = mapKey (0 :: Int, "") (liftMissing (second introM >>> fstL))

-- >>> get testMK (Some [("Alice",(0,"Hey")), ("Bob",(1,"Bbb")), ("Cecil",(2,"Cxx"))])
-- Some [("Alice",0),("Bob",1),("Cecil",2)]

-- >>> put testMK (Some [("Alice",(0,"Hey")), ("Bob",(1,"Bbb")), ("Cecil",(2,"Cxx"))]) (Some [("Bob",1),("David",2),("Alice",99)])
-- Ok (Some [("Bob",(1,"Bbb")),("David",(2,"")),("Alice",(99,"Hey"))])

-- >>> put testMK None (Some [("Bob",1),("David",2),("Alice",99)])
-- Ok (Some [("Bob",(1,"")),("David",(2,"")),("Alice",(99,""))])
