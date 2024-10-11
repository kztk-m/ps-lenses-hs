{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}

module MALens.Examples.MapKeyT where

import Control.Category
import Prelude hiding (id, (.))

import MALens

import qualified Data.List
import qualified Data.Map as M
import Data.Maybe (fromJust)
import Debug.Trace (trace)
import Domain
import Err
import GHC.Stack (HasCallStack, callStack, prettyCallStack)
import MALens.Examples.List (mapL, sequenceL)
import MALensTH (arrP)

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
assertEmptyG :: (HasCallStack) => Galois (M.Map k a) ()
assertEmptyG = Galois f g
  where
    f m
      | M.null m = pure ()
      | otherwise = err $ "checkEmptyG: expects the empty\n" ++ prettyCallStack callStack
    g () = pure M.empty

assertEmptyL :: (Discrete k) => MALens (M (M.Map k v)) (M ())
assertEmptyL = liftGalois (invert assertEmptyG)

-- This is ok because
-- (1) null check is monotone
-- (2) M.empty is the smallest element for which null returns true
assertEmptyL' :: (Discrete k) => MALens (M.Map k v) (M ())
assertEmptyL' = MALens g p
  where
    g m
      | M.null m = Some ()
      | otherwise = None

    p _ (Some _) = pure M.empty
    p s None = pure s

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
  (Ord k, Discrete k, Templatable k, Templatable a, Show k, Show a) =>
  MALens (M [(k, a)]) (M (M.Map k a, [k]))
toContainer =
  outListL
    >>> cond nilCase r1 consCase r2 (EnsureMonotone $ null . snd)
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
                >>> liftMissing (assocToLeftL >>> first (introM >>> insertL k) >>> second introMd >>> pairM)
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

-- >>> let s = (M.fromList [("a", 1), ("b",2)], ["a","b"])
-- >>> get fromContainer (Some s)
-- Some [("a",1.0),("b",2.0)]
-- >>> put fromContainer (Some s) (Some [("b", 3)])
-- Ok (Some (fromList [("a",1.0),("b",3.0)],["b"]))

fromContainer ::
  forall k a.
  (Show k, Show a, Templatable a, Templatable k) =>
  (Ord k, Discrete k) =>
  MALens (M (M.Map k a, [k])) (M [(k, a)])
fromContainer =
  liftMissingDefault
    (M.empty, [])
    ( introM
        *** (introM >>> outListL)
        >>> swapL
        >>> pairM
        >>> dist
        -- >>> inspectL "1-cond"
        >>> cond lCase lRec rCase rRec (EnsureMonotone null)
        -- `withInspect` "fc-cond"
    )
    >>> joinM
  where
    lCase :: MALens ((), M.Map k a) (M [(k, a)])
    lCase =
      introM *** (introM >>> assertEmptyL)
        >>> pairM
        >>> letM ((), ()) (deleteUnit >>> introM)
        >>> nilL

    lRec :: Maybe ((k, [k]), M.Map k a) -> [(k, a)] -> Err ((), M.Map k a)
    lRec _ _ = trace "!!!lRec!!!" $ pure ((), M.empty)
    -- lRec (Just (_, m)) _ = pure ((), m)
    -- lRec Nothing vs = pure ((), M.fromList vs)

    rRec :: Maybe ((), M.Map k a) -> [(k, a)] -> Err ((k, [k]), M.Map k a)
    rRec _ vs@((k, _) : vs') = trace "!!!rRec!!!" $ pure ((k, map fst vs'), M.fromList vs)
    -- rRec (Just (_, m)) ((k, _) : _) = pure ((k, []), m)
    -- rRec _ vs@((k, _) : _) = pure ((k, []), M.fromList vs)
    -- rRec Nothing vs@((k, _) : _) = pure ((k, []), M.fromList vs)
    rRec _ _ = err "Cannot happen?"

    rCase :: MALens ((k, [k]), M.Map k a) (M [(k, a)])
    rCase =
      $(arrP [|\((k, ks), m) -> ((ks, m), k)|])
        >>> snapshot
          ( \k ->
              (introM *** (introM >>> tryExtractL k))
                >>> swapL
                >>> pairM
                >>> dist
                -- Either (M.Map k a, [k]) ((a, M.Map k a), [k])
                >>> cond
                  br1
                  (const $ const $ err "Cannot happen")
                  (br2 k)
                  (rec2 k)
                  (EnsureMonotone $ notElem k . map fst)
                  -- `withInspect` ("rCase-cond[" ++ show k ++ "]")
                  -- M [(k,a)]
          )
        -- (M [(k, a)], k)
        -- Goal: eliminate k using the fact that the first element of the list must have the form of (k,_)
        >>> second (introM >>> introM)
        >>> swapL
        >>> pairM
        -- M (M k, [(k,a)])
        >>> letM
          (least, [])
          ( snapshotO
              ( OrderInd $ \case
                  [] -> eraseL >>> introM
                  ((k', _) : _) -> assertEqL k'
              )
              >>> second introM
              >>> pairM
          )
        >>> letM ((), []) (deleteUnit >>> introM)
      where
        br1 :: MALens (M.Map k a, [k]) (M [(k, a)])
        br1 =
          inspectL "br1"
            -- >>> introM >>> fromContainer
            >>> eraseL
            >>> introM
            >>> nilL

        br2 :: k -> MALens ((a, M.Map k a), [k]) (M [(k, a)])
        br2 k =
          $(arrP [|\((a, m), ks) -> (a, (m, ks))|])
            >>> second (introM >>> fromContainer)
            >>> first (introUnit >>> (introM >>> constLunit k) *** introM >>> pairM)
            >>> pairM
            >>> consL

        rec2 :: k -> Maybe (M.Map k a, [k]) -> [(k, a)] -> Err ((a, M.Map k a), [k])
        rec2 k _ v = trace "!!!rec2!!!" $ pure ((fromJust $ M.lookup k m, m'), Data.List.delete k $ map fst v)
          where
            m' = M.delete k m
            m = M.fromList v

mapKeyBody ::
  forall k a b.
  (Ord k, Discrete k, Templatable a, Templatable b, Show k, Show b) =>
  a
  -> MALens a b
  -> MALens (M (M.Map k a, [k])) (M (M.Map k b, [k]))
mapKeyBody def f =
  letM (M.empty, []) $
    snapshot
      ( foldr
          ( \k l ->
              introM
                >>> tryExtractL k
                >>> cond
                  undefined
                  recon1
                  (first (f >>> introM) >>> second l >>> pairM >>> insertL k)
                  recon2
                  (EnsureMonotone $ not . M.member k)
          )
          (introM >>> assertEmptyL >>> emptyL)
      )
      >>> second introMd
      >>> pairM
  where
    recon1 :: Maybe (a, M.Map k a) -> M.Map k b -> Err (M.Map k a)
    recon1 _ _ = err "Never called."
    recon2 :: Maybe (M.Map k a) -> M.Map k b -> Err (a, M.Map k a)
    recon2 (Just m) _ = pure (def, m)
    recon2 Nothing _ = err "recon2: expects the source value"

mapKey ::
  (Ord k, Discrete k, Templatable k, Templatable a, Templatable b, Show k, Show b, Show a) =>
  a
  -> MALens a b
  -> MALens (M [(k, a)]) (M [(k, b)])
mapKey def f =
  toContainer
    >>> mapKeyBody def f
    >>> fromContainer

nameScoresKey :: MALens [(String, String, Int)] (M [(String, Int)])
nameScoresKey =
  mapL ("", "", 0) $(arrP [|\(x, y, z) -> (x, (y, z))|])
    >>> introM
    >>> mapKey ("", 0) sndL'

-- >>> let s = [("Brown", "CS", 90), ("Smith", "Math", 88), ("Johnson", "CS", 65)]
-- >>> get nameScoresKey s
-- >>> put nameScoresKey s (Some [("Smith", 88), ("Brown", 90)])
-- >>> put nameScoresKey s (Some [("Smith", 80), ("Brown", 99)])
-- >>> put nameScoresKey s (Some [("Johnson", 80), ("Brown", 99)])
-- >>> put nameScoresKey s (Some [("Johnson", 80), ("Brown", 99), ("Willson", 85)])
-- Some [("Brown",90),("Smith",88),("Johnson",65)]
-- Ok [("Smith","Math",88),("Brown","CS",90)]
-- Ok [("Smith","Math",80),("Brown","CS",99)]
-- Ok [("Johnson","CS",80),("Brown","CS",99)]
-- Ok [("Johnson","CS",80),("Brown","CS",99),("Willson","",85)]
