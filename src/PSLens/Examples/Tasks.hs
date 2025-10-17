{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-missing-export-lists #-}

module PSLens.Examples.Tasks where

import Control.Category ((>>>))
import Control.Monad (forM_)
import qualified Data.IntMap.Strict as IM
import qualified Data.IntSet as IS
import Data.List (sort)
import Domain
import Err (Err, err, guardErr)
import PSLens

type ID = Int
type Date = Int

newtype Tasks = Tasks {getTasks :: IM.IntMap (Bool, String, Date)}
  deriving stock (Show, Eq)

instance Discrete Tasks

printTasks :: Tasks -> IO ()
printTasks (Tasks m) =
  forM_ ks $ \(is, cs, ns, ps) -> do
    putStr (fillSp is mi)
    putStr "  "
    putStr (fillSp cs mc)
    putStr "  "
    putStr (fillSp ns mn)
    putStr "  "
    putStr (fillSp ps mp)
    putStr "\n"
  where
    ks = map (\(i, (c, n, p)) -> (show i, show c, n, "+" ++ show p)) $ IM.toList m
    mi = foldr (max . (\(i, _, _, _) -> length i)) 0 ks
    mc = foldr (max . (\(_, c, _, _) -> length c)) 0 ks
    mn = foldr (max . (\(_, _, n, _) -> length n)) 0 ks
    mp = foldr (max . (\(_, _, _, p) -> length p)) 0 ks

    fillSp s n = take n $ s ++ replicate n ' '

data P = N | OnGoing | DueToday

data CompReq (a :: P) where
  CN :: CompReq N
  COnGoing :: Tasks -> CompReq OnGoing
  CDueToday :: CompReq DueToday
deriving stock instance Show (CompReq a)

data PostReq (a :: P) where
  PN :: PostReq N
  POnGoing :: PostReq OnGoing
  PDueToday :: Tasks -> PostReq DueToday

deriving stock instance Show (PostReq a)

data PTasks a = PTasks
  { addReq :: Tasks
  , delReq :: [ID]
  , compReq :: CompReq a
  , postReq :: PostReq a
  }
  deriving stock Show

printPTasks :: PTasks a -> IO ()
printPTasks (PTasks aa dd cc pp) = do
  forM_ ks $ \(is, cs, ns, ps, ms) -> do
    putStr (fillSp is mi)
    putStr "  "
    putStr (fillSp cs mc)
    putStr "  "
    putStr (fillSp ns mn)
    putStr "  "
    putStr (fillSp ps mp)
    putStr "  "
    putStr ms
    putStr "\n"
  where
    renderTask m (i, (c, n, p)) = (show i, show c, n, "+" ++ show p, m)
    a' = map (renderTask "(+)") $ IM.toList $ getTasks aa
    d' = map (\i -> (show i, "", "", "", "(-)")) dd
    c' = case cc of
      CN -> []
      COnGoing t -> map (renderTask "(C)") $ IM.toList $ getTasks t
      CDueToday -> []
    p' = case pp of
      PN -> []
      POnGoing -> []
      PDueToday t -> map (renderTask "(P)") $ IM.toList $ getTasks t
    ks = sort $ a' ++ d' ++ c' ++ p'

    mi = foldr (max . (\(i, _, _, _, _) -> length i)) 0 ks
    mc = foldr (max . (\(_, c, _, _, _) -> length c)) 0 ks
    mn = foldr (max . (\(_, _, n, _, _) -> length n)) 0 ks
    mp = foldr (max . (\(_, _, _, p, _) -> length p)) 0 ks

    fillSp s n = take n $ s ++ replicate n ' '

data DT a = ProperTasks Tasks | PartialTasks (PTasks a)
  deriving stock Show

printDT :: DT a -> IO ()
printDT (ProperTasks t) = printTasks t
printDT (PartialTasks t) = printPTasks t

printDTPair :: (DT a, DT b) -> IO ()
printDTPair (a, b) = do
  printDT a
  putStrLn ""
  printDT b

isPresentIn :: (Eq a) => IM.IntMap a -> IM.IntMap a -> Bool
isPresentIn = IM.isSubmapOf

isNotPresentIn :: [ID] -> IM.IntMap a -> Bool
isNotPresentIn ks m = all (\i -> not $ IM.member i m) ks

isImplementedBy :: PTasks a -> Tasks -> Bool
isImplementedBy (PTasks a d c p) t =
  getTasks a `isPresentIn` getTasks t
    && (d ++ cIDs c ++ pIDs p) `isNotPresentIn` getTasks t

applyUpd :: PTasks N -> Tasks -> Err Tasks
applyUpd (PTasks (Tasks a) d _ _) (Tasks t) =
  pure $ Tasks $ IM.union a (t `delTasks` d)
  where
    delTasks = foldr IM.delete

tIDs :: Tasks -> [ID]
tIDs (Tasks t) = IM.keys t

cIDs :: CompReq p -> [ID]
cIDs (COnGoing (Tasks t)) = IM.keys t
cIDs _ = []

pIDs :: PostReq p -> [ID]
pIDs (PDueToday (Tasks t)) = IM.keys t
pIDs _ = []

disjointIDs :: [ID] -> [ID] -> Bool
disjointIDs is = not . any (`elem` is)

tryMergeTasks :: Tasks -> Tasks -> Maybe Tasks
tryMergeTasks (Tasks t1) (Tasks t2) =
  if IS.foldr (\k -> (&&) (IM.lookup k t1 == IM.lookup k t2)) True commonKeys
    then
      Just $ Tasks $ IM.union t1 t2
    else
      Nothing
  where
    commonKeys = IS.intersection (IM.keysSet t1) (IM.keysSet t2)

tryMergeCompReq :: CompReq a -> CompReq a -> Maybe (CompReq a)
tryMergeCompReq (COnGoing t1) (COnGoing t2) = fmap COnGoing (tryMergeTasks t1 t2)
tryMergeCompReq t _ = Just t

tryMergePostReq :: PostReq a -> PostReq a -> Maybe (PostReq a)
tryMergePostReq (PDueToday t1) (PDueToday t2) = fmap PDueToday (tryMergeTasks t1 t2)
tryMergePostReq t _ = Just t

instance Lub (PTasks a) where
  lub (PTasks a d c p) (PTasks a' d' c' p') = do
    aa <- maybe (err "Competing updates in addition requests") pure $ tryMergeTasks a a'
    cc <- maybe (err "Competing updates in completion requests") pure $ tryMergeCompReq c c'
    pp <- maybe (err "Competing updates in postponing requests") pure $ tryMergePostReq p p'
    if
      | not $ disjointIDs (tIDs aa) dd -> err "Addition/deletion conflicts"
      | not $ disjointIDs (tIDs aa) (cIDs cc) -> err "Addition/completion conflicts"
      | not $ disjointIDs (tIDs aa) (pIDs pp) -> err "Addition/postponing conflicts"
      | not $ disjointIDs dd (cIDs cc) -> err "Deletion/completion conflicts"
      | not $ disjointIDs dd (pIDs pp) -> err "Deletion/completion conflicts"
      -- \| not $ disjointIDs (tIDs cc) (tIDs pp) -> err "Cannot happen"
      | otherwise -> pure $ PTasks aa dd cc pp
    where
      dd = d ++ d'

instance Lub (DT a) where
  lub (PartialTasks d) (PartialTasks d') = PartialTasks <$> lub d d'
  lub (PartialTasks d) (ProperTasks t)
    | d `isImplementedBy` t = pure $ ProperTasks t
    | otherwise = err "no lub for incomparable partial state and proper state"
  lub (ProperTasks t) (PartialTasks d)
    | d `isImplementedBy` t = pure $ ProperTasks t
    | otherwise = err "no lub for incomparable partial state and proper state"
  lub (ProperTasks t) (ProperTasks t')
    | t == t' = pure $ ProperTasks t
    | otherwise = err "no lub for two different proper states"

instance LowerBounded (PTasks OnGoing) where
  least = PTasks (Tasks IM.empty) [] (COnGoing $ Tasks IM.empty) POnGoing

instance LowerBounded (PTasks DueToday) where
  least = PTasks (Tasks IM.empty) [] CDueToday (PDueToday $ Tasks IM.empty)

instance (LowerBounded (PTasks p)) => LowerBounded (DT p) where
  least = PartialTasks least

initTask :: PSLens Tasks (DT N)
initTask = PSLens (pure . ProperTasks) p
  where
    p _ (ProperTasks t) = pure t
    p t (PartialTasks d) = applyUpd d t

isOngoing :: (Bool, b, c) -> Bool
isOngoing (b, _, _) = not b

isDueToday :: (Eq a1, Num a1) => (a2, b, a1) -> Bool
isDueToday (_, _, d) = d == 0

allOnGoing :: Tasks -> Bool
allOnGoing = IM.foldr ((&&) . isOngoing) True . getTasks

allComplete :: Tasks -> Bool
allComplete = IM.foldr ((&&) . not . isOngoing) True . getTasks

allDueToday :: Tasks -> Bool
allDueToday = IM.foldr ((&&) . isDueToday) True . getTasks

allDueLater :: Tasks -> Bool
allDueLater = IM.foldr ((&&) . not . isDueToday) True . getTasks

filterOG :: PSLens (DT N) (DT OnGoing)
filterOG = PSLens g pt
  where
    g (ProperTasks (Tasks t)) = pure $ ProperTasks $ Tasks $ IM.filter isOngoing t
    g (PartialTasks (PTasks (Tasks a) d _ _)) =
      pure $ PartialTasks $ PTasks (Tasks a') d (COnGoing $ Tasks c') POnGoing
      where
        (a', c') = IM.partition isOngoing a

    pt :: DT N -> DT OnGoing -> Err (DT N)
    pt (ProperTasks (Tasks t)) (ProperTasks (Tasks t'))
      | allOnGoing (Tasks t') =
          pure $ ProperTasks $ Tasks $ t' `IM.union` IM.filter (not . isOngoing) t
    pt _ (PartialTasks (PTasks a d (COnGoing c) _)) = do
      guardErr "Addition requests must be all on-going" $ allOnGoing a
      guardErr "Completion requests must be all complete" $ allComplete c
      guardErr "Addition/completion requests must be disjoint" $ disjointIDs (tIDs a) (tIDs c)
      pure $ PartialTasks $ PTasks (Tasks $ IM.union (getTasks a) (getTasks c)) d CN PN
    pt _ _ = err "put filterOG: pattern failure"

filterDT :: PSLens (DT N) (DT DueToday)
filterDT = PSLens g pt
  where
    g (ProperTasks (Tasks t)) = pure $ ProperTasks $ Tasks $ IM.filter isDueToday t
    g (PartialTasks (PTasks (Tasks a) d _ _)) =
      pure $ PartialTasks $ PTasks (Tasks a') d CDueToday (PDueToday $ Tasks p')
      where
        (a', p') = IM.partition isDueToday a

    pt :: DT N -> DT DueToday -> Err (DT N)
    pt (ProperTasks (Tasks t)) (ProperTasks (Tasks t'))
      | allDueToday (Tasks t') =
          pure $ ProperTasks $ Tasks $ t' `IM.union` IM.filter (not . isDueToday) t
    pt _ (PartialTasks (PTasks a d _ (PDueToday p))) = do
      guardErr "Addition requests must be all due today" $ allDueToday a
      guardErr "Postponing requests must be all due later" $ allDueLater p
      guardErr "Addition/postponing requests must be disjoint" $ disjointIDs (tIDs a) (tIDs p)
      pure $ PartialTasks $ PTasks (Tasks (IM.union (getTasks a) (getTasks p))) d CN PN
    pt _ _ = err "put filterDT: pattern failure"

lTasks :: PSLens Tasks (DT OnGoing, DT DueToday)
lTasks = initTask >>> dup >>> (filterOG *** filterDT)

originalTasks :: Tasks
originalTasks =
  Tasks $
    IM.fromList
      [ (1, (False, "Buy milk", 1))
      , (2, (True, "Walk dog", 0))
      , (3, (False, "Jog", 0))
      ]

-- >>> get lTasks originalTasks
-- Ok (ProperTasks (Tasks {getTasks = fromList [(1,(False,"Buy milk",1)),(3,(False,"Jog",0))]}),ProperTasks (Tasks {getTasks = fromList [(2,(True,"Walk dog",0)),(3,(False,"Jog",0))]}))

dOG :: DT OnGoing
dOG = PartialTasks $ PTasks a [] (COnGoing $ Tasks IM.empty) POnGoing
  where
    a = Tasks $ IM.fromList [(4, (False, "Buy egg", 0))]

-- >>> let res = put lTasks originalTasks (dOG , least)
-- >>> res
-- >>> get lTasks =<< res
-- Ok (Tasks {getTasks = fromList [(1,(False,"Buy milk",1)),(2,(True,"Walk dog",0)),(3,(False,"Jog",0)),(4,(False,"Buy egg",0))]})
-- Ok (ProperTasks (Tasks {getTasks = fromList [(1,(False,"Buy milk",1)),(3,(False,"Jog",0)),(4,(False,"Buy egg",0))]}),ProperTasks (Tasks {getTasks = fromList [(2,(True,"Walk dog",0)),(3,(False,"Jog",0)),(4,(False,"Buy egg",0))]}))

dDT :: DT DueToday
dDT = PartialTasks $ PTasks a d CDueToday (PDueToday $ Tasks IM.empty)
  where
    a = Tasks $ IM.fromList [(3, (False, "Stretch", 0))]
    d = [2]

-- >>> let res = put lTasks originalTasks (dOG, dDT)
-- >>> res
-- >>> get lTasks =<< res
-- Ok (Tasks {getTasks = fromList [(1,(False,"Buy milk",1)),(3,(False,"Stretch",0)),(4,(False,"Buy egg",0))]})
-- Ok (ProperTasks (Tasks {getTasks = fromList [(1,(False,"Buy milk",1)),(3,(False,"Stretch",0)),(4,(False,"Buy egg",0))]}),ProperTasks (Tasks {getTasks = fromList [(3,(False,"Stretch",0)),(4,(False,"Buy egg",0))]}))

dOGc :: DT OnGoing
dOGc = PartialTasks $ PTasks (Tasks IM.empty) d (COnGoing c) POnGoing
  where
    d = [1]
    c = Tasks $ IM.fromList [(3, (True, "Stretch", 0))]

-- >>> put lTasks originalTasks (dOGc, least)
-- Ok (Tasks {getTasks = fromList [(2,(True,"Walk dog",0)),(3,(True,"Stretch",0))]})

-- A conflicting update
dDTpConflict :: DT DueToday
dDTpConflict = PartialTasks $ PTasks (Tasks IM.empty) d CDueToday (PDueToday $ Tasks p)
  where
    d = [3] -- d = [(3, fromJust $ IM.lookup 3 $ getTasks originalTasks)]
    p = IM.map (\(c, n, _) -> (c, n, 3)) $ IM.restrictKeys (getTasks originalTasks) (IS.fromList [2, 3])

-- >>> put lTasks originalTasks (dOGc, dDTpConflict)
-- Err ["Competing updates in addition requests"]

-- Another conflicting update
dDTpConflictWithdOGc :: DT DueToday
dDTpConflictWithdOGc = PartialTasks $ PTasks (Tasks IM.empty) d CDueToday (PDueToday $ Tasks $ IM.empty)
  where
    d = [3] -- d = [(3, fromJust $ IM.lookup 3 $ getTasks originalTasks)]

-- >>> put lTasks originalTasks (dOGc, dDTpConflict2)
-- Err ["Addition/deletion conflicts"]
