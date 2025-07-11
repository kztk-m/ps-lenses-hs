{-# LANGUAGE DerivingStrategies #-}
{-# OPTIONS_GHC -Wno-missing-export-lists #-}

module PSLens.Examples.Tasks where

import Control.Category ((>>>))
import qualified Data.IntMap as IM
import Data.Maybe
import Debug.Trace (trace)
import Domain
import Err (Err, err)
import PSLens

type ID = Int
type Date = Int

newtype Tasks = Tasks {getTasks :: IM.IntMap (Bool, String, Date)}
  deriving stock (Show, Eq)

instance Discrete Tasks

data PTasks = PTasks
  { addReq :: Tasks
  , delReq :: [(ID, (Bool, String, Date))]
  , completeReq :: [ID]
  , postponeReq :: IM.IntMap Date
  }
  deriving stock Show

data DT = ProperTasks Tasks | PartialTasks PTasks
  deriving stock Show

isPresentIn :: (Eq a) => IM.IntMap a -> IM.IntMap a -> Bool
isPresentIn = IM.isSubmapOf

isNotPresentIn :: (Eq a) => [(ID, a)] -> IM.IntMap a -> Bool
isNotPresentIn kvs m =
  flip all kvs $ \(k, v) -> case IM.lookup k m of
    Nothing -> True
    Just v' -> v /= v'

instance Eq PTasks where
  a == b = (a <=% b) && (b <=% a)

instance POrd PTasks where
  PTasks a d c p <=% PTasks a' d' c' p' =
    getTasks a `isPresentIn` getTasks a'
      && all (\b -> b `elem` d') d
      && all (\i -> i `elem` c') c
      && IM.isSubmapOfBy (<=) p p'

allCompleted :: [ID] -> Tasks -> Bool
allCompleted c t = flip all c $ \k -> case IM.lookup k (getTasks t) of
  Nothing -> True
  Just (b, _, _) -> not b

allPostponed :: IM.IntMap a -> Tasks -> Bool
allPostponed p t = flip all (IM.toList p) $ \(k, _) -> case IM.lookup k (getTasks t) of
  Nothing -> True
  Just (_, _, d) -> d /= 0

isImplementedBy :: PTasks -> Tasks -> Bool
isImplementedBy (PTasks a d c p) t =
  getTasks a `isPresentIn` getTasks t
    && d `isNotPresentIn` getTasks t
    && allCompleted c t
    && allPostponed p t

complete :: [ID] -> IM.IntMap (Bool, a, b) -> IM.IntMap (Bool, a, b)
complete cs m = foldr (IM.adjust (\(_, n, d) -> (True, n, d))) m cs

postpone :: IM.IntMap Date -> IM.IntMap (c, a, Date) -> IM.IntMap (c, a, Date)
postpone ps m =
  foldr
    ( \(k, dd) ->
        IM.adjust (\(c, n, d) -> if d == 0 then (c, n, dd) else (c, n, d)) k
    )
    m
    $ IM.toList ps

delTasks :: (Eq a) => IM.IntMap a -> [(ID, a)] -> IM.IntMap a
delTasks t d =
  IM.differenceWith f t (IM.fromListWith (++) $ map (\(k, v) -> (k, [v])) d)
  where
    f a as = if a `elem` as then Nothing else Just a

applyUpd :: PTasks -> Tasks -> Err Tasks
applyUpd (PTasks (Tasks a) d c p) (Tasks t) =
  pure $ Tasks $ IM.union a (postpone p (complete c (t `delTasks'` d)))
  where
    delTasks' x y =
      let r = delTasks x y
      in  trace (show x ++ " \\ " ++ show y ++ " = " <> show r) r

instance Eq DT where
  a == b = (a <=% b) && (b <=% a)

instance POrd DT where
  ProperTasks t <=% ProperTasks t' = t == t'
  PartialTasks d <=% ProperTasks t = d `isImplementedBy` t
  PartialTasks d <=% PartialTasks d' = d <=% d'
  _ <=% _ = False

instance Lub PTasks where
  lub (PTasks (Tasks a) d c p) (PTasks (Tasks a') d' c' p')
    | any (\k -> IM.member k a') (IM.keys a) = err "Adding tasks with same ID"
    | any (\(k, _) -> IM.member k $ getTasks aa) dd = err "Addition/deletion conflicts"
    | otherwise = pure $ PTasks aa dd cc pp
    where
      aa = Tasks $ IM.union a a'
      dd = d ++ d'
      cc = c ++ c'
      pp = IM.unionWith max p p'

instance Lub DT where
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

instance LowerBounded PTasks where
  least = PTasks (Tasks IM.empty) [] [] IM.empty

instance LowerBounded DT where
  least = PartialTasks least

initTask :: PSLens Tasks DT
initTask = PSLens (pure . ProperTasks) p
  where
    p _ (ProperTasks t) = pure t
    p t (PartialTasks d) = applyUpd d t

isOngoing :: (Bool, b, c) -> Bool
isOngoing (b, _, _) = not b

isDueToday :: (Eq a1, Num a1) => (a2, b, a1) -> Bool
isDueToday (_, _, d) = d == 0

-- For simplicity, we use the same datatypes
type DTOG = DT
type DTDT = DT

filterOG :: PSLens DT DT
filterOG = PSLens g pt
  where
    g (ProperTasks (Tasks t)) = pure $ ProperTasks $ Tasks $ IM.filter isOngoing t
    g (PartialTasks (PTasks (Tasks a) d c _)) =
      pure $
        PartialTasks $
          PTasks
            (Tasks $ IM.filter isOngoing a)
            (filter (isOngoing . snd) d)
            c
            IM.empty

    goodT x = IM.null (IM.filter (not . isOngoing) x)
    goodT' x = all (isOngoing . snd) x

    pt (ProperTasks (Tasks t)) (ProperTasks (Tasks t'))
      | goodT t' =
          pure $ ProperTasks $ Tasks $ t' `IM.union` IM.filter (not . isOngoing) t
    pt _ (PartialTasks (PTasks a d c p))
      | goodT (getTasks a) && goodT' d =
          if IM.null p
            then pure $ PartialTasks $ PTasks a d c IM.empty
            else err "put filterOG: p must be empty"
    pt _ _ = err "put filterOG: pattern failure"

filterDT :: PSLens DT DT
filterDT = PSLens g pt
  where
    g (ProperTasks (Tasks t)) = pure $ ProperTasks $ Tasks $ IM.filter isDueToday t
    g (PartialTasks (PTasks (Tasks a) d c _)) =
      pure $
        PartialTasks $
          PTasks
            (Tasks $ IM.filter isDueToday a)
            (filter (isDueToday . snd) d)
            c
            IM.empty

    goodT x = IM.null (IM.filter (not . isDueToday) x)
    goodT' x = all (isDueToday . snd) x

    pt (ProperTasks (Tasks t)) (ProperTasks (Tasks t'))
      | goodT t' =
          pure $ ProperTasks $ Tasks $ t' `IM.union` IM.filter (not . isDueToday) t
    pt _ (PartialTasks (PTasks a d c p))
      | goodT (getTasks a) && goodT' d =
          if null c
            then pure $ PartialTasks $ PTasks a d [] p
            else err "put filterDT: c must be empty"
    pt _ _ = err "put filterDT: pattern failure"

lTasks :: PSLens Tasks (DT, DT)
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

dOG :: DT
dOG = PartialTasks $ PTasks a [] [] IM.empty
  where
    a = Tasks $ IM.fromList [(4, (False, "Buy egg", 0))]

-- >>> let res = put lTasks originalTasks (dOG , least)
-- >>> res
-- >>> get lTasks =<< res
-- Ok (Tasks {getTasks = fromList [(1,(False,"Buy milk",1)),(2,(True,"Walk dog",0)),(3,(False,"Jog",0)),(4,(False,"Buy egg",0))]})
-- Ok (ProperTasks (Tasks {getTasks = fromList [(1,(False,"Buy milk",1)),(3,(False,"Jog",0)),(4,(False,"Buy egg",0))]}),ProperTasks (Tasks {getTasks = fromList [(2,(True,"Walk dog",0)),(3,(False,"Jog",0)),(4,(False,"Buy egg",0))]}))

dDT :: DT
dDT = PartialTasks $ PTasks a d [] IM.empty
  where
    a = Tasks $ IM.fromList [(3, (False, "Stretch", 0))]
    d = [(2, (True, "Walk dog", 0))]

-- >>> let res = put lTasks originalTasks (dOG, dDT)
-- >>> res
-- >>> get lTasks =<< res
-- Ok (Tasks {getTasks = fromList [(1,(False,"Buy milk",1)),(3,(False,"Stretch",0)),(4,(False,"Buy egg",0))]})
-- Ok (ProperTasks (Tasks {getTasks = fromList [(1,(False,"Buy milk",1)),(3,(False,"Stretch",0)),(4,(False,"Buy egg",0))]}),ProperTasks (Tasks {getTasks = fromList [(3,(False,"Stretch",0)),(4,(False,"Buy egg",0))]}))

dOGc :: DT
dOGc = PartialTasks $ PTasks (Tasks IM.empty) d [3] IM.empty
  where
    d = [(1, (False, "Buy milk", 1))]

-- >>> put lTasks originalTasks (dOGc, least)
-- Ok (Tasks {getTasks = fromList [(2,(True,"Walk dog",0)),(3,(True,"Jog",0))]})

dDTp :: DT
dDTp = PartialTasks $ PTasks (Tasks IM.empty) d [] (IM.fromList [(2, 3), (3, 3)])
  where
    d = [(3, fromJust $ IM.lookup 3 $ getTasks originalTasks)]

-- >>> put (dup >>> (filterOG *** filterDT)) (ProperTasks originalTasks) (dOGc , dDTp)
-- Ok (PartialTasks (PTasks {addReq = Tasks {getTasks = fromList []}, delReq = [(1,(False,"Buy milk",1)),(3,(False,"Jog",0))], completeReq = [3], postponeReq = fromList [(2,3),(3,3)]}))

-- >>> put lTasks originalTasks (dOGc, dDTp)
-- Ok (Tasks {getTasks = fromList [(2,(True,"Walk dog",3))]})

-- data CompletionAction = CAComplete | CANoop

-- extractC :: ID -> PSLens DT CompletionAction
-- extractC k = PSLens get' put'
--   where
--     get' (ProperTasks (Tasks t)) =
--       case IM.lookup k t of
--         Nothing ->
--           -- as a completion can be implemented by a deletion, we regard that here that completion action has been executed
--           pure CAComplete
--         Just (b, _, _) ->
--           if b
--             then pure CAComplete -- cannot happen, when it used after filterOG
--             else pure CANoop
--     get' (PartialTasks (PTasks _ _ c _)) =
--       -- In partially-specified states, completion is distinguished from other update requests
--       if k `elem` c
--         then pure CAComplete
--         else pure CANoop

--     put' _ CANoop = pure least
--     put' _ CAComplete = pure $ PartialTasks $ PTasks (Tasks IM.empty) [] [k] IM.empty

-- -- Let's check it's well-behavedness of `extractC`.
-- --
-- -- Suppose that get s = v and v' <= v. We will show put s v' <= s. We safely
-- -- assume v' = v by the monotonicity of put in the second argument.
-- --
-- --   * Case: v is CANoop. Obvious.
-- --   * Case: v is CAComplete: we need to check that get s = CACompele must imply
-- --     put s v <= s. This in fact holds.
-- --
-- -- Suppose that put s v = s' and s' <= s''. We will show v <= get s'. We safely
-- -- assume s'' = s' by the monotonicity of get.
-- --
-- --   * Case: v is CANoop. Then, s' = least and the componenets of s' is all empty. Thus, get s' = CANoop.
-- --   * Case: v is CAComplete. This time, we also have get s' = CANoop.
