{-# LANGUAGE TemplateHaskell #-}

module MALensTH (arrP) where

import qualified Language.Haskell.TH as TH

import Data.Maybe (isJust)
import MALens

data SimplePat
  = SVarP TH.Name
  | STupP [SimplePat]
  | SSigP SimplePat TH.Type
  | SConP TH.Name [SimplePat]

asPat :: (Applicative m) => SimplePat -> m TH.Pat
asPat = pure . go
  where
    go (SVarP x) = TH.VarP x
    go (STupP ps) = TH.TildeP . TH.TupP $ map go ps
    go (SSigP p t) = TH.SigP (go p) t
    go (SConP cn ps) = TH.ConP cn [] $ map go ps

asExp :: (Applicative m) => SimplePat -> m TH.Exp
asExp = pure . go
  where
    go (SVarP x) = TH.VarE x
    go (STupP ps) = TH.TupE $ map (Just . go) ps
    go (SSigP p t) = TH.SigE (go p) t
    go (SConP cn ps) = foldl TH.AppE (TH.ConE cn) $ map go ps

{- | This function converts a simple lambda \p -> e where
e and e consist of tuples and variables into lenses.
TODO: use 'least' in put when a variable does not appear in p2.
-}
arrP :: TH.Q TH.Exp -> TH.Q TH.Exp
arrP me = do
  (p1, p2) <- extractPatAndBody =<< me
  [|MALens (\ $(asPat p1) -> $(asExp p2)) (const $ \ $(asPat p2) -> pure $(asExp p1))|]

extractPatAndBody :: TH.Exp -> TH.Q (SimplePat, SimplePat)
extractPatAndBody (TH.LamE [p] e) = (,) <$> p2sp p <*> e2sp e
extractPatAndBody _ = fail "expected an expression of the form of '\\p -> e'"

-- This function succeeds only when a given constructor is not the unique constructor of its type to form.
checkSingleConstructor :: TH.Name -> TH.Q ()
checkSingleConstructor n = do
  i <- TH.reify n
  case i of
    TH.DataConI _ t _ -> do
      res <- extractResultTypeName t
      case res of
        SomeTuple -> pure ()
        TypeName tn -> do
          j <- TH.reify tn
          case j of
            TH.TyConI (TH.DataD _ _ _ _ [_] _) -> pure ()
            TH.TyConI (TH.DataD{}) -> fail $ show (TH.ppr n) ++ " is not a single constructor of type (constructor) " ++ show (TH.ppr tn)
            TH.TyConI (TH.NewtypeD{}) -> pure ()
            _ -> fail "Unsupported form of declaration"
    _ -> fail "Not a data constructor"

data TN = TypeName TH.Name | SomeTuple

-- Extract a type constructor of the return type
extractResultTypeName :: TH.Type -> TH.Q TN
extractResultTypeName (TH.ForallT _ _ t) = extractResultTypeName t
extractResultTypeName (TH.AppT (TH.AppT TH.ArrowT _) t2) = extractResultTypeName t2
extractResultTypeName t | Just tn <- checkConAppForm t = pure tn
extractResultTypeName t = fail $ "Unsupported form of type: " ++ show t

checkConAppForm :: TH.Type -> Maybe TN
checkConAppForm (TH.AppT t1 _) = checkConAppForm t1
checkConAppForm (TH.ConT tn) = pure $ TypeName tn
checkConAppForm (TH.InfixT _ tn _) = pure $ TypeName tn
checkConAppForm (TH.PromotedInfixT _ tn _) = pure $ TypeName tn
checkConAppForm (TH.TupleT _) = pure SomeTuple
checkConAppForm _ = Nothing

p2sp :: TH.Pat -> TH.Q SimplePat
p2sp (TH.VarP x) = pure $ SVarP x
p2sp (TH.TupP ps) = STupP <$> mapM p2sp ps
p2sp (TH.ParensP p) = p2sp p
p2sp (TH.TildeP p) = p2sp p
p2sp (TH.SigP p t) = SSigP <$> p2sp p <*> pure t
p2sp (TH.ConP cn [] ps) = do
  checkSingleConstructor cn
  SConP cn <$> mapM p2sp ps
p2sp p = fail $ "Unsupported pattern: " ++ show (TH.ppr p)

e2sp :: TH.Exp -> TH.Q SimplePat
e2sp (TH.VarE x) = pure $ SVarP x
e2sp (TH.TupE es) | all isJust es = STupP <$> sequenceA [e2sp e | Just e <- es]
e2sp (TH.ParensE e) = e2sp e
e2sp (TH.SigE e t) = SSigP <$> e2sp e <*> pure t
e2sp e | Just (cn, es) <- checkAppForm e = do
  checkSingleConstructor cn
  -- TODO: check this is fully-applied
  SConP cn <$> mapM e2sp es
e2sp e = fail $ "Unsupported expression: " ++ show (TH.ppr e)

checkAppForm :: TH.Exp -> Maybe (TH.Name, [TH.Exp])
checkAppForm (TH.VarE x) = pure (x, [])
checkAppForm (TH.AppE e1 e2) = do
  (n, args) <- checkAppForm e1
  pure (n, args ++ [e2])
checkAppForm e = Nothing

-- arrP :: TH.Q TH.Pat -> TH.Q TH.Pat -> TH.Q TH.Exp
-- arrP mp1 mp2 =
--   [|MALens (\ $(introTilde =<< mp1) -> $(p2e =<< mp2)) (const $ \ $(introTilde =<< mp2) -> pure $(p2e =<< mp2))|]

-- p2e :: TH.Pat -> TH.Q TH.Exp
-- p2e (TH.VarP x) = pure $ TH.VarE x
-- p2e (TH.TupP ps) = TH.TupE <$> mapM (fmap Just . p2e) ps
-- p2e (TH.ParensP p) = p2e p
-- p2e (TH.TildeP p) = p2e p
-- p2e (TH.SigP p t) = TH.SigE <$> p2e p <*> pure t
-- p2e p = fail $ "Unsupported pattern: `" ++ show p ++ "'"

-- introTilde :: TH.Pat -> TH.Q TH.Pat
-- introTilde (TH.VarP x) = pure $ TH.VarP x
-- introTilde (TH.TupP ps) = TH.TildeP <$> TH.TupP <$> (mapM introTilde ps)
-- introTilde (TH.ParensP p) = TH.ParensP <$> introTilde p
-- introTilde (TH.TildeP p) = introTilde p -- is it OK?
-- introTilde (TH.SigP p t) = TH.SigP <$> introTilde p <*> pure t
-- introTilde p = fail $ "Unsupported pattern: `" ++ show p ++ "'"