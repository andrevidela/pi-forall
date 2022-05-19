{- PiForall language -}

-- | The main routines for type-checking
module TypeCheck (tcModules, inferType, checkType) where

import Control.Monad.Except
import Data.List (nub)

import Data.Maybe ( catMaybes )


import Environment (D (..), TcMonad)
import Environment qualified as Env
import Equal qualified
import PrettyPrint (Disp (disp))
import Syntax
import Text.PrettyPrint.HughesPJ (($$),render)
import Unbound.Generics.LocallyNameless qualified as Unbound
import Unbound.Generics.LocallyNameless.Internal.Fold qualified as Unbound
import Unbound.Generics.LocallyNameless.Unsafe (unsafeUnbind)

import Debug.Trace

-- | Infer the type of a term. The returned type is not guaranteed to be checkable(?)
inferType :: Term -> TcMonad Type
inferType t = tcTerm t Nothing

-- | Check that the given term has the expected type.
-- The provided type does not necessarily to be in whnf, but it should be
-- already checked to be a good type
checkType :: Term -> Type -> TcMonad Type
checkType tm expectedTy = do
  nf <- Equal.whnf expectedTy
  tcTerm tm (Just nf)
  
-- | Make sure that the term is a type (i.e. has type 'Type')
tcType :: Term -> TcMonad ()
tcType tm = Env.withStage Erased (checkType tm Type) >> return ()
    
-- | check a term, producing an elaborated term
-- where all type annotations have been filled in.
-- The second argument is 'Nothing' in inference mode and
-- an expected type (in weak-head-normal form) in checking mode
tcTerm :: Term -> Maybe Type -> TcMonad Type
-- i-var
tcTerm t@(Var x) Nothing = do
  sig <- Env.lookupTy x   -- make sure the variable is accessible
  Env.checkStage (sigEp sig) 
  return (sigType sig)
-- i-type
tcTerm Type Nothing = return Type
-- i-pi
tcTerm (Pi bnd) Nothing = do
  ((x, {- SOLN EP -}ep,{- STUBWITH -} Unbound.unembed -> tyA), tyB) <- Unbound.unbind bnd
  tcType tyA
  Env.extendCtx (Sig (S x ep  tyA)) $ tcType tyB
  return Type
-- c-lam: check the type of a function
tcTerm (Lam bnd) (Just (Pi bnd2)) = do
  -- unbind the variables in the lambda expression and pi type
  ( (x {- SOLN EP -}, ep1 {- STUBWITH -}),
    body,
    (_, ep2,  Unbound.unembed -> tyA),
    tyB
    ) <-
    Unbound.unbind2Plus bnd bnd2
-- epsilons should match up
  guard (ep1 == ep2) 
  -- check the type of the body of the lambda expression
  etyB <- Env.extendCtx (Sig (S x ep1  tyA)) (checkType body tyB)
  return (Pi bnd2)
   
tcTerm (Lam _) (Just nf) =
  Env.err [DS "Lambda expression should have a function type, not ", DD nf]

-- i-app
tcTerm (App t1 a2) Nothing = do
  ty1 <- inferType t1
  (x, ep2,  tyA, tyB) <- Equal.ensurePi ty1
  guard (argEp a2 == ep2) 
  ty2 <- {- SOLN EP -}Env.withStage (argEp a2) ${- STUBWITH -} checkType (unArg a2) tyA
  return (Unbound.subst x (Ann (unArg a2) tyA) tyB)

-- i-ann
tcTerm (Ann tm ty) Nothing = do
  ty' <- tcType ty
  checkType tm ty
  
-- practicalities
-- remember the current position in the type checking monad
tcTerm (Pos p tm) mTy =
  Env.extendSourceLocation p tm $ tcTerm tm mTy
-- ignore parentheses
tcTerm (Paren tm) mTy = tcTerm tm mTy
-- ignore term, just return type annotation
tcTerm t@(TrustMe) (Just ty) = return ty
  
tcTerm (TyUnit) Nothing = return Type
tcTerm (LitUnit) Nothing = return TyUnit

-- i-bool
tcTerm (TyBool) Nothing = return Type


-- i-true/false
tcTerm (LitBool b) Nothing = do
  return TyBool


-- c-if
tcTerm t@(If t1 t2 t3) (Just ty) = do
  _ <- checkType t1 TyBool
  dtrue <- def t1 (LitBool True)
  dfalse <- def t1 (LitBool False)
  _ <- Env.extendCtxs dtrue $ checkType t2 ty
  _ <- Env.extendCtxs dfalse $ checkType t3 ty
  return ty


tcTerm (Let bnd) ann = do
  ((x, Unbound.unembed -> rhs), body) <- Unbound.unbind bnd
  aty <- inferType rhs 
  let sig = mkSig x aty
  ty <- Env.extendCtxs [Sig sig, Def x rhs] $
      tcTerm body ann
  when (x `elem` Unbound.toListOf Unbound.fv ty) $
    Env.err [DS "Let bound variable", DD x, DS "escapes in type", DD ty]
  return ty

-- Type constructor application
tcTerm (TCon c params) Nothing = do
  (Telescope delta, _) <- Env.lookupTCon c
  unless (length params == length delta) $
    Env.err
      [ DS "Datatype constructor",
        DD c,
        DS $
          "should have " ++ show (length delta)
            ++ "parameters, but was given",
        DD (length params)
      ]
  eparams <- tsTele params delta
  return Type

-- Data constructor application
-- we don't know the expected type, so see if there
-- is only one datacon of that name that takes no
-- parameters
tcTerm t@(DCon c args) Nothing = do
  matches <- Env.lookupDConAll c
  case matches of
    [(tname, (Telescope [], ConstructorDef _ _ (Telescope deltai)))] -> do
      let numArgs = length deltai
      unless (length args == numArgs) $
        Env.err
          [ DS "Constructor",
            DS c,
            DS "should have",
            DD numArgs,
            DS "data arguments, but was given",
            DD (length args),
            DS "arguments."
          ]
      eargs <- tcArgTele args deltai
      let ty = TCon tname []
      return ty
    [_] ->
      Env.err
        [ DS "Cannot infer the parameters to data constructors.",
          DS "Add an annotation."
        ]
    _ -> Env.err [DS "Ambiguous data constructor", DS c]

-- we know the expected type of the data constructor
-- so look up its type in the context
tcTerm t@(DCon c args) (Just ty) = do
  case ty of
    (TCon tname params) -> do
      (Telescope delta, Telescope deltai) <- Env.lookupDCon c tname
      let numArgs = length (filter isAssnSig deltai)
      unless (length args == numArgs) $
        Env.err
          [ DS "Constructor",
            DS c,
            DS "should have",
            DD numArgs,
            DS "data arguments, but was given",
            DD (length args),
            DS "arguments."
          ]
      newTele <- substTele delta params deltai
      eargs <- tcArgTele args newTele
      return ty
    _ ->
      Env.err [DS "Unexpected type", DD ty, DS "for data constructor", DD t]

-- Must have an annotation for Case
tcTerm t@(Case scrut alts) (Just ty) = do
  sty <- inferType scrut
  scrut' <- Equal.whnf scrut
  whnfTCon <- Equal.ensureTCon sty
  let checkAlt (Match bnd) = do
        (pat, body) <- Unbound.unbind bnd
        -- add variables from pattern to context
        -- could fail if branch is in-accessible
        (decls, evars) <- declarePatTCon pat whnfTCon
        -- add defs to the contents from scrut = pat
        -- could fail if branch is in-accessible
        decls' <- equateWithPatTCon scrut' pat whnfTCon
        _ <- Env.extendCtxs (decls ++ decls') $
            checkType body ty
        
        return ()
  let pats = map (\(Match bnd) -> fst (unsafeUnbind bnd)) alts
  mapM_ checkAlt alts
  exhaustivityCheck scrut' sty pats
  return ty

tcTerm (TyEq a b) Nothing = do
  aTy <- inferType a
  bTy <- checkType b aTy
  return Type
tcTerm Refl (Just ty@(TyEq a b)) = do
  Equal.equate a b
  return ty
tcTerm Refl (Just ty) = 
  Env.err [DS "refl annotated with", DD ty]
tcTerm t@(Subst tm p) (Just ty) = do
  -- infer the type of the proof p
  tp <- inferType p
  -- make sure that it is an equality between m and n
  (m, n) <- Equal.ensureTyEq tp
  -- if either side is a variable, add a definition to the context
  edecl <- def m n
  pdecl <- def p Refl
  _ <- Env.extendCtxs (edecl ++ pdecl) $ checkType tm ty
  return ty
tcTerm t@(Contra p) (Just ty) = do
  ty' <- inferType p
  (a, b) <- Equal.ensureTyEq ty'
  a' <- Equal.whnf a
  b' <- Equal.whnf b
  case (a', b') of
    
    (DCon da _, DCon db _)
      | da /= db ->
        return ty
    
    (LitBool b1, LitBool b2)
      | b1 /= b2 ->
        return ty
    (_, _) ->
      Env.err
        [ DS "I can't tell that",
          DD a,
          DS "and",
          DD b,
          DS "are contradictory"
        ]


tcTerm t@(Sigma bnd) Nothing = do
  ((x, Unbound.unembed -> tyA), tyB) <- Unbound.unbind bnd
  tcType tyA
  Env.extendCtx (Sig (mkSig x tyA)) $ tcType tyB
  return Type


tcTerm t@(Prod a b) (Just ty) = do
  case ty of
    (Sigma bnd) -> do
      ((x, Unbound.unembed -> tyA), tyB) <- Unbound.unbind bnd
      tyA' <- checkType a tyA
      tyB' <- Env.extendCtxs [Sig (mkSig x tyA'), Def x a] $ checkType b tyB
      return (Sigma (Unbound.bind (x, Unbound.embed tyA') tyB'))
    _ ->
      Env.err
        [ DS "Products must have Sigma Type",
          DD ty,
          DS "found instead"
        ]


tcTerm t@(LetPair p bnd) (Just ty) = do
  pty <- inferType p
  pty' <- Equal.whnf pty
  case pty' of
    Sigma bnd' -> do
      ((x, Unbound.unembed -> tyA), tyB) <- Unbound.unbind bnd'
      ((x', y'), body) <- Unbound.unbind bnd
      let tyB' = Unbound.subst x (Var x') tyB
      decl <- def p (Prod (Var x') (Var y'))
      Env.extendCtxs ([Sig (mkSig x' tyA), Sig (mkSig y' tyB')] ++ decl) $
          checkType body ty
    _ -> Env.err [DS "Scrutinee of pcase must have Sigma type"]


tcTerm t@(PrintMe) (Just ty) = do
  gamma <- Env.getLocalCtx
  Env.warn [DS "Unmet obligation.\nContext: ", DD gamma,
        DS "\nGoal: ", DD ty]
  return ty

-- c-infer
tcTerm tm (Just ty) = do
  ty' <- inferType tm
  Equal.equate ty' ty

  return ty'

tcTerm tm Nothing = 
  Env.err [DS "Must have a type annotation to check ", DD tm]

---------------------------------------------------------------------
-- helper functions for type checking

-- | Create a Def if either side normalizes to a single variable
def :: Term -> Term -> TcMonad [Decl]
def t1 t2 = do
    nf1 <- Equal.whnf t1
    nf2 <- Equal.whnf t2
    case (nf1, nf2) of
      (Var x, _) -> return [Def x nf2]
      (_, Var x) -> return [Def x nf1]
      _ -> return []

---------------------------------------------------------------------
-- helper functions for type constructor creation

-- | type check a list of type constructor arguments against a telescope
tsTele :: [Arg] -> [Assn] -> TcMonad [Arg]
tsTele = tcArgTele
  
---------------------------------------------------------------------
-- | type check a list of data constructor arguments against a telescope
tcArgTele :: [Arg] -> [Assn] -> TcMonad [Arg]
tcArgTele [] [] = return []
tcArgTele args (AssnProp (Eq tx ty) : tele) = do
  Equal.equate tx ty
  tcArgTele args tele
tcArgTele (Arg ep1 tm : terms) (AssnSig sig : tele') | ep1 == sigEp sig = do
  ety <- Env.withStage ep1 $ checkType tm (sigType sig)
  tele'' <- doSubst [(sigName sig, Ann tm ety)] tele'
  eterms <- tcArgTele terms tele''
  return $ Arg ep1 tm : eterms
tcArgTele (Arg ep1 _ : _) (AssnSig sig2 : _) =
  Env.err
    [ DD ep1,
      DS "argument provided when",
      DD (sigEp sig2),
      DS "argument was expected"
    ]
tcArgTele [] _ =
  Env.err [DD "Too few arguments provided."]
tcArgTele _ [] =
  Env.err [DD "Too many arguments provided."]

-- | Substitute a list of terms for the variables bound in a telescope
-- This is used to instantiate the parameters of a data constructor
-- to find the types of its arguments.
-- The first argument should only contain 'Runtime' type declarations.
substTele :: [Assn] -> [Arg] -> [Assn] -> TcMonad [Assn]
substTele tele args delta = doSubst (mkSubst tele (map unArg args)) delta
  where
    mkSubst [] [] = []
    mkSubst (AssnSig (S x Runtime _) : tele') (tm : tms) =
      (x, tm) : mkSubst tele' tms
    mkSubst _ _ = error "Internal error: substTele given illegal arguments"

-- From a constraint, fetch all declarations
-- derived from unifying the two terms
-- If the terms are not unifiable, throw an error
-- Note: we could do better with our unification
amb :: Term -> Bool
amb (App t1 t2) = True
amb (Pi _) = True
amb (If _ _ _) = True
amb (Sigma _) = True
amb (LetPair _ _) = True
amb (Let _) = True
amb (Case _ _) = True
amb _ = False

constraintToDecls :: Term -> Term -> TcMonad [Decl]
constraintToDecls tx ty = do
  txnf <- Equal.whnf tx
  tynf <- Equal.whnf ty
  if (Unbound.aeq txnf tynf)
    then return []
    else case (txnf, tynf) of
      (Var y, yty) -> return [Def y yty]
      (yty, Var y) -> return [Def y yty]
      (TCon s1 tms1, TCon s2 tms2)
        | s1 == s2 -> matchArgs tms1 tms2
      (Prod a1 a2, Prod b1 b2) -> matchTerms [a1, a2] [b1, b2]
      (TyEq a1 a2, TyEq b1 b2) -> matchTerms [a1, a2] [b1, b2]
      (DCon s1 a1s, DCon s2 a2s)
        | s1 == s2 -> matchArgs a1s a2s
      _ ->
        if amb txnf || amb tynf
          then return []
          else Env.err [DS "Cannot equate", DD txnf, DS "and", DD tynf]
  where
    matchTerms ts1 ts2 = matchArgs (map (Arg Runtime) ts1) (map (Arg Runtime) ts2)
    matchArgs (Arg _ t1 : a1s) (Arg _ t2 : a2s) = do
      ds <- constraintToDecls t1 t2
      ds' <- matchArgs a1s a2s
      return $ ds ++ ds'
    matchArgs [] [] = return []
    matchArgs _ _ = Env.err [DS "internal error (constraintToDecls)"]

-- Propagate the given substitution through the telescope, potentially
-- reworking the constraints.
doSubst :: [(TName, Term)] -> [Assn] -> TcMonad [Assn]
doSubst ss [] = return []
doSubst ss (AssnProp (Eq tx ty) : tele') = do
  let tx' = Unbound.substs ss tx
  let ty' = Unbound.substs ss ty
  -- (_decls, tsf) <- match tx' ty'
  decls <- constraintToDecls tx' ty'
  tele <- Env.extendCtxs decls $ (doSubst ss tele')
  return $ (AssnProp (Eq tx' ty') : tele)
doSubst ss (AssnSig sig : tele') = do
  tynf <- Equal.whnf (Unbound.substs ss (sigType sig))
  let sig' = sig{sigType = tynf}
  tele'' <- doSubst ss tele'
  return $ AssnSig sig' : tele''

-----------------------------------------------------------
-- helper functions for checking pattern matching

forgetTCon :: Equal.WhnfTCon -> Type
forgetTCon (Equal.WhnfTCon n ps) = 
  case n of
    "Bool" -> TyBool
    "One" -> TyUnit
    _ -> TCon n ps

-- | Create a binding in the context for each of the variables in
-- the pattern.
-- Also returns the erased variables so that they can be checked
declarePat :: Pattern -> Epsilon -> Type -> TcMonad ([Decl], [TName])
declarePat (PatVar x) ep y = return ([Sig (S x ep y)], [])
declarePat pat Runtime ty = do 
  whnfTCon <- Equal.ensureTCon ty
  declarePatTCon pat whnfTCon
declarePat pat Erased _ty =
  Env.err [DS "Cannot pattern match erased arguments in pattern ", DD pat]

declarePatTCon :: Pattern -> Equal.WhnfTCon -> TcMonad ([Decl], [TName])
declarePatTCon (PatCon d pats) (Equal.WhnfTCon c params) = do
  (Telescope delta, Telescope deltai) <- Env.lookupDCon d c
  tele <- substTele delta params deltai
  declarePats d pats tele
declarePatTCon (PatBool _) (Equal.WhnfTCon "Bool" []) = do
  return ([],[])
declarePatTCon PatUnit (Equal.WhnfTCon "One" []) = do
  return ([],[])
declarePatTCon (PatVar x) y = 
  Env.err [DS "Internal error: declarePatTCon, found ", DD (PatVar x)]
declarePatTCon pat ty =
  Env.err [DS "Cannot match pattern", DD pat, DS "with type", DD (forgetTCon ty)]


declarePats :: DCName -> [(Pattern, Epsilon)] -> [Assn] -> TcMonad ([Decl], [TName])
declarePats dc [] [] = return ([], [])
declarePats dc pats (AssnProp (Eq tx ty) : tele) = do
  new_decls <- constraintToDecls tx ty
  (decls, names) <- Env.extendCtxs new_decls $ declarePats dc pats tele
  return (new_decls ++ decls, names)
declarePats dc ((pat, _) : pats) (AssnSig (S x ep ty) : tele) = do
  (ds1, v1) <- declarePat pat ep ty
  tm <- pat2Term pat ty
  (ds2, v2) <- declarePats dc pats (Unbound.subst x tm tele)
  return ((ds1 ++ ds2), (v1 ++ v2))
declarePats dc [] _ = Env.err [DS "Not enough patterns in match for data constructor", DD dc]
declarePats dc pats [] = Env.err [DS "Too many patterns in match for data constructor", DD dc]

-- | Convert a pattern to an (annotated) term so that we can substitute it for
-- variables in telescopes. Because data constructors must be annotated with
-- their types, we need to have the expected type of the pattern available.
pat2Term :: Pattern -> Type -> TcMonad Term
pat2Term (PatCon dc pats) ty@(TCon n params) = do
  (Telescope delta, Telescope deltai) <- Env.lookupDCon dc n
  tele <- substTele delta params deltai
  args <- pats2Terms pats tele
  return (DCon dc args)
  where
    pats2Terms :: [(Pattern, Epsilon)] -> [Assn] -> TcMonad [Arg]
    pats2Terms [] [] = return []
    pats2Terms ps (AssnProp (Eq tx' ty') : tele') = do
      decls <- constraintToDecls tx' ty'
      Env.extendCtxs decls $ pats2Terms ps tele'
    pats2Terms ((p, _) : ps) (AssnSig (S x ep ty1) : d) = do
      t <- pat2Term p ty1
      ts <- pats2Terms ps (Unbound.subst x t d)
      return (Arg ep t : ts)
    pats2Terms _ _ = Env.err [DS "Invalid number of args to pattern", DD dc]
pat2Term (PatBool b) ty = pure $ LitBool b
pat2Term (PatUnit) ty = pure $ LitUnit
pat2Term (PatVar x) ty = return (Var x)
pat2Term _ _ = Env.err [DS "Internal error: pat2Term"]

-- | Create a list of variable definitions from the scrutinee
-- of a case expression and the pattern in a branch. Scrutinees
-- that are not variables or constructors applied to vars may not
-- produce any equations.
equateWithPat :: Term -> Pattern -> Type -> TcMonad [Decl]
equateWithPat (Var x) pat ty = do
  tm <- pat2Term pat ty
  return [Def x tm]
equateWithPat tm pat ty = do 
  whnfTCon <- Equal.ensureTCon ty
  equateWithPatTCon tm pat whnfTCon

equateWithPatTCon :: Term -> Pattern -> Equal.WhnfTCon -> TcMonad [Decl]
equateWithPatTCon (Var x) pat ty = do
  tm <- pat2Term pat (forgetTCon ty)
  return [Def x tm]
equateWithPatTCon (LitBool b) (PatBool b') (Equal.WhnfTCon "Bool" []) | b == b' = pure []
equateWithPatTCon LitUnit PatUnit (Equal.WhnfTCon "One" []) = pure []
equateWithPatTCon (DCon dc args) (PatCon dc' pats) (Equal.WhnfTCon n params)
  | dc == dc' = do
    (Telescope delta, Telescope deltai) <- Env.lookupDCon dc n
    tele <- substTele delta params deltai
    let eqWithPats :: [Term] -> [(Pattern, Epsilon)] -> [Assn] -> TcMonad [Decl]
        eqWithPats [] [] [] = return []
        eqWithPats ts ps (AssnProp (Eq tx ty) : tl) = do
          decls <- constraintToDecls tx ty
          Env.extendCtxs decls $ eqWithPats ts ps tl
        eqWithPats (t : ts) ((p, _) : ps) (AssnSig (S x _ ty) : tl) = do
          t' <- Equal.whnf t
          decls <- equateWithPat t' p ty
          decls' <- eqWithPats ts ps (Unbound.subst x t' tl)
          return (decls ++ decls')
        eqWithPats _ _ _ =
          Env.err [DS "Invalid number of args to pattern", DD dc]
    eqWithPats (map unArg args) pats tele
equateWithPatTCon (DCon dc args) (PatCon dc' pats) (Equal.WhnfTCon n params) = do
  Env.warn
    [ DS "The case for",
      DD dc',
      DS "is unreachable.",
      DS "However, this implementation cannot yet allow it",
      DS "to be omitted."
    ]
    >> return []
equateWithPatTCon _ _ _ = return []

-- | Check all of the types contained within a telescope
tcTypeTele :: [Assn] -> TcMonad ()
tcTypeTele [] = return ()
tcTypeTele (AssnProp (Eq tm1 tm2) : tl) = do
  ty1 <- Env.withStage Erased $ inferType tm1
  _ <- Env.withStage Erased $ checkType tm2 ty1
  decls <- constraintToDecls tm1 tm2
  Env.extendCtxs decls $ tcTypeTele tl
tcTypeTele (AssnSig sig : tl) = do
  tcType (sigType sig)
  Env.extendCtx (Sig sig) $ tcTypeTele tl



--------------------------------------------------------
-- Using the typechecker for decls and modules and stuff
--------------------------------------------------------

-- | Typecheck a collection of modules. Assumes that each module
-- appears after its dependencies. Returns the same list of modules
-- with each definition typechecked
tcModules :: [Module] -> TcMonad [Module]
tcModules mods = foldM tcM [] mods
  where
    -- Check module m against modules in defs, then add m to the list.
    defs `tcM` m = do
      -- "M" is for "Module" not "monad"
      let name = moduleName m
      liftIO $ putStrLn $ "Checking module " ++ show name
      m' <- defs `tcModule` m
      return $ defs ++ [m']

-- | Typecheck an entire module.
tcModule ::
  -- | List of already checked modules (including their Decls).
  [Module] ->
  -- | Module to check.
  Module ->
  -- | The same module with all Decls checked and elaborated.
  TcMonad Module
tcModule defs m' = do
  checkedEntries <-
    Env.extendCtxMods importedModules $
      foldr
        tcE
        (return [])
        (moduleEntries m')
  return $ m' {moduleEntries = checkedEntries}
  where
    d `tcE` m = do
      -- Extend the Env per the current Decl before checking
      -- subsequent Decls.
      x <- tcEntry d
      case x of
        AddHint hint -> Env.extendHints hint m
        -- Add decls to the Decls to be returned
        AddCtx decls -> (decls ++) <$> (Env.extendCtxsGlobal decls m)
    -- Get all of the defs from imported modules (this is the env to check current module in)
    importedModules = filter (\x -> (ModuleImport (moduleName x)) `elem` moduleImports m') defs

-- | The Env-delta returned when type-checking a top-level Decl.
data HintOrCtx
  = AddHint Sig
  | AddCtx [Decl]

-- | Check each sort of declaration in a module
tcEntry :: Decl -> TcMonad HintOrCtx
tcEntry (Def n term) = do
  oldDef <- Env.lookupDef n
  case oldDef of
    Nothing -> tc
    Just term' -> die term'
  where
    tc = do
      lkup <- Env.lookupHint n
      case lkup of
        Nothing -> do
          ty <- inferType term
          return $ AddCtx [Sig (S n {- SOLN EP -}Runtime{- STUBWITH -} ty), Def n term]
        Just sig ->
          let handler (Env.Err ps msg) = throwError $ Env.Err ps (msg $$ msg')
              msg' =
                disp
                  [ DS "When checking the term ",
                    DD term,
                    DS "against the signature",
                    DD sig
                  ]
           in do
                ety <-
                  Env.extendCtx (Sig sig) $ checkType term (sigType sig) `catchError` handler
                -- Put the elaborated version of term into the context.
                let esig = sig{sigType = ety}
                if (n `elem` Unbound.toListOf Unbound.fv term)
                  then return $ AddCtx [Sig esig, RecDef n term]
                  else return $ AddCtx [Sig esig, Def n term]
    die term' =
      Env.extendSourceLocation (unPosFlaky term) term $
        Env.err
          [ DS "Multiple definitions of",
            DD n,
            DS "Previous definition was",
            DD term'
          ]
tcEntry (Sig sig) = do
  duplicateTypeBindingCheck sig
  tcType (sigType sig)
  return $ AddHint sig

-- rule Decl_data
tcEntry (Data t (Telescope delta) cs) =
  do
    -- Check that the telescope for the datatype definition is well-formed
    edelta <- tcTypeTele delta
    ---- check that the telescope provided
    ---  for each data constructor is wellfomed, and elaborate them
    let elabConstructorDef defn@(ConstructorDef pos d (Telescope tele)) =
          Env.extendSourceLocation pos defn $
            Env.extendCtx (DataSig t (Telescope delta)) $
              Env.extendCtxTele delta $ do
                etele <- tcTypeTele tele
                return (ConstructorDef pos d (Telescope tele))
    ecs <- mapM elabConstructorDef cs
    -- Implicitly, we expect the constructors to actually be different...
    let cnames = map (\(ConstructorDef _ c _) -> c) cs
    unless (length cnames == length (nub cnames)) $
      Env.err [DS "Datatype definition", DD t, DS "contains duplicated constructors"]
    -- finally, add the datatype to the env and perform action m
    return $ AddCtx [Data t (Telescope delta) ecs]
tcEntry (DataSig _ _) = Env.err [DS "internal construct"]
tcEntry (RecDef _ _) = Env.err [DS "internal construct"]



-- | Make sure that we don't have the same name twice in the
-- environment. (We don't rename top-level module definitions.)
duplicateTypeBindingCheck :: Sig -> TcMonad ()
duplicateTypeBindingCheck sig = do
  -- Look for existing type bindings ...
  let n = sigName sig
  l <- Env.lookupTyMaybe n
  l' <- Env.lookupHint n
  -- ... we don't care which, if either are Just.
  case catMaybes [l, l'] of
    [] -> return ()
    -- We already have a type in the environment so fail.
    sig' : _ ->
      let (Pos p _) = sigType sig
          msg =
            [ DS "Duplicate type signature ",
              DD sig,
              DS "Previous was",
              DD sig'
            ]
       in Env.extendSourceLocation p sig $ Env.err msg

-----------------------------------------------------------
-- Checking that pattern matching is exhaustive
-----------------------------------------------------------

-- | Given a particular type and a list of patterns, make
-- sure that the patterns cover all potential cases for that
-- type.
-- If the list of patterns starts with a variable, then it doesn't
-- matter what the type is, the variable is exhaustive. (This code
-- does not report unreachable patterns.)
-- Otherwise, the scrutinee type must be a type constructor, so the
-- code looks up the data constructors for that type and makes sure that
-- there are patterns for each one.
exhaustivityCheck :: Term -> Type -> [Pattern] -> TcMonad ()
exhaustivityCheck scrut ty (PatVar x : _) = return ()
exhaustivityCheck scrut TyUnit [PatUnit] = return ()
exhaustivityCheck scrut TyBool [PatBool b] = return ()
exhaustivityCheck scrut ty pats = do
  (Equal.WhnfTCon tcon tys) <- Equal.ensureTCon ty
  (Telescope delta, mdefs) <- Env.lookupTCon tcon
  case mdefs of
    Just datacons -> loop pats datacons
      where
        loop [] [] = return ()
        loop [] dcons = do
          l <- checkImpossible dcons
          if null l
            then return ()
            else Env.err $ [DS "Missing case for "] ++ map DD l
        loop [PatUnit] [ConstructorDef _ "tt" (Telescope [])]  = do
          return ()
        loop (PatUnit : _) _ = Env.err [DS "loop PatUnit"]
        loop (PatBool b : pats') dcons = do
          (cd@(ConstructorDef _ _ _, dcons')) <- removeDcon (show b) dcons
          loop pats' dcons'
        loop ((PatVar x) : _) dcons = return ()
        loop ((PatCon dc args) : pats') dcons = do
          (cd@(ConstructorDef _ _ (Telescope tele), dcons')) <- removeDcon dc dcons
          tele' <- substTele delta tys tele
          let (aargs, pats'') = relatedPats dc pats'
          checkSubPats dc tele' (args : aargs)
          loop pats'' dcons'

        -- make sure that the given list of constructors is impossible
        -- in the current environment
        checkImpossible :: [ConstructorDef] -> TcMonad [DCName]
        checkImpossible [] = return []
        checkImpossible cd@(ConstructorDef _ dc (Telescope tele) : rest) = do
          this <-
            ( do
                tele' <- substTele delta tys tele
                _ <- tcTypeTele tele'
                return [dc]
              )
              `catchError` (\_ -> return [])
          others <- checkImpossible rest
          return (this ++ others)
    Nothing ->
      Env.err [DS "Cannot determine constructors of", DD ty]

-- this could be because the scrutinee is not unifiable with the pattern
-- or because the constraints on the pattern are not satisfiable

-- | Given a particular data constructor name and a list of data
-- constructor definitions, pull the definition out of the list and
-- return it paired with the remainder of the list.
removeDcon ::
  DCName ->
  [ConstructorDef] ->
  TcMonad (ConstructorDef, [ConstructorDef])
removeDcon dc (cd@(ConstructorDef _ dc' _) : rest)
  | dc == dc' =
    return (cd, rest)
removeDcon dc (cd1 : rest) = do
  (cd2, rr) <- removeDcon dc rest
  return (cd2, cd1 : rr)
removeDcon dc [] = Env.err [DS $ "Internal error: Can't find" ++ show dc]

-- | Given a particular data constructor name and a list of patterns,
-- pull out the subpatterns that occur as arguments to that data
-- constructor and return them paired with the remaining patterns.
relatedPats :: DCName -> [Pattern] -> ([[(Pattern, Epsilon)]], [Pattern])
relatedPats dc [] = ([], [])
relatedPats dc (pc@(PatVar _) : pats) = ([], pc : pats)
relatedPats dc ((PatCon dc' args) : pats)
  | dc == dc' =
    let (aargs, rest) = relatedPats dc pats
     in (args : aargs, rest)
relatedPats dc (pc : pats) =
  let (aargs, rest) = relatedPats dc pats
   in (aargs, pc : rest)


-- | Occurs check for the subpatterns of a data constructor. Given
-- the telescope specifying the types of the arguments, plus the
-- subpatterns identified by relatedPats, check that they are each
-- exhaustive.

-- for simplicity, this function requires that all subpatterns
-- are pattern variables.
checkSubPats :: DCName -> [Assn] -> [[(Pattern, Epsilon)]] -> TcMonad ()
checkSubPats dc [] _ = return ()
checkSubPats dc (AssnProp _ : tele) patss = checkSubPats dc tele patss
checkSubPats dc (AssnSig _ : tele) patss
  | length patss > 0 && (all ((> 0) . length) patss) = do
    let hds = map (fst . head) patss
    let tls = map tail patss
    case hds of
      (PatVar _ : []) -> checkSubPats dc tele tls
      _ -> Env.err [DS "All subpatterns must be variables in this version."]
checkSubPats dc t ps =
  Env.err [DS "Internal error in checkSubPats", DD dc, DS (show ps)]

