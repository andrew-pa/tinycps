{-# LANGUAGE OverloadedStrings #-}

module XIr where

import Control.Monad.Reader
import Control.Monad.State
import Data.Containers.ListUtils (nubOrd)
import Data.Functor ((<&>))
import Data.List (intercalate)
import qualified Data.Map as Map
import Data.Map ((!))
import Data.Maybe (fromMaybe, maybeToList)
import qualified Data.Set as Set
import qualified Data.Text as T
import Ext (incrSymCounter)
import Ir (KType, UType(..), showPair)
import qualified Ir

data Symbol =
    Symbol T.Text Int
    deriving (Eq, Ord)

instance Show Symbol where
    show (Symbol text int) = T.unpack text ++ show int

symbolName :: Symbol -> T.Text
symbolName (Symbol name _) = name

symToText :: Symbol -> T.Text
symToText (Symbol name index) = T.concat [name, T.pack (show index)]

data Binding ty = Binding
    { bindingName :: Symbol
    , bindingType :: ty
    } deriving (Eq)

instance (Show t) => Show (Binding t) where
    show (Binding sym ty) = showPair (sym, ty)

data Lambda = Lambda
    { l_args :: [Binding UType]
    , l_cont :: Binding KType
    , l_body :: Expr
    } deriving (Eq)

instance Show Lambda where
    show (Lambda args cont body) =
        "λ("
            ++ intercalate ", " (map show args)
            ++ " ⟶ "
            ++ show cont
            ++ ") { "
            ++ show body
            ++ " }"

lambdaType :: Lambda -> UType
lambdaType Lambda {l_args, l_cont, l_body = _} = TyFn (map bindingType l_args) (bindingType l_cont)

newtype UTerm =
    UVar Symbol
    deriving (Eq)

instance Show UTerm where
    show (UVar sym) = show sym

utermAsSymbol :: UTerm -> Symbol
utermAsSymbol (UVar v) = v

data KTerm
    = KVar Symbol
    | KLambda
          { kl_arg :: Maybe (Binding UType)
          , kl_body :: Expr
          }
    deriving (Eq)

instance Show KTerm where
    show (KVar sym) = show sym
    show (KLambda (Just arg) body) = "κ" ++ show arg ++ " {" ++ show body ++ "}"
    show (KLambda Nothing body) = "κ {" ++ show body ++ "}"

boundSymbol :: KTerm -> Maybe Symbol
boundSymbol KLambda {kl_arg = Just (Binding name _)} = Just name
boundSymbol _ = Nothing

data Lifetime
    = Unknown
    | Immediate
    | Stack
    | Heap
    deriving (Eq, Show)

data LiteralRecordValue
    = LRVUTerm UTerm
    | LRVSelect UTerm T.Text
    deriving (Eq)

instance Show LiteralRecordValue where
    show (LRVUTerm t) = show t
    show (LRVSelect r f) = show r ++ "." ++ show f

litRecValAsUTerm :: LiteralRecordValue -> UTerm
litRecValAsUTerm (LRVUTerm t) = t
litRecValAsUTerm (LRVSelect r _) = r

data LiteralValue
    = LiInt Int
    | LiRecord (Map.Map T.Text LiteralRecordValue)
    | ULambda Lambda
    | TopLevelRef Symbol
    deriving (Eq)

instance Show LiteralValue where
    show (LiInt i) = show i
    show (LiRecord rec) = "{ " ++ intercalate ", " (map showPair (Map.toList rec)) ++ " }"
    show (ULambda lambda) = show lambda
    show (TopLevelRef s) = "mod:" ++ show s

data Expr
    = UCall
          { uc_func :: UTerm
          , uc_args :: [UTerm]
          , uc_cont :: KTerm
          }
    | Literal
          { lt_val :: LiteralValue
          , lt_lifetime :: Lifetime
          , lt_cont :: KTerm
          }
    | KCall
          { kc_cont :: KTerm
          , kc_arg :: UTerm
          }
    | Select
          { sl_field :: T.Text
          , sl_record :: UTerm
          , sl_cont :: KTerm
          }
    | If
          { if_test :: UTerm
          , if_csq :: KTerm
          , if_alt :: KTerm
          }
    deriving (Eq)

-- uterm variables used as operands of the root expression
exprOperands :: Expr -> Set.Set Symbol
exprOperands UCall {uc_func, uc_args} = Set.fromList $ map utermAsSymbol $ uc_func : uc_args
exprOperands Literal {lt_val = LiRecord fields} =
    Set.fromList $ map (utermAsSymbol . litRecValAsUTerm . snd) $ Map.toList fields
exprOperands Literal {lt_val = ULambda lam} = freeVariables lam
exprOperands Literal {lt_val = TopLevelRef _} = Set.empty
exprOperands Literal {} = Set.empty
exprOperands KCall {kc_arg} = Set.singleton $ utermAsSymbol kc_arg
exprOperands Select {sl_record} = Set.singleton $ utermAsSymbol sl_record
exprOperands If {if_test} = Set.singleton $ utermAsSymbol if_test

-- continuation terms in an expression
exprContinuations :: Expr -> [KTerm]
exprContinuations UCall {uc_cont} = [uc_cont]
exprContinuations Literal {lt_cont} = [lt_cont]
exprContinuations KCall {kc_cont} = [kc_cont]
exprContinuations Select {sl_cont} = [sl_cont]
exprContinuations If {if_csq, if_alt} = [if_csq, if_alt]

variablesByFirstOccurenceInExpr :: Expr -> [Symbol]
variablesByFirstOccurenceInExpr = nubOrd . runE
  where
    runE e = Set.toList (exprOperands e) ++ concatMap runKT (exprContinuations e)
    runKT KLambda {kl_body} = runE kl_body
    runKT _ = []

transformContBody ::
       Monad m
    => (Expr -> ReaderT (Map.Map Symbol UType) m Expr)
    -> KTerm
    -> ReaderT (Map.Map Symbol UType) m KTerm
transformContBody f (KLambda {kl_arg, kl_body}) = do
    body <- local (maybe id (\(Binding n t) -> Map.insert n t) kl_arg) $ f kl_body
    return KLambda {kl_arg = kl_arg, kl_body = body}
transformContBody _ k = return k

mapOverContinuationBodies ::
       Monad m
    => Expr
    -> (Expr -> ReaderT (Map.Map Symbol UType) m Expr)
    -> ReaderT (Map.Map Symbol UType) m Expr
mapOverContinuationBodies UCall {uc_func, uc_args, uc_cont} f =
    transformContBody f uc_cont <&> \c -> UCall {uc_func = uc_func, uc_args = uc_args, uc_cont = c}
mapOverContinuationBodies KCall {kc_cont, kc_arg} f =
    transformContBody f kc_cont <&> \c -> KCall {kc_cont = c, kc_arg = kc_arg}
mapOverContinuationBodies Literal {lt_val, lt_lifetime, lt_cont} f =
    transformContBody f lt_cont <&> \c ->
        Literal {lt_val = lt_val, lt_lifetime = lt_lifetime, lt_cont = c}
mapOverContinuationBodies Select {sl_field, sl_record, sl_cont} f =
    transformContBody f sl_cont <&> \c ->
        Select {sl_field = sl_field, sl_record = sl_record, sl_cont = c}
mapOverContinuationBodies If {if_test, if_csq, if_alt} f = do
    csq <- transformContBody f if_csq
    alt <- transformContBody f if_alt
    return If {if_test = if_test, if_csq = csq, if_alt = alt}

instance Show Expr where
    show (UCall func args cont) =
        show func ++ "(" ++ intercalate ", " (map show args) ++ ") " ++ "⟶ " ++ show cont
    show (Literal val lifetime cont) =
        "(" ++ show val ++ "'" ++ show lifetime ++ ") ⇒ " ++ show cont
    show (KCall cont arg) = show cont ++ " ← (" ++ show arg ++ ")"
    show (Select field record cont) = show record ++ "." ++ show field ++ " ⟶ " ++ show cont
    show (If tst csq alt) = "if " ++ show tst ++ " then " ++ show csq ++ " else " ++ show alt

newtype Module = Module
    { m_funcs :: Map.Map Symbol Lambda
    } deriving (Eq)

instance Show Module where
    show (Module funcs) = "Module {\n" ++ unlines (map showFunc (Map.toList funcs)) ++ "}"
      where
        showFunc (name, lambda) = show name ++ " = " ++ show lambda

collectOverTerms ::
       (Monad m)
    => (Monoid r) => (UTerm -> m r) -> (KTerm -> m r) -> (LiteralValue -> m r) -> Expr -> m r
collectOverTerms inUTerm inKTerm inLiteral e =
    case e of
        UCall {uc_func, uc_args, uc_cont} -> do
            inCont <- inKTerm uc_cont
            inArgs <- mapM inUTerm (uc_func : uc_args)
            return (mconcat $ inCont : inArgs)
        KCall {kc_cont, kc_arg} -> do
            inCont <- inKTerm kc_cont
            inArg <- inUTerm kc_arg
            return (mappend inCont inArg)
        Select {sl_record, sl_cont} -> do
            inCont <- inKTerm sl_cont
            inArg <- inUTerm sl_record
            return (mappend inCont inArg)
        If {if_test, if_csq, if_alt} -> do
            inTest <- inUTerm if_test
            inCsq <- inKTerm if_csq
            inAlt <- inKTerm if_alt
            return (mconcat [inTest, inCsq, inAlt])
        Literal {lt_val, lt_cont} -> do
            cont <- inKTerm lt_cont
            val <- inLiteral lt_val
            return $ mconcat [cont, val]

freeVariables :: Lambda -> Set.Set Symbol
freeVariables Lambda {l_args, l_cont, l_body} = runReader (freeInExpr l_body) (argsToSet l_args)

argsToSet :: [Binding ty] -> Set.Set Symbol
argsToSet = Set.fromList . map bindingName

freeInExpr :: Expr -> Reader (Set.Set Symbol) (Set.Set Symbol)
freeInExpr = collectOverTerms freeInUTerm freeInKTerm freeInLiteral

freeInKTerm :: KTerm -> Reader (Set.Set Symbol) (Set.Set Symbol)
freeInKTerm (KVar _) = return Set.empty
freeInKTerm KLambda {kl_arg = Just argName, kl_body} =
    local (Set.insert (bindingName argName)) (freeInExpr kl_body)
freeInKTerm KLambda {kl_arg = Nothing, kl_body} = freeInExpr kl_body

freeInUTerm :: UTerm -> Reader (Set.Set Symbol) (Set.Set Symbol)
freeInUTerm (UVar v) = do
    bound <- reader $ Set.member v
    return
        (if bound
             then Set.empty
             else Set.singleton v)

freeInLiteral :: LiteralValue -> Reader (Set.Set Symbol) (Set.Set Symbol)
freeInLiteral (LiInt _) = return Set.empty
freeInLiteral (TopLevelRef _) = return Set.empty
freeInLiteral (LiRecord fields) = mapM (freeInUTerm . litRecValAsUTerm) fields <&> Set.unions
freeInLiteral (ULambda Lambda {l_args, l_cont, l_body}) =
    local (Set.union $ argsToSet l_args) (freeInExpr l_body)

subst :: Map.Map Symbol UTerm -> Expr -> Expr
subst subMap expr =
    case expr of
        UCall func args cont -> UCall (substUTerm func) (map substUTerm args) (substKTerm cont)
        Literal val lifetime cont -> Literal (substLiteral val) lifetime (substKTerm cont)
        KCall cont arg -> KCall (substKTerm cont) (substUTerm arg)
        Select field record cont -> Select field (substUTerm record) (substKTerm cont)
        If test csq alt -> If (substUTerm test) (substKTerm csq) (substKTerm alt)
  where
    -- Substitute UTerm using the substitution map
    substUTerm :: UTerm -> UTerm
    substUTerm uvar@(UVar sym) = Map.findWithDefault uvar sym subMap
    -- Substitute in KTerm
    substKTerm :: KTerm -> KTerm
    substKTerm (KVar sym) = KVar sym
    substKTerm (KLambda arg body) = KLambda (fmap substBinding arg) (subst subMap body)
    -- Substitute in Binding
    substBinding :: Binding ty -> Binding ty
    substBinding (Binding name ty) = Binding name ty
    -- Substitute in LiteralValue
    substLiteral :: LiteralValue -> LiteralValue
    substLiteral (LiInt i) = LiInt i
    substLiteral (LiRecord rec) = LiRecord (Map.map substLiteralRecordValue rec)
    substLiteral (ULambda lambda) = ULambda (substLambda lambda)
    substLiteral (TopLevelRef s) = TopLevelRef s
    -- Substitute in LiteralRecordValue
    substLiteralRecordValue :: LiteralRecordValue -> LiteralRecordValue
    substLiteralRecordValue (LRVUTerm t) = LRVUTerm (substUTerm t)
    substLiteralRecordValue (LRVSelect r f) = LRVSelect (substUTerm r) f
    -- Substitute in Lambda
    substLambda :: Lambda -> Lambda
    substLambda (Lambda args cont body) =
        Lambda (map substBinding args) (substBinding cont) (subst subMap body)

-- TODO: perhaps the preprocess step should have its own module?
type PreprocessEnv = (Map.Map T.Text Int, Map.Map Ir.Symbol UType, Map.Map Ir.Symbol UType)

type PreprocessM a = ReaderT PreprocessEnv (State Int) a

uniqueSym :: Monad m => T.Text -> (StateT Int m) Symbol
uniqueSym t = Symbol t <$> incrSymCounter

nextTempVar :: PreprocessM Symbol
nextTempVar = lift $ uniqueSym "tmp"

convertSym :: Ir.Symbol -> PreprocessM Symbol
convertSym (Ir.Symbol s) = do
    i <- reader $ Map.lookup s . (\(a, _, _) -> a)
    j <- get
    return (Symbol s (fromMaybe j i))

convertBinding :: Ir.Binding t -> PreprocessM (Binding t)
convertBinding (Ir.Binding name ty) = do
    n <- convertSym name
    return Binding {bindingName = n, bindingType = ty}

inNewScope :: Maybe (Binding KType) -> [Binding UType] -> PreprocessM a -> PreprocessM a
inNewScope k_binding u_bindings m = lift incrSymCounter >> local updateEnv m
  where
    addBindingU (Binding (Symbol n i) t) (ei, et, tl) =
        (Map.insert n i ei, Map.insert (Ir.Symbol n) t et, tl)
    addBindingK (Binding (Symbol n i) _) (ei, et, tl) = (Map.insert n i ei, et, tl)
    updateEnv env = foldr addBindingU (foldr addBindingK env (maybeToList k_binding)) u_bindings

preprocess :: Ir.Module -> State Int Module
preprocessLambda :: Ir.Lambda -> PreprocessM Lambda
preprocessExpr :: Ir.Expr -> PreprocessM Expr
preprocessUTerm :: Ir.UTerm -> (UTerm -> PreprocessM Expr) -> PreprocessM Expr
preprocessKTerm :: Ir.KTerm -> PreprocessM KTerm
preprocess (Ir.Module funcs) =
    runReaderT process (Map.empty, Map.empty, Map.map Ir.lambdaType funcs)
  where
    process = mapM processTopLevel (Map.toList funcs) <&> (Module . Map.fromList)
    processTopLevel (n, f) = do
        nn <- convertSym n
        pf <- preprocessLambda f
        return (nn, pf)

preprocessLambda (Ir.Lambda args cont body) = do
    cargs <- mapM convertBinding args
    ccont <- convertBinding cont
    cbody <- inNewScope (Just ccont) cargs (preprocessExpr body)
    return $ Lambda cargs ccont cbody

preprocessKTerm (Ir.KVar v) = convertSym v <&> KVar
preprocessKTerm (Ir.KLambda kl_arg kl_body) = do
    arg <- mapM convertBinding kl_arg
    body <- inNewScope Nothing (maybeToList arg) $ preprocessExpr kl_body
    return KLambda {kl_arg = arg, kl_body = body}

lookupType :: Ir.Symbol -> PreprocessEnv -> UType
lookupType s (_, et, _) = et ! s

preprocessUTerm (Ir.UVar v@(Ir.Symbol vtxt)) k = do
    isTopLevel <- reader (\(_, _, tl) -> Map.lookup v tl)
    case isTopLevel of
        Just topLevelDefType -> do
            tmpVar <- nextTempVar
            innerNext <- k (UVar tmpVar)
            return
                $ Literal
                      { lt_val = TopLevelRef $ Symbol vtxt 0
                      , lt_lifetime = Immediate
                      , lt_cont =
                            KLambda
                                { kl_arg = Just (Binding tmpVar topLevelDefType)
                                , kl_body = innerNext
                                }
                      }
        Nothing -> convertSym v >>= k . UVar
preprocessUTerm ut@(Ir.LiRecord record_fields) k = buildExpr (Map.toList record_fields) []
  where
    buildExpr :: [(T.Text, Ir.UTerm)] -> [(T.Text, LiteralRecordValue)] -> PreprocessM Expr
    buildExpr [] resFields = do
        tmpVar <- nextTempVar
        innerNext <- k (UVar tmpVar)
        ty <- Ir.utermType lookupType ut
        return
            $ Literal
                  { lt_val = LiRecord $ Map.fromList resFields
                  , lt_lifetime = Heap
                  , lt_cont = KLambda {kl_arg = Just (Binding tmpVar ty), kl_body = innerNext}
                  }
    buildExpr ((name, value):fields) resFields =
        preprocessUTerm value $ \cv -> buildExpr fields ((name, LRVUTerm cv) : resFields)
preprocessUTerm ut k = do
    tmpVar <- nextTempVar
    inner <- k (UVar tmpVar)
    ty <- Ir.utermType lookupType ut
    (val, lifetime) <-
        case ut of
            (Ir.LiInt i) -> return (LiInt i, Immediate)
            (Ir.ULambda lam) -> do
                plam <- preprocessLambda lam
                return (ULambda plam, Heap)
    return
        $ Literal
              { lt_val = val
              , lt_lifetime = lifetime
              , lt_cont = KLambda {kl_arg = Just (Binding tmpVar ty), kl_body = inner}
              }

preprocessExpr Ir.UCall {Ir.uc_func, Ir.uc_args, Ir.uc_cont} = buildExpr uc_args []
  where
    buildExpr :: [Ir.UTerm] -> [UTerm] -> PreprocessM Expr
    buildExpr [] args =
        preprocessUTerm uc_func $ \func -> do
            cont <- preprocessKTerm uc_cont
            return UCall {uc_func = func, uc_args = args, uc_cont = cont}
    buildExpr (a:args) resArgs = preprocessUTerm a $ \aa -> buildExpr args (aa : resArgs)
preprocessExpr Ir.KCall {Ir.kc_arg, Ir.kc_cont} =
    preprocessUTerm kc_arg $ \arg -> do
        cont <- preprocessKTerm kc_cont
        return KCall {kc_arg = arg, kc_cont = cont}
preprocessExpr Ir.Select {Ir.sl_field, Ir.sl_record, Ir.sl_cont} =
    preprocessUTerm sl_record $ \record -> do
        cont <- preprocessKTerm sl_cont
        return Select {sl_field = sl_field, sl_record = record, sl_cont = cont}
preprocessExpr Ir.If {Ir.if_test, Ir.if_csq, Ir.if_alt} =
    preprocessUTerm if_test $ \test -> do
        csq <- preprocessKTerm if_csq
        alt <- preprocessKTerm if_alt
        return If {if_test = test, if_csq = csq, if_alt = alt}
