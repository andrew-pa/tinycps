module Ir where
import qualified Data.Text as T
import qualified Data.Map as Map
import Data.Map ((!))
import Control.Monad.State
import qualified Data.Set as Set
import Control.Monad.Reader (runReader, reader, MonadReader (local), Reader, ReaderT)
import Data.Functor ((<&>))
import Data.Maybe (fromMaybe)
import Data.List (intercalate)
import Debug.Trace (traceShowM)

showPair :: Show a=>Show b=>(a,b) -> String
showPair (k, v) = show k ++ ": " ++ show v

data Symbol = Symbol T.Text Int deriving(Eq, Ord)

instance Show Symbol where
    show (Symbol text int) = T.unpack text ++ show int

data UType = TyInt | TyRecord (Map.Map Symbol UType) | TyFn [UType] KType deriving(Eq)
instance Show UType where
    show TyInt = "int"
    show (TyRecord fields) = "{ " ++ intercalate ", " (map showPair $ Map.toList fields) ++ " }"
    show (TyFn args cont) = "(" ++ intercalate ", " (map show args) ++ ")->" ++ show cont
newtype KType = TyCont (Maybe UType) deriving(Eq)
instance Show KType where
    show (TyCont Nothing) = "^()"
    show (TyCont (Just ty)) = "^" ++show ty

data Binding ty = Binding { bindingName :: Symbol, bindingType :: ty } deriving(Eq)
instance (Show t) => Show (Binding t) where
    show (Binding sym ty) = showPair (sym,ty)

data Lambda = Lambda {
        l_args :: [Binding UType],
        l_cont :: Binding KType,
        l_body :: Expr
    }
    deriving (Eq)

lambdaType :: Lambda -> UType
lambdaType Lambda { l_args, l_cont, l_body = _ } = TyFn (map bindingType l_args) (bindingType l_cont)

instance Show Lambda where
    show (Lambda args cont body) =
        "λ(" ++ intercalate ", " (map show args) ++ " ⟶ " ++ show cont ++ ") { " ++ show body ++ " }"

data UTerm =
    UVar Symbol
    | LiInt Int
    | LiRecord (Map.Map Symbol UTerm)
    | ULambda Lambda
    deriving (Eq)

utermType :: (Monad m) => UTerm -> ReaderT (Map.Map Symbol UType) m UType
utermType (UVar v) = reader (! v)
utermType (LiInt _) = return TyInt
utermType (LiRecord fields) = do
    fieldTypes <- mapM utermType fields
    return $ TyRecord fieldTypes
utermType (ULambda lam) = return $ lambdaType lam

instance Show UTerm where
    show (UVar sym) = show sym
    show (LiInt i) = show i
    show (LiRecord rec) = "{ " ++ intercalate ", " (map showPair (Map.toList rec)) ++ " }"
    show (ULambda lambda) = show lambda

data KTerm =
    KVar Symbol
    | KLambda {
        kl_arg :: Maybe (Binding UType),
        kl_body :: Expr
    }
    deriving (Eq)

instance Show KTerm where
    show (KVar sym) = show sym
    show (KLambda (Just arg) body) = "κ" ++ show arg ++ " {" ++ show body ++ "}"
    show (KLambda Nothing body) = "κ {" ++ show body ++ "}"

data Expr =
    UCall {
        uc_func :: UTerm,
        uc_args :: [UTerm],
        uc_cont :: KTerm
    }
    | KCall {
        kc_cont :: KTerm,
        kc_arg  :: UTerm
    }
    | Select {
        sl_field :: Symbol,
        sl_record :: UTerm,
        sl_cont :: KTerm
    }
    | If {
        if_test :: UTerm,
        if_csq  :: KTerm,
        if_alt  :: KTerm
    }
    deriving (Eq)

instance Show Expr where
    show (UCall func args cont) =
        show func ++ "(" ++ intercalate ", " (map show args) ++ ") " ++ "⟶ " ++ show cont
    show (KCall cont arg) =
        show cont ++ " ← (" ++ show arg ++ ")"
    show (Select field record cont) =
        show record ++ "." ++ show field ++ " ⟶ " ++ show cont
    show (If tst csq alt) =
        "if " ++ show tst ++ " then " ++ show csq ++ " else " ++ show alt

newtype Module = Module {
    m_funcs :: Map.Map Symbol Lambda
}
    deriving (Eq)

instance Show Module where
    show (Module funcs) =
        "Module {\n" ++ unlines (map showFunc (Map.toList funcs)) ++ "}"
        where showFunc (name, lambda) = show name ++ " = " ++ show lambda

collectOverTerms :: (Monad m) => (Monoid r) => (UTerm -> m r) -> (KTerm -> m r) -> Expr -> m r
collectOverTerms inUTerm inKTerm e = case e of
    UCall { uc_func, uc_args, uc_cont } -> do
        inCont <- inKTerm uc_cont
        inArgs <- mapM inUTerm (uc_func : uc_args)
        return (mconcat $ inCont : inArgs)
    KCall { kc_cont, kc_arg } -> do
        inCont <- inKTerm kc_cont
        inArg <- inUTerm kc_arg
        return (mappend inCont inArg)
    Select { sl_record, sl_cont } -> do
        inCont <- inKTerm sl_cont
        inArg <- inUTerm sl_record
        return (mappend inCont inArg)
    If { if_test, if_csq, if_alt } -> do
        inTest <- inUTerm if_test
        inCsq <- inKTerm if_csq
        inAlt <- inKTerm if_alt
        return (mconcat [inTest, inCsq, inAlt])

freeVariables :: Lambda -> Set.Set Symbol
freeVariables Lambda {l_args, l_cont, l_body} =
    runReader (freeInExpr l_body) (argsToSet l_args)
    where
    argsToSet = Set.fromList . map bindingName
    freeInExpr = collectOverTerms freeInUTerm freeInKTerm
    freeInKTerm (KVar _) = return Set.empty
    freeInKTerm KLambda { kl_arg = Just argName, kl_body } =
        local (Set.insert (bindingName argName)) (freeInExpr kl_body)
    freeInKTerm KLambda { kl_arg = Nothing, kl_body } = freeInExpr kl_body

    freeInUTerm :: UTerm -> Reader (Set.Set Symbol) (Set.Set Symbol)
    freeInUTerm (UVar v) = do
        bound <- reader $ Set.member v
        return (if bound then Set.empty else Set.singleton v)
    freeInUTerm (LiInt _) = return Set.empty
    freeInUTerm (LiRecord fields) = mapM freeInUTerm fields <&> Set.unions
    freeInUTerm (ULambda Lambda { l_args, l_cont, l_body }) =
        local (Set.union $ argsToSet l_args) (freeInExpr l_body)

substInExprU :: Expr -> Reader (Symbol -> Maybe UTerm) Expr
substInExprK :: Expr -> Reader (Symbol -> Maybe KTerm) Expr

mapTermsInExpr :: (Monad m) => (UTerm -> m UTerm) -> (KTerm -> m KTerm) -> Expr -> m Expr
mapTermsInExpr mapUTerm mapKTerm e = case e of
    KCall {kc_cont, kc_arg} -> do
        cont <- mapKTerm kc_cont
        arg <- mapUTerm kc_arg
        return KCall {kc_cont=cont, kc_arg=arg}
    UCall{uc_func,uc_args,uc_cont} -> do
        func <- mapUTerm uc_func
        args <- mapM mapUTerm uc_args
        cont <- mapKTerm uc_cont
        return UCall{uc_func=func,uc_args=args,uc_cont=cont}
    Select{sl_field, sl_record,sl_cont} -> do
        record <- mapUTerm sl_record
        cont <- mapKTerm sl_cont
        return Select{sl_field=sl_field,sl_record=record,sl_cont=cont}
    If{if_test,if_csq,if_alt} -> do
        test <- mapUTerm if_test
        csq  <- mapKTerm if_csq
        alt  <- mapKTerm if_alt
        return If{if_test=test,if_csq=csq,if_alt=alt}

substInExprU = mapTermsInExpr substInUTerm substInKTerm
    where
    substInKTerm KLambda { kl_arg, kl_body } = do
        body <- substInExprU kl_body
        return KLambda { kl_arg, kl_body=body }
    substInKTerm t = return t

    substInUTerm t@(UVar s) = do
        sub <- reader (\m -> m s)
        return $ fromMaybe t sub
    substInUTerm (LiRecord fields) = do
        newFields <- mapM substInUTerm fields
        return $ LiRecord newFields
    substInUTerm (ULambda Lambda {l_args, l_cont, l_body}) = do
        body <- substInExprU l_body
        return $ ULambda Lambda { l_args=l_args, l_cont=l_cont, l_body=body }
    substInUTerm t = return t

substInExprK = mapTermsInExpr substInUTerm substInKTerm
    where
    substInKTerm KLambda { kl_arg, kl_body } = do
        body <- substInExprK kl_body
        return KLambda { kl_arg, kl_body=body }
    substInKTerm t@(KVar s) = do
        sub <- reader (\m -> m s)
        return $ fromMaybe t sub

    substInUTerm (LiRecord fields) = do
        newFields <- mapM substInUTerm fields
        return $ LiRecord newFields
    substInUTerm (ULambda Lambda {l_args, l_cont, l_body}) = do
        body <- substInExprK l_body
        return $ ULambda Lambda { l_args=l_args, l_cont=l_cont, l_body=body }
    substInUTerm t = return t

mapToFn :: Ord k => Map.Map k v -> (k -> Maybe v)
mapToFn = flip Map.lookup

simplify :: Expr -> Expr
simplify UCall { uc_func = (ULambda Lambda { l_args, l_cont, l_body }), uc_args, uc_cont } =
    runReader (substInExprK (runReader (substInExprU l_body) (mapToFn $ Map.fromList $ zip (map bindingName l_args) uc_args))) (mapToFn $ Map.singleton (bindingName l_cont) uc_cont)
simplify KCall { kc_cont = (KLambda { kl_arg = Just argName, kl_body }), kc_arg } =
    runReader (substInExprU kl_body) (mapToFn $ Map.singleton (bindingName argName) kc_arg)
simplify Select { sl_field, sl_record = LiRecord fields, sl_cont = KLambda { kl_arg = Just argName, kl_body } }
    | Map.member sl_field fields = runReader (substInExprU kl_body) (mapToFn $ Map.singleton (bindingName argName) $ fields Map.! sl_field)
-- so long as we have no side-effects
simplify UCall { uc_func = _, uc_args = _, uc_cont = KLambda { kl_arg = Nothing, kl_body } } =
    kl_body
simplify Select { sl_field = _, sl_record = _, sl_cont = KLambda { kl_arg = Nothing, kl_body } } =
    kl_body
simplify e = e


type GenIdState = State Int
uniqueSym :: String -> GenIdState Symbol
uniqueSym s = do
    i <- get
    put $ i + 1
    return (Symbol (T.pack s) i)
