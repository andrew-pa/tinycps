module Ir where
import qualified Data.Text as T
import qualified Data.Map as Map
import Control.Monad.State
import qualified Data.Set as Set
import Control.Monad.Reader (runReader, reader, MonadReader (local), Reader)
import Data.Functor ((<&>))
import Data.Maybe (fromMaybe)
import Data.List (intercalate)

data Symbol = Symbol T.Text Int deriving(Eq, Ord)

instance Show Symbol where
    show (Symbol text int) = T.unpack text ++ show int

data Lambda = Lambda {
        l_args :: [Symbol],
        l_cont :: Symbol,
        l_body :: Expr
    }
    deriving (Eq)

instance Show Lambda where
    show (Lambda args cont body) =
        "λ(" ++ unwords (map show args) ++ " ⟶ " ++ show cont ++ ") {" ++ show body ++ "}"

data UTerm =
    UVar Symbol
    | LiInt Int
    | LiRecord (Map.Map Symbol UTerm)
    | ULambda Lambda
    deriving (Eq)

instance Show UTerm where
    show (UVar sym) = show sym
    show (LiInt i) = show i
    show (LiRecord rec) = "{" ++ intercalate ", " (map showPair (Map.toList rec)) ++ "}"
        where showPair (k, v) = show k ++ ": " ++ show v
    show (ULambda lambda) = show lambda

data KTerm =
    KVar Symbol
    | KLambda {
        kl_arg :: Maybe Symbol,
        kl_body :: Expr
    }
    deriving (Eq)

instance Show KTerm where
    show (KVar sym) = show sym
    show (KLambda arg body) = "κ" ++ show arg ++ " {" ++ show body ++ "}"

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
        show func ++ "(" ++ unwords (map show args) ++ ") " ++ "⟶ " ++ show cont
    show (KCall cont arg) =
        show cont ++ "← (" ++ show arg ++ ")"
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

freeVariables :: Lambda -> Set.Set Symbol
freeVariables Lambda {l_args, l_cont, l_body} =
    runReader (freeInExpr l_body) (Set.fromList $ l_cont : l_args)
    where
    freeInKTerm (KVar v) = do
        bound <- reader $ Set.member v
        return (if bound then Set.empty else Set.singleton v)
    freeInKTerm KLambda { kl_arg = Just argName, kl_body } = local (Set.insert argName) (freeInExpr kl_body)
    freeInKTerm KLambda { kl_arg = Nothing, kl_body } = freeInExpr kl_body

    freeInUTerm :: UTerm -> Reader (Set.Set Symbol) (Set.Set Symbol)
    freeInUTerm (UVar v) = do
        bound <- reader $ Set.member v
        return (if bound then Set.empty else Set.singleton v)
    freeInUTerm (LiInt _) = return Set.empty
    freeInUTerm (LiRecord fields) = mapM freeInUTerm fields <&> Set.unions
    freeInUTerm (ULambda Lambda { l_args, l_cont, l_body }) =
        local (Set.union $ Set.fromList (l_cont : l_args)) (freeInExpr l_body)

    freeInExpr UCall { uc_func, uc_args, uc_cont } = do
        freeInCont <- freeInKTerm uc_cont
        freeInArgs <- mapM freeInUTerm (uc_func : uc_args)
        return (Set.unions $ freeInCont : freeInArgs)
    freeInExpr KCall { kc_cont, kc_arg } = do
        freeInCont <- freeInKTerm kc_cont
        freeInArg <- freeInUTerm kc_arg
        return (Set.union freeInCont freeInArg)
    freeInExpr Select { sl_record, sl_cont } = do
        freeInCont <- freeInKTerm sl_cont
        freeInArg <- freeInUTerm sl_record
        return (Set.union freeInCont freeInArg)
    freeInExpr If { if_test, if_csq, if_alt } = do
        freeInTest <- freeInUTerm if_test
        freeInCsq <- freeInKTerm if_csq
        freeInAlt <- freeInKTerm if_alt
        return (Set.unions [freeInTest, freeInCsq, freeInAlt])

substInExprU :: Expr -> Reader (Symbol -> Maybe UTerm) Expr
substInExprK :: Expr -> Reader (Symbol -> Maybe KTerm) Expr

mapTermsInExpr :: (Monad m) => (UTerm -> m UTerm) -> (KTerm -> m KTerm) -> Expr -> m Expr
mapTermsInExpr substInUTerm substInKTerm e = case e of
    KCall {kc_cont, kc_arg} -> do
        cont <- substInKTerm kc_cont
        arg <- substInUTerm kc_arg
        return KCall {kc_cont=cont, kc_arg=arg}
    UCall{uc_func,uc_args,uc_cont} -> do
        func <- substInUTerm uc_func
        args <- mapM substInUTerm uc_args
        cont <- substInKTerm uc_cont
        return UCall{uc_func=func,uc_args=args,uc_cont=cont}
    Select{sl_field, sl_record,sl_cont} -> do
        record <- substInUTerm sl_record
        cont <- substInKTerm sl_cont
        return Select{sl_field=sl_field,sl_record=record,sl_cont=cont}
    If{if_test,if_csq,if_alt} -> do
        test <- substInUTerm if_test
        csq  <- substInKTerm if_csq
        alt  <- substInKTerm if_alt
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
    runReader (substInExprK (runReader (substInExprU l_body) (mapToFn $ Map.fromList $ zip l_args uc_args))) (mapToFn $ Map.singleton l_cont uc_cont)
simplify KCall { kc_cont = (KLambda { kl_arg = Just argName, kl_body }), kc_arg } =
    runReader (substInExprU kl_body) (mapToFn $ Map.singleton argName kc_arg)
simplify Select { sl_field, sl_record = LiRecord fields, sl_cont = KLambda { kl_arg = Just argName, kl_body } }
    | Map.member sl_field fields = runReader (substInExprU kl_body) (mapToFn $ Map.singleton argName $ fields Map.! sl_field)
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
