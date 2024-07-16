{-# LANGUAGE OverloadedStrings #-}

module XIr where

import Control.Monad.Reader
import Control.Monad.State
import Data.Functor ((<&>))
import Data.List (intercalate)
import qualified Data.Map as Map
import Data.Map ((!))
import Data.Maybe (fromMaybe, maybeToList)
import qualified Data.Text as T
import Ir (KType, UType(..), showPair)
import qualified Ir

data Symbol =
    Symbol T.Text Int
    deriving (Eq, Ord)

instance Show Symbol where
    show (Symbol text int) = T.unpack text ++ show int

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

newtype UTerm =
    UVar Symbol
    deriving (Eq)

instance Show UTerm where
    show (UVar sym) = show sym

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

data Lifetime
    = Unknown
    | Immediate
    | Stack
    | Heap
    deriving (Eq, Show)

data LiteralValue
    = LiInt Int
    | LiRecord (Map.Map T.Text UTerm)
    | ULambda Lambda
    deriving (Eq)

instance Show LiteralValue where
    show (LiInt i) = show i
    show (LiRecord rec) = "{ " ++ intercalate ", " (map showPair (Map.toList rec)) ++ " }"
    show (ULambda lambda) = show lambda

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

instance Show Expr where
    show (UCall func args cont) =
        show func ++ "(" ++ intercalate ", " (map show args) ++ ") " ++ "⟶ " ++ show cont
    show (Literal val lifetime cont) =
        show cont ++ " ← (" ++ show val ++ "'" ++ show lifetime ++ ")"
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

type PreprocessM a = ReaderT (Map.Map T.Text Int, Map.Map Ir.Symbol UType) (State Int) a

nextTempVar :: PreprocessM Symbol
nextTempVar = error "X"

convertSym :: Ir.Symbol -> PreprocessM Symbol
convertSym (Ir.Symbol s) = do
    i <- reader $ Map.lookup s . fst
    j <- get
    return (Symbol s (fromMaybe j i))

convertBinding :: Ir.Binding t -> PreprocessM (Binding t)
convertBinding (Ir.Binding name ty) = do
    n <- convertSym name
    return Binding {bindingName = n, bindingType = ty}

incrSymCounter :: PreprocessM ()
incrSymCounter = do
    i <- get
    put $ i + 1

inNewScope :: Maybe (Binding KType) -> [Binding UType] -> PreprocessM a -> PreprocessM a
inNewScope k_binding u_bindings m = incrSymCounter >> local updateEnv m
  where
    addBindingU (Binding (Symbol n i) t) (ei, et) =
        (Map.insert n i ei, Map.insert (Ir.Symbol n) t et)
    addBindingK (Binding (Symbol n i) _) (ei, et) = (Map.insert n i ei, et)
    updateEnv env = foldr addBindingU (foldr addBindingK env (maybeToList k_binding)) u_bindings

preprocess :: Ir.Module -> PreprocessM Module
preprocessLambda :: Ir.Lambda -> PreprocessM Lambda
preprocessExpr :: Ir.Expr -> PreprocessM Expr
preprocessUTerm :: Ir.UTerm -> (UTerm -> PreprocessM Expr) -> PreprocessM Expr
preprocessKTerm :: Ir.KTerm -> PreprocessM KTerm
preprocess (Ir.Module funcs) = mapM processTopLevel (Map.toList funcs) <&> (Module . Map.fromList)
  where
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

preprocessUTerm (Ir.UVar v) k = convertSym v >>= k . UVar
preprocessUTerm ut@(Ir.LiRecord record_fields) k = buildExpr (Map.toList record_fields) []
  where
    buildExpr :: [(T.Text, Ir.UTerm)] -> [(T.Text, UTerm)] -> PreprocessM Expr
    buildExpr [] resFields = do
        tmpVar <- nextTempVar
        innerNext <- k (UVar tmpVar)
        ty <- Ir.utermType (\s e -> snd e ! s) ut
        return
            $ Literal
                  { lt_val = LiRecord $ Map.fromList resFields
                  , lt_lifetime = Heap
                  , lt_cont = KLambda {kl_arg = Just (Binding tmpVar ty), kl_body = innerNext}
                  }
    buildExpr ((name, value):fields) resFields =
        preprocessUTerm value $ \cv -> buildExpr fields ((name, cv) : resFields)
preprocessUTerm ut k = do
    tmpVar <- nextTempVar
    inner <- k (UVar tmpVar)
    ty <- Ir.utermType (\s e -> snd e ! s) ut
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
