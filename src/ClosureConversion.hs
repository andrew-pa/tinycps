{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TupleSections #-}

module ClosureConversion where

import Control.Applicative ()
import Control.Monad.Reader
import Control.Monad.Writer
import Data.Functor ((<&>))
import qualified Data.Map as Map
import Data.Map ((!))
import qualified Data.Set as Set
import qualified Data.Text as T
import Ext (GenIdState)
import Ir (UType(..))
import XIr

-- | Make explicit all closures from a module.
-- Every ULambda generates a top-level function that accepts a record as its first argument.
-- Every top-level function also is modified to accept a record as its first argument.
-- Every ULambda gets t urned into a LiRecord that gathers the captured variables and names the top level function that was generated for the lambda.
-- Every UCall is wrapped in a select that fetches the actual function from the record before calling it, and passes the record as the first argument.
-- Every UVar refering to a top-level function is replaced with a LiRecord that refers to the top-level function.
convertClosures :: Module -> GenIdState Module
fnFieldName :: T.Text
fnFieldName = "$fn"

convertClosures m = do
    (a, b) <- runWriterT $ mapM closureConvert (m_funcs m)
    return Module {m_funcs = Map.union a b}
  where
    closureConvert :: Lambda -> (WriterT (Map.Map Symbol Lambda) GenIdState) Lambda
    closureConvert theLambda = runReaderT (convertLambda Set.empty theLambda) Map.empty
      where
        convertLambda ::
               Set.Set Symbol
            -> Lambda
            -> ReaderT (Map.Map Symbol UType) (WriterT (Map.Map Symbol Lambda) GenIdState) Lambda
        convertLambda freeVars lam@Lambda {l_args, l_cont, l_body} = do
            cloRecordName <- lift $ lift $ uniqueSym "$clo"
            body <-
                local (Map.union (Map.fromList $ map (\(Binding n ty) -> (n, ty)) l_args))
                    $ convertExpr l_body
            cloRecordTy <-
                mapM (\n@(Symbol nn _) -> reader (\e -> (nn, e ! n))) (Set.toList freeVars)
                    <&> (Map.fromList . ((fnFieldName, lambdaType lam) :))
            let new_body =
                    foldl
                        (\inner var@(Symbol varName _) ->
                             Select
                                 { sl_record = UVar cloRecordName
                                 , sl_field = varName
                                 , sl_cont =
                                       KLambda
                                           { kl_arg = Just (Binding var (cloRecordTy ! varName))
                                           , kl_body = inner
                                           }
                                 })
                        body
                        freeVars
            return
                Lambda
                    { l_args = Binding cloRecordName (TyRecord cloRecordTy) : l_args
                    , l_cont = l_cont
                    , l_body = new_body
                    }
        convertKTerm KLambda {kl_arg, kl_body} = do
            body <-
                local (maybe id (\(Binding n ty) -> Map.insert n ty) kl_arg) $ convertExpr kl_body
            return KLambda {kl_arg = kl_arg, kl_body = body}
        convertKTerm k = return k
        convertExpr (Literal (ULambda lam) lifetime cont) = do
            fnName <- lift $ lift $ uniqueSym "@lambda"
            fnTmpName <- lift $ lift $ uniqueSym "tmp"
            let freeVars = freeVariables lam
            newLam <- convertLambda freeVars lam
            tell $ Map.singleton fnName newLam
            let record =
                    (fnFieldName, UVar fnTmpName)
                        : map (\v@(Symbol vName _) -> (vName, UVar v)) (Set.toList freeVars)
            let fnTy = lambdaType lam
            k <- convertKTerm cont
            let createRecordE =
                    Literal
                        { lt_val = LiRecord . Map.fromList $ record
                        , lt_lifetime = lifetime
                        , lt_cont = k
                        }
            return
                $ Literal
                      { lt_val = TopLevelRef fnName
                      , lt_lifetime = Immediate
                      , lt_cont =
                            KLambda
                                {kl_arg = Just (Binding fnTmpName fnTy), kl_body = createRecordE}
                      }
        convertExpr (Literal val lifetime cont) = do
            k <- convertKTerm cont
            return $ Literal {lt_val = val, lt_lifetime = lifetime, lt_cont = k}
        convertExpr UCall {uc_func, uc_args, uc_cont} = do
            fnTemp <- lift $ lift $ uniqueSym "$f"
            funcTy <- reader (! utermAsSymbol uc_func)
            cont <- convertKTerm uc_cont
            return
                $ -- simplify
                 Select
                     { sl_field = fnFieldName
                     , sl_record = uc_func
                     , sl_cont =
                           KLambda
                               { kl_arg = Just $ Binding fnTemp funcTy
                               , kl_body =
                                     UCall
                                         { uc_func = UVar fnTemp
                                         , uc_args = uc_func : uc_args
                                         , uc_cont = cont
                                         }
                               }
                     }
        convertExpr KCall {kc_cont, kc_arg} = do
            cont <- convertKTerm kc_cont
            return KCall {kc_cont = cont, kc_arg = kc_arg}
        convertExpr Select {sl_field, sl_record, sl_cont} = do
            cont <- convertKTerm sl_cont
            return Select {sl_field = sl_field, sl_record = sl_record, sl_cont = cont}
        convertExpr If {if_test, if_csq, if_alt} = do
            csq <- convertKTerm if_csq
            alt <- convertKTerm if_alt
            return If {if_test = if_test, if_csq = csq, if_alt = alt}
