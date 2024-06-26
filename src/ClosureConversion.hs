{-# LANGUAGE OverloadedStrings #-}

module ClosureConversion where

import Control.Applicative
import Control.Monad.Reader
import Control.Monad.Writer
import Data.Functor ((<&>))
import qualified Data.Map as Map
import Data.Map ((!))
import qualified Data.Set as Set
import Ir

-- | Make explicit all closures from a module.
-- Every ULambda generates a top-level function that accepts a record as its first argument.
-- Every top-level function also is modified to accept a record as its first argument.
-- Every ULambda gets t urned into a LiRecord that gathers the captured variables and names the top level function that was generated for the lambda.
-- Every UCall is wrapped in a select that fetches the actual function from the record before calling it, and passes the record as the first argument.
-- Every UVar refering to a top-level function is replaced with a LiRecord that refers to the top-level function.
convertClosures :: Module -> GenIdState Module
fnFieldName :: Symbol
fnFieldName = Symbol "$fn" 0

mapMWithKey :: Monad m => (k -> a -> m b) -> Map.Map k a -> m (Map.Map k b)
mapMWithKey f = unwrapMonad . Map.traverseWithKey (\k a -> WrapMonad (f k a))

convertClosures m = do
    (a, b) <- runWriterT $ mapM closureConvert (m_funcs m)
    return Module {m_funcs = Map.union a b}
  where
    closureConvert :: Lambda -> (WriterT (Map.Map Symbol Lambda) GenIdState) Lambda
    closureConvert lam = runReaderT (convertLambda Set.empty lam) Map.empty
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
                mapM (\n -> reader (\e -> (n, e ! n))) (Set.toList freeVars) <&> Map.fromList
                    . ((fnFieldName, lambdaType lam) :)
            let new_body =
                    foldl
                        (\inner var ->
                             Select
                                 { sl_record = UVar cloRecordName
                                 , sl_field = var
                                 , sl_cont =
                                       KLambda
                                           { kl_arg = Just (Binding var (cloRecordTy ! var))
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
        convertUTerm (ULambda l) = do
            fnName <- lift $ lift $ uniqueSym "@lambda"
            let freeVars = freeVariables l
            newLam <- convertLambda freeVars l
            tell $ Map.singleton fnName newLam
            return
                (LiRecord
                     $ Map.fromList
                     $ (fnFieldName, UVar fnName) : map (\v -> (v, UVar v)) (Set.toList freeVars))
        convertUTerm (LiRecord r) = do
            fields <- mapM convertUTerm r
            return $ LiRecord fields
        convertUTerm u = return u
        convertKTerm KLambda {kl_arg, kl_body} = do
            body <-
                local (maybe id (\(Binding n ty) -> Map.insert n ty) kl_arg) $ convertExpr kl_body
            return KLambda {kl_arg = kl_arg, kl_body = body}
        convertKTerm k = return k
        convertExpr UCall {uc_func, uc_args, uc_cont} = do
            fnTemp <- lift $ lift $ uniqueSym "$f"
            func <- convertUTerm uc_func
            funcTy <- utermType uc_func
            args <- mapM convertUTerm uc_args
            cont <- convertKTerm uc_cont
            return
                $ simplify
                      Select
                          { sl_field = fnFieldName
                          , sl_record = func
                          , sl_cont =
                                KLambda
                                    { kl_arg = Just $ Binding fnTemp funcTy
                                    , kl_body =
                                          UCall
                                              { uc_func = UVar fnTemp
                                              , uc_args = func : args
                                              , uc_cont = cont
                                              }
                                    }
                          }
        convertExpr KCall {kc_cont, kc_arg} = do
            cont <- convertKTerm kc_cont
            arg <- convertUTerm kc_arg
            return KCall {kc_cont = cont, kc_arg = arg}
        convertExpr Select {sl_field, sl_record, sl_cont} = do
            record <- convertUTerm sl_record
            cont <- convertKTerm sl_cont
            return Select {sl_field = sl_field, sl_record = record, sl_cont = cont}
        convertExpr If {if_test, if_csq, if_alt} = do
            test <- convertUTerm if_test
            csq <- convertKTerm if_csq
            alt <- convertKTerm if_alt
            return If {if_test = test, if_csq = csq, if_alt = alt}
