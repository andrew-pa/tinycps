{-# LANGUAGE OverloadedStrings #-}
module ClosureConversion where
import Ir
import qualified Data.Map as Map
import Control.Applicative
import Control.Monad.Writer
import qualified Data.Set as Set

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
    (a, b) <- runWriterT $ mapMWithKey closureConvert (m_funcs m)
    return Module {
        m_funcs = Map.union a b
    }
    where
    closureConvert :: Symbol -> Lambda -> WriterT (Map.Map Symbol Lambda) GenIdState Lambda
    closureConvert _ = convertLambda Set.empty
        where
            convertLambda freeVars  Lambda {l_args, l_cont, l_body} = do
                cloRecordName <- lift $ uniqueSym "$clo"
                body <- convertExpr l_body
                let new_body = foldl (\inner var -> Select {
                    sl_record = UVar cloRecordName,
                    sl_field = var,
                    sl_cont = KLambda { kl_arg = var, kl_body = inner }
                }) body freeVars
                return Lambda {
                    l_args = cloRecordName : l_args,
                    l_cont = l_cont,
                    l_body = new_body
                }

            convertUTerm (ULambda l) = do
                fnName <- lift $ uniqueSym "@lambda"
                let freeVars = freeVariables l
                newLam <- convertLambda freeVars l
                tell $ Map.singleton fnName newLam
                return (LiRecord $ Map.fromList $ (fnFieldName, UVar fnName) : map (\v -> (v, UVar v)) (Set.toList freeVars))
            convertUTerm (LiRecord r) = do
                fields <- mapM convertUTerm r
                return $ LiRecord fields
            convertUTerm u = return u

            convertKTerm KLambda { kl_arg, kl_body } = do
                body <- convertExpr kl_body
                return KLambda { kl_arg = kl_arg, kl_body = body }
            convertKTerm k = return k

            convertExpr UCall { uc_func, uc_args, uc_cont } = do
                fnTemp <- lift $ uniqueSym "$f"
                func <- convertUTerm uc_func
                args <- mapM convertUTerm uc_args
                cont <- convertKTerm uc_cont
                return $ simplify Select {
                    sl_field = fnFieldName,
                    sl_record = func,
                    sl_cont = KLambda {
                        kl_arg = fnTemp,
                        kl_body = UCall {
                            uc_func = UVar fnTemp,
                            uc_args = func : args,
                            uc_cont = cont
                        }
                    }
                }
            convertExpr KCall {kc_cont, kc_arg}= do
                cont <- convertKTerm kc_cont
                arg <- convertUTerm kc_arg
                return KCall {kc_cont=cont, kc_arg=arg}
            convertExpr Select {sl_field,sl_record,sl_cont} = do
                record <- convertUTerm sl_record
                cont <- convertKTerm sl_cont
                return Select { sl_field=sl_field, sl_record=record, sl_cont=cont }


