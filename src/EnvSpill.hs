module EnvSpill where

import Control.Monad.Reader
import Control.Monad.State
import Data.Functor ((<&>))
import qualified Data.Map as Map
import Data.Maybe (fromJust)
import qualified Data.Set as Set
import qualified Data.Text as T
import Debug.Trace (trace, traceM)
import Ext (GenIdState, incrSymCounter, splitRelation)
import Ir (UType(..))
import XIr

todo :: a
todo = error "TODO"

spillEnvs :: Int -> Module -> GenIdState Module
spillEnvs maxVars (Module {m_funcs}) = do
    funcs <- mapM (spillLambda maxVars) m_funcs
    return Module {m_funcs = funcs}

spillLambda :: Int -> Lambda -> State Int Lambda
spillLambda maxVars Lambda {l_cont, l_body, l_args} = do
    body <-
        runReaderT
            (spillExpr
                 Cx
                     { maxVars = maxVars
                     , resultVars = Set.empty
                     , currentSpillRecord = Nothing
                     , uniqulyBoundVars = Set.fromList $ map bindingName l_args
                     , duplicateVars = Set.empty
                     }
                 l_body)
            (Map.fromList $ map (\(Binding n t) -> (n, t)) l_args)
    return Lambda {l_cont = l_cont, l_args = l_args, l_body = body}

data Cx = Cx
    { maxVars :: Int
    , resultVars :: Set.Set Symbol
    , currentSpillRecord :: Maybe (Map.Map T.Text UType, Symbol)
    , uniqulyBoundVars :: Set.Set Symbol
    , duplicateVars :: Set.Set Symbol
    }

computeSBeforeAfterIfThereIsASpillRecord ::
       Set.Set Symbol
    -> (Map.Map T.Text UType, Symbol)
    -> (Set.Set Symbol, Set.Set Symbol, Map.Map T.Text UType)
computeSBeforeAfterIfThereIsASpillRecord v_after (fields, name) =
    let s_c_intersect_v_after_is_null =
            Set.null (Map.keysSet fields `Set.intersection` Set.map symToText v_after)
     in ( Set.singleton name -- s_before
        , if s_c_intersect_v_after_is_null
              then Set.empty
              else Set.singleton name -- s_after_v
        , if s_c_intersect_v_after_is_null
              then Map.empty
              else fields -- s_after_c
         )

generateSpillRecord ::
       Set.Set Symbol
    -> Set.Set Symbol
    -> Maybe (Map.Map T.Text UType, Symbol)
    -> ReaderT
           (Map.Map Symbol UType)
           (State Int)
           (Map.Map T.Text LiteralRecordValue, Map.Map T.Text UType)
generateSpillRecord v_before d'_union_u currentSpillRecord =
    mapM processVar (Set.toList v_before) <&> splitRelation
  where
    s_c = maybe Map.empty fst currentSpillRecord
    s_v = fmap snd currentSpillRecord
    processVar v
        | Set.member v d'_union_u = do
            ty <- reader (Map.! v)
            return (vtxt, (LRVUTerm $ UVar v, ty))
        | Map.member vtxt s_c =
            return (vtxt, (LRVSelect (UVar $ fromJust s_v) vtxt, s_c Map.! vtxt))
        | otherwise = error "v not in d'_union_u or s_c but was before e"
      where
        vtxt = symToText v

spillExpr :: Cx -> Expr -> ReaderT (Map.Map Symbol UType) (State Int) Expr
spillExpr Cx {maxVars, resultVars, currentSpillRecord, uniqulyBoundVars, duplicateVars} e =
    let rootArgs = exprOperands e
        v_before = runReader (freeInExpr e) Set.empty
        v_bound =
            foldr (\c s -> maybe s (`Set.insert` s) (boundSymbol c)) Set.empty (exprContinuations e)
        v_after = Set.unions $ v_bound : map ((`runReader` Set.empty) . freeInKTerm) (exprContinuations e)
        (s_before, s_after_v, s_after_c) =
            maybe
                (Set.empty, Set.empty, Map.empty)
                (computeSBeforeAfterIfThereIsASpillRecord v_after)
                currentSpillRecord
        n_dup =
            maxVars
                - Set.size s_before
                - Set.size (Set.union (uniqulyBoundVars `Set.intersection` v_before) resultVars)
        dup_vars'_start = (duplicateVars `Set.intersection` v_before)
        dup_vars' =
            dup_vars'_start
                `Set.difference` Set.fromList
                                     (take (max 0 (Set.size dup_vars'_start - n_dup))
                                          $ reverse
                                          $ variablesByFirstOccurenceInExpr e)
        n_rem = maxVars - Set.size s_after_v
        uniquly_bound_leftovers = Set.intersection uniqulyBoundVars v_after
     in if Set.size (rootArgs `Set.union` uniquly_bound_leftovers) > n_rem
               || Set.size (v_bound `Set.union` uniquly_bound_leftovers) > n_rem
            then do
                let dup_vars'' =
                        (uniqulyBoundVars `Set.union` dup_vars') `Set.intersection` v_before
                traceM
                    ("\n(new spill record: Nd="
                         ++ show n_dup
                         ++ " Nr=" ++ show n_rem
                         ++ " rA=" ++ show (Set.toList rootArgs)
                         ++ "| " ++ show (Set.toList v_before)
                         ++ "+" ++ show (Set.toList v_bound)
                         ++ "->"
                         ++ show (Set.toList v_after)
                         ++ " ubl=" ++ show (Set.toList uniquly_bound_leftovers)
                         ++ " D''=" ++ show (Set.toList dup_vars'')
                         ++ ")")
                newSpillRecordName <- lift incrSymCounter <&> Symbol (T.pack "$spill")
                (newSpillRecord, newSpillRecordType) <-
                    generateSpillRecord
                        v_before
                        (Set.union dup_vars' uniqulyBoundVars)
                        currentSpillRecord
                next <-
                    spillExpr
                        Cx
                            { maxVars = maxVars
                            , resultVars = Set.empty
                            , uniqulyBoundVars = Set.empty
                            , duplicateVars = dup_vars''
                            , currentSpillRecord = Just (newSpillRecordType, newSpillRecordName)
                            }
                        e
                return
                    Literal
                        { lt_val = LiRecord newSpillRecord
                        , lt_lifetime = Unknown
                        , lt_cont =
                              KLambda
                                  { kl_arg =
                                        Just
                                            $ Binding
                                                  newSpillRecordName
                                                  (TyRecord newSpillRecordType)
                                  , kl_body = next
                                  }
                        }
            else let must_fetch = rootArgs `Set.difference` (uniqulyBoundVars `Set.union` dup_vars')
                  in case 
                     {-trace
                              ("\n(fetch) "
                                   ++ show e
                                   ++ ": "
                                   ++ show (Set.toList must_fetch)
                                   ++ " spill record: "
                                   ++ show currentSpillRecord
                                   ++ " rootArgs="
                                   ++ show (Set.toList rootArgs)
                                   ++ " uBV="
                                   ++ show (Set.toList uniqulyBoundVars)
                                   ++ " D="
                                   ++ show (Set.toList dup_vars')
                                   ++ " Vb="
                                   ++ show (Set.toList v_bound)
                                   ++ " Va="
                                   ++ show (Set.toList v_after)
                                   ++ " R="
                                   ++ show (Set.toList resultVars)
                                   ++ "(fetch)") -}
                              (currentSpillRecord, Set.size must_fetch) of
                         (_, 0) ->
                             let newCx =
                                     Cx
                                         { maxVars = maxVars
                                         , resultVars = v_bound
                                         , uniqulyBoundVars = uniqulyBoundVars `Set.union` v_after
                                         , duplicateVars = dup_vars'
                                         , currentSpillRecord =
                                               if Set.size s_after_v > 0
                                                   then Just (s_after_c, Set.findMin s_after_v)
                                                   else Nothing
                                         }
                              in mapOverContinuationBodies e $ spillExpr newCx
                         (Just (s_c, s_v), n) -> do
                             let v = Set.findMin must_fetch
                             let vType = s_c Map.! symToText v
                             v' <- lift incrSymCounter <&> Symbol (symbolName v)
                             body <-
                                 spillExpr
                                     Cx
                                         { maxVars = maxVars
                                         , resultVars = Set.empty
                                         , uniqulyBoundVars =
                                               uniqulyBoundVars `Set.intersection` v_before
                                         , duplicateVars = dup_vars' `Set.union` Set.singleton v'
                                         , currentSpillRecord =
                                               if n == 1
                                                   then Just (s_after_c, Set.findMin s_after_v)
                                                   else currentSpillRecord
                                         }
                                     (subst (Map.singleton v (UVar v')) e)
                             return
                                 Select
                                     { sl_record = UVar s_v
                                     , sl_field = symToText v
                                     , sl_cont =
                                           KLambda
                                               {kl_arg = Just $ Binding v' vType, kl_body = body}
                                     }
                         _ -> error "no spill record but need to spill"
