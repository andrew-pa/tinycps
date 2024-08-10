module EnvSpill where

import Control.Monad.Reader
import Control.Monad.State
import qualified Data.Map as Map
import Data.Maybe (fromJust)
import qualified Data.Set as Set
import qualified Data.Text as T
import Ext (splitRelation)
import Ir (UType(..))
import XIr

data SpillState
    = Direct
    | Spilled

todo :: a
todo = error "TODO"

spillEnvs :: Int -> Lambda -> State Int Lambda
spillEnvs maxVars Lambda {l_cont, l_body, l_args} = todo

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
    -> (Map.Map T.Text LiteralRecordValue, Map.Map T.Text UType)
generateSpillRecord v_before d'_union_u currentSpillRecord =
    splitRelation $ map processVar $ Set.toList v_before
  where
    s_c = maybe Map.empty fst currentSpillRecord
    s_v = fmap snd currentSpillRecord
    processVar v
        | Set.member v d'_union_u = (symToText v, (LRVUTerm $ UVar v, todo))
        | Map.member (symToText v) s_c =
            (symToText v, (LRVSelect (UVar $ fromJust s_v) (symToText v), todo))
        | otherwise = error "v not in d'_union_u or s_c but was before e"

spillExpr :: Cx -> Expr -> Expr
spillExpr Cx {maxVars, resultVars, currentSpillRecord, uniqulyBoundVars, duplicateVars} e =
    let rootArgs = exprOperands e
        v_before = runReader (freeInExpr e) Set.empty
        v_bound =
            foldr (\c s -> maybe s (`Set.insert` s) (boundSymbol c)) Set.empty (exprContinuations e)
        v_after = Set.unions $ map ((`runReader` Set.empty) . freeInKTerm) (exprContinuations e)
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
            then let dup_vars'' =
                         (uniqulyBoundVars `Set.union` dup_vars') `Set.intersection` v_before
                     newSpillRecordName = todo
                     (newSpillRecord, newSpillRecordType) =
                         generateSpillRecord
                             v_before
                             (Set.union dup_vars' uniqulyBoundVars)
                             currentSpillRecord
                     next =
                         spillExpr
                             Cx
                                 { maxVars = maxVars
                                 , resultVars = Set.empty
                                 , uniqulyBoundVars = Set.empty
                                 , duplicateVars = dup_vars''
                                 , currentSpillRecord =
                                       Just (newSpillRecordType, newSpillRecordName)
                                 }
                             e
                  in Literal
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
                  in case (currentSpillRecord, Set.size must_fetch) of
                         (_, 0) ->
                             let newCx =
                                     Cx
                                         { maxVars = maxVars
                                         , resultVars = v_bound
                                         , uniqulyBoundVars = uniqulyBoundVars `Set.union` v_after
                                         , duplicateVars = dup_vars'
                                         , currentSpillRecord =
                                               Just (s_after_c, Set.findMin s_after_v)
                                         }
                              in mapOverContinuationBodies e $ spillExpr newCx
                         (Just (s_c, s_v), n) ->
                             let v = Set.findMin must_fetch
                                 vType = s_c Map.! symToText v
                                 v' = todo
                              in Select
                                     { sl_record = UVar s_v
                                     , sl_field = symToText v
                                     , sl_cont =
                                           KLambda
                                               { kl_arg = Just $ Binding v' vType
                                               , kl_body =
                                                     spillExpr
                                                         Cx
                                                             { maxVars = maxVars
                                                             , resultVars = Set.empty
                                                             , uniqulyBoundVars =
                                                                   uniqulyBoundVars
                                                                       `Set.intersection` v_before
                                                             , duplicateVars =
                                                                   dup_vars'
                                                                       `Set.union` Set.singleton v'
                                                             , currentSpillRecord =
                                                                   if n == 1
                                                                       then Just
                                                                                ( s_after_c
                                                                                , Set.findMin
                                                                                      s_after_v)
                                                                       else currentSpillRecord
                                                             }
                                                         (subst v v' e)
                                               }
                                     }
                         _ -> error "no spill record but need to spill"
