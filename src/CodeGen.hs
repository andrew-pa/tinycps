{-# LANGUAGE OverloadedStrings #-}

module CodeGen where

import Control.Monad.State
import Control.Monad.Writer
import qualified Data.Map as Map
import Data.Maybe (isNothing)
import qualified Data.Set as Set
import Ext (localState, localStateWithContext)
import Ir

-- CPS to instructions
-- figure out register allocation, instruction sequence, calling convention
-- leave tag manipulation, instruction selection, jump calculation to assembler
newtype Register =
    Reg Int
    deriving (Eq, Show, Ord)

data VarAssignment =
    VarAssign (Map.Map Symbol Register) (Set.Set Register)

nextFreeRegister :: VarAssignment -> Register
nextFreeRegister (VarAssign _ free) = Set.findMin free

assignVariable :: Binding UType -> Register -> VarAssignment -> VarAssignment
assignVariable s r (VarAssign assigned free) =
    VarAssign (Map.insert (bindingName s) r assigned) (Set.delete r free)

reserveTemporary :: VarAssignment -> (VarAssignment, Register)
reserveTemporary (VarAssign assigned free) =
    let fr = Set.findMin free
     in (VarAssign assigned $ Set.delete fr free, fr)

lookupAssignment :: Symbol -> VarAssignment -> Maybe Register
lookupAssignment s (VarAssign assigned _) = Map.lookup s assigned

swapAssignment :: Symbol -> Register -> VarAssignment -> Writer [Instr] VarAssignment
-- Ensure that previously assigned `s` is now assigned the register `r`. If `r` is in use, the variable using `r` will now use the register previously assigned to `s`.
-- To do so, it may be necessary to emit some instructions to manipulate the registers.
swapAssignment s r = error "TODO"

-- makeArgumentRegistersAvailable :: Set.Set Register -> Set.Set Symbol -> GenM VarAssignment
-- makeArgumentRegistersAvailable requiredArgumentRegisters retainedVariables = do
--     VarAssign currentAssigned currentFree <- ask
--     let availableFree = Set.difference currentFree (Set.fromList requiredArgumentRegisters)
data MachineDesc = MachineDesc
    { numRegisters :: Int
    , argumentVariableAssignment :: [Symbol] -> VarAssignment
    , returnRegister :: Register
    , argumentRegisters :: [Register]
    }

data Condition
    = Always
    | EqualZero Register
    deriving (Eq, Show)

data Instr
    = Label Int
    | Jump Condition Int
    | Call Register
    | Return
    | LoadField Register Int Register
    | StoreField Register Int Register
    | LoadImm Register Int
    | CreateRecord Register Int
    | Move Register Register
    | Swap Register Register
    | LoadAddressOf Symbol Register
    deriving (Eq, Show)

type GenM = StateT VarAssignment (Writer [Instr])

codeGen :: MachineDesc -> Module -> Map.Map Symbol [Instr]
codeGen machineDesc mod = fmap codeGenFn (m_funcs mod)
  where
    codeGenFn :: Lambda -> [Instr]
    codeGenFn Lambda {l_cont = top_level_return_continuation, l_body, l_args} =
        execWriter
            $ evalStateT
                  (codeGenExpr l_body)
                  (argumentVariableAssignment machineDesc $ map bindingName l_args)
      where
        top_level_return_continuation_name = bindingName top_level_return_continuation
        codeGenExpr :: Expr -> GenM ()
        -- given a term and a register, emit code that places the value of the term in that register
        codeGenUTerm :: UTerm -> Register -> GenM ()
        codeGenUTermAnyDest :: UTerm -> (Register -> GenM a) -> GenM a
        -- given a term and a register, emit code that executes the continuation with the value in the register as the result of the previous computation
        codeGenKTerm :: KTerm -> Maybe Register -> GenM ()
        nextLabel :: GenM Int
        nextLabel = return 0
        fieldOffsetForRecord :: Symbol -> UTerm -> GenM Int
        fieldOffsetForRecord _ _ = return 0
        codeGenUTerm (UVar x) dstReg =
            case Map.lookup x (m_funcs mod) of
                Just _ -> tell [LoadAddressOf x dstReg]
                Nothing -> do
                    r <- gets $ lookupAssignment x
                    case r of
                        Just srcReg ->
                            if srcReg == dstReg
                                then return ()
                                else tell [Move srcReg dstReg]
                        Nothing -> error "unexpected free variable"
        codeGenUTerm (LiInt v) reg = do
            tell [LoadImm reg v]
        codeGenUTerm rec@(LiRecord fields) recordReg = do
            tell [CreateRecord recordReg (Map.size fields)]
            void
                (Map.traverseWithKey
                     (\k v -> do
                          offset <- fieldOffsetForRecord k rec
                          codeGenUTermAnyDest v $ \r -> tell [StoreField recordReg offset r])
                     fields)
        codeGenUTerm (ULambda _) _ = error "must closure convert first"
        codeGenUTermAnyDest (UVar v) k
            | isNothing $ Map.lookup v (m_funcs mod) = do
                maybeReg <- gets $ lookupAssignment v
                case maybeReg of
                    Just r -> k r
                    Nothing -> error "unexpected free variable"
        codeGenUTermAnyDest t k =
            localStateWithContext
                reserveTemporary
                (\tmpReg -> do
                     codeGenUTerm t tmpReg
                     k tmpReg)
        codeGenKTerm (KVar v) (Just resReg)
            | v == top_level_return_continuation_name =
                if resReg == returnRegister machineDesc
                    then tell [Return]
                    else tell [Move resReg (returnRegister machineDesc), Return]
            | otherwise = error "TODO: call non-return cont"
        codeGenKTerm (KVar v) Nothing
            | v == top_level_return_continuation_name = tell [Return]
            | otherwise = error "TODO: call non-return cont"
        codeGenKTerm (KLambda {kl_arg, kl_body}) resReg =
            case (kl_arg, resReg) of
                (Just arg, Just reg) -> localState (assignVariable arg reg) $ codeGenExpr kl_body
                (Nothing, Nothing) -> codeGenExpr kl_body
                _ -> error "continuation result arity mismatch"
        codeGenExpr UCall {uc_func, uc_args, uc_cont} = do
            -- evaluate all arguments, placing them in argument registers
            -- TODO: make sure we are not overwriting anything we need
            --       need to move any variables that are free in uc_cont to a different register if they occupy a used argument register
            mapM_ (uncurry codeGenUTerm) $ zip uc_args (argumentRegisters machineDesc)
            -- emit the call for the function
            -- TODO: make sure the return register is free
            codeGenUTermAnyDest uc_func (\fnReg -> tell [Call fnReg])
            codeGenKTerm uc_cont $ Just (returnRegister machineDesc)
        codeGenExpr KCall {kc_arg, kc_cont} = do
            -- TODO: make sure the return register is free
            -- TODO: should this just happen in any free register?
            codeGenUTerm kc_arg (returnRegister machineDesc)
            codeGenKTerm kc_cont $ Just (returnRegister machineDesc)
        codeGenExpr Select {sl_field, sl_record, sl_cont} = do
            offset <- fieldOffsetForRecord sl_field sl_record
            localStateWithContext
                reserveTemporary
                (\fieldReg -> do
                     codeGenUTermAnyDest
                         sl_record
                         (\recordReg -> tell [LoadField recordReg offset fieldReg])
                     codeGenKTerm sl_cont (Just fieldReg))
        codeGenExpr If {if_test, if_csq, if_alt} = do
            elseBlockLabel <- nextLabel
            endBlockLabel <- nextLabel
            codeGenUTermAnyDest if_test (\tmp -> tell [Jump (EqualZero tmp) elseBlockLabel])
            codeGenKTerm if_csq Nothing
            tell [Jump Always endBlockLabel, Label elseBlockLabel]
            codeGenKTerm if_alt Nothing
            tell [Label endBlockLabel]
