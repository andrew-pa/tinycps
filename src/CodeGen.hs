{-# LANGUAGE OverloadedStrings #-}

module CodeGen where

import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Writer
import Data.Foldable (find)
import Data.Functor ((<&>))
import qualified Data.Map as Map
import Data.Map ((!))
import Data.Maybe (isNothing)
import qualified Data.Set as Set
import qualified Data.Text as T
import Ext (incrSymCounter)
import Ir (UType(..))
import XIr

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

unassignVariable :: Binding UType -> VarAssignment -> VarAssignment
unassignVariable s (VarAssign assigned free) =
    let r = assigned ! bindingName s
     in VarAssign (Map.delete (bindingName s) assigned) (Set.insert r free)

reserveTemporary :: VarAssignment -> (VarAssignment, Register)
reserveTemporary (VarAssign assigned free) =
    let fr = Set.findMin free
     in (VarAssign assigned $ Set.delete fr free, fr)

lookupAssignmentMaybe :: Symbol -> VarAssignment -> Maybe Register
lookupAssignmentMaybe s (VarAssign assigned _) = Map.lookup s assigned

lookupAssignment :: Symbol -> VarAssignment -> Register
lookupAssignment s (VarAssign assigned _) = assigned ! s

swapAssignment :: Monad m => Symbol -> Register -> VarAssignment -> WriterT [Instr] m VarAssignment
-- Ensure that previously assigned `s` is now assigned the register `r`. If `r` is in use, the variable using `r` will now use the register previously assigned to `s`.
-- To do so, it may be necessary to emit some instructions to manipulate the registers.
swapAssignment s r (VarAssign assigned free)
    | r == assigned ! s = return (VarAssign assigned free)
    | otherwise =
        case find ((== r) . snd) (Map.toList assigned) <&> fst of
            Just otherS ->
                tell [Swap r (assigned ! s)]
                    >> return
                           (VarAssign
                                (Map.insert s r (Map.insert otherS (assigned ! s) assigned))
                                free)
            Nothing ->
                return
                    $ VarAssign
                          (Map.insert s r assigned)
                          (Set.insert (assigned ! s) (Set.delete r free))

swapAssignmentM :: UTerm -> Register -> GenM ()
swapAssignmentM (UVar s) r = do
    va <- get
    nva <- lift $ lift $ lift $ lift $ swapAssignment s r va
    put nva

data MachineDesc = MachineDesc
    { numRegisters :: Int
    , argumentVariableAssignment :: [Binding UType] -> VarAssignment
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
    | CopyField Register Int Register Int
    | LoadImm Register Int
    | CreateRecord Register Int
    | Move Register Register
    | Swap Register Register
    | LoadAddressOf Symbol Register
    deriving (Eq, Show)

codeGen :: Module -> MachineDesc -> Map.Map Symbol [Instr]
codeGen m = runReader (mapM codeGenFn (m_funcs m))

codeGenFn :: Lambda -> Reader MachineDesc [Instr]
codeGenFn Lambda {l_cont, l_body, l_args} = do
    ava <- reader argumentVariableAssignment
    let argTypes = Map.fromList $ map (\(Binding n t) -> (n, t)) l_args
    execWriterT
        $ evalStateT
              (evalStateT
                   (runReaderT (runReaderT (codeGenExpr l_body) argTypes) (bindingName l_cont))
                   (ava l_args))
              1

type GenM
    = ReaderT
          (Map.Map Symbol UType)
          (ReaderT Symbol (StateT VarAssignment (StateT Int (WriterT [Instr] (Reader MachineDesc)))))

askArgumentVariableAssignment :: GenM ([Binding UType] -> VarAssignment)
askArgumentVariableAssignment = lift $ lift $ reader argumentVariableAssignment

askReturnRegister :: GenM Register
askReturnRegister = lift $ lift $ reader returnRegister

askArgumentRegisters :: GenM [Register]
askArgumentRegisters = lift $ lift $ reader argumentRegisters

nextLabel :: GenM Int
nextLabel = lift $ lift $ lift incrSymCounter

askTopLevelContinuationName :: GenM Symbol
askTopLevelContinuationName = lift ask

bindVar :: Binding UType -> GenM Register
bindVar b = do
    va <- get
    let r = nextFreeRegister va
    modify $ assignVariable b r
    return r

maybeM_ :: Monad m => (a -> m ()) -> Maybe a -> m ()
maybeM_ f (Just x) = f x
maybeM_ _ Nothing = return ()

fieldOffsetForRecord :: UType -> T.Text -> GenM Int
fieldOffsetForRecord (TyRecord fields) fieldName
    | isNothing $ Map.lookup "$fn" fields = return $ Map.findIndex fieldName fields
    | otherwise =
        return
            $ if fieldName == "$fn"
                  then 0
                  else 1 + Map.findIndex fieldName (Map.delete "$fn" fields)
fieldOffsetForRecord (TyFn _ _) "$fn" = return 0
fieldOffsetForRecord (TyFn _ _) _ = error "illegal to select anything except $fn from a function"
fieldOffsetForRecord _ _ = error "non-record type has no fields"

recordSize :: Map.Map T.Text UType -> GenM Int
recordSize = return . Map.size

codeGenUTerm :: UTerm -> GenM Register
codeGenUTerm (UVar v) = gets (lookupAssignment v)

codeGenKTerm :: KTerm -> Maybe Register -> GenM ()
codeGenKTerm KLambda {kl_arg, kl_body} reg = do
    case (kl_arg, reg) of
        (Just a, Just r) -> modify $ assignVariable a r
        (Nothing, Nothing) -> return ()
        _ -> error "kterm ariety mismatch"
    local (maybe id (\(Binding n t) -> Map.insert n t) kl_arg) $ codeGenExpr kl_body
    maybeM_ (modify . unassignVariable) kl_arg
codeGenKTerm (KVar v) reg = do
    topLevelK <- askTopLevelContinuationName
    returnReg <- askReturnRegister
    if v == topLevelK
        then do
            maybeM_ (\r -> tell [Move r returnReg]) reg
            tell [Return]
        else error "escaped continuation"

codeGenKTermK :: KTerm -> (Register -> GenM ()) -> GenM ()
codeGenKTermK KLambda {kl_arg, kl_body} genArgInReg = do
    maybeM_ (bindVar >=> genArgInReg) kl_arg
    local (maybe id (\(Binding n t) -> Map.insert n t) kl_arg) $ codeGenExpr kl_body
    maybeM_ (modify . unassignVariable) kl_arg
codeGenKTermK (KVar v) genArgInReg = do
    topLevelK <- askTopLevelContinuationName
    returnReg <- askReturnRegister
    if v == topLevelK
        then do
            genArgInReg returnReg
            tell [Return]
        else error "escaped continuation"

codeGenExpr :: Expr -> GenM ()
codeGenExpr UCall {uc_func, uc_args, uc_cont} = do
    returnReg <- askReturnRegister
    argRegs <- askArgumentRegisters
    fnPtr <- codeGenUTerm uc_func
    mapM_ (uncurry swapAssignmentM) $ zip uc_args argRegs
    -- deal with return register being assigned? some platforms reuse argument register for return register!?
    tell [Call fnPtr]
    codeGenKTerm uc_cont (Just returnReg)
-- TODO: implement literal lifetimes correctly
codeGenExpr Literal {lt_val = LiInt v, lt_cont} = codeGenKTermK lt_cont $ \r -> tell [LoadImm r v]
codeGenExpr Literal {lt_val = ULambda _} = error "must closure convert prior to codegen"
codeGenExpr Literal {lt_val = LiRecord fields, lt_cont} = do
    recordTy <- mapM typeOfLRV fields
    fieldRegs <- mapM (codeGenField $ fieldOffsetForRecord $ TyRecord recordTy) (Map.toList fields)
    size <- recordSize recordTy
    codeGenKTermK lt_cont $ \r -> tell $ CreateRecord r size : map ($ r) fieldRegs
  where
    typeOfLRV (LRVUTerm t) = reader (! utermAsSymbol t)
    typeOfLRV (LRVSelect r f) = reader $ selectType . (! utermAsSymbol r)
      where
        selectType (TyRecord thefields) = thefields ! f
        selectType _ = error "cannot select from non-record type"
    codeGenField fieldOffset (fieldName, fieldTerm) = do
        dstOffset <- fieldOffset fieldName
        case fieldTerm of
            LRVUTerm t -> do
                reg <- codeGenUTerm t
                return $ \dst -> StoreField dst dstOffset reg
            LRVSelect srcRecord srcField -> do
                src <- codeGenUTerm srcRecord
                srcType <- reader (! utermAsSymbol srcRecord)
                srcOffset <- fieldOffsetForRecord srcType srcField
                return $ \dst -> CopyField dst dstOffset src srcOffset
codeGenExpr Literal {lt_val = TopLevelRef n, lt_cont} =
    codeGenKTermK lt_cont $ \r -> tell [LoadAddressOf n r]
codeGenExpr KCall {kc_arg, kc_cont} = do
    r <- codeGenUTerm kc_arg
    codeGenKTerm kc_cont (Just r)
codeGenExpr Select {sl_field, sl_record, sl_cont} = do
    recordReg <- codeGenUTerm sl_record
    recordTy <- reader (! utermAsSymbol sl_record)
    offset <- fieldOffsetForRecord recordTy sl_field
    codeGenKTermK sl_cont $ \r -> tell [LoadField recordReg offset r]
codeGenExpr If {if_test, if_csq, if_alt} = do
    elseBlockLabel <- nextLabel
    endBlockLabel <- nextLabel
    tst <- codeGenUTerm if_test
    -- TODO: both branches can have the same variable assignment state
    tell [Jump (EqualZero tst) elseBlockLabel]
    codeGenKTerm if_csq Nothing
    tell [Jump Always endBlockLabel, Label elseBlockLabel]
    codeGenKTerm if_alt Nothing
    tell [Label endBlockLabel]
