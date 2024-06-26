{-# LANGUAGE OverloadedStrings #-}
module CodeGen where
import qualified Data.Text as T
import Ir
import qualified Data.Map as Map
import Control.Monad.Writer
import qualified Data.Set as Set
import Control.Monad.Reader (ReaderT(ReaderT))

-- CPS to instructions
-- figure out register allocation, instruction sequence, calling convention
-- leave tag manipulation, instruction selection, jump calculation to assembler

data VarAssignment = VarAssign (Map.Map Symbol Register) (Set.Set Register)

newtype MachineDesc = MachineDesc {
    numRegisters :: Int,
    argumentVariableAssignment :: [Symbol] -> VarAssignment
}

newtype Register = Reg Int deriving (Eq,Show)

data Condition = Always | EqualZero Register

data Instr =
    Label T.Text
    | Jump Condition T.Text
    | Call Symbol
    | LoadField Register Symbol Register
    | StoreField Register Symbol Register
    | LoadImm Register Int
    | CreateRecord Register Int


codeGen :: MachineDesc -> Module -> Map.Map Symbol [Instr]

codeGen machineDesc mod = map codeGenFn (m_funcs mod)
    where
    codeGenFn :: Lambda -> [Instr]
    codeGenExpr :: Expr -> ReaderT VarAssignment (Writer [Instr] ())

    codeGenFn Lambda {l_cont, l_body, l_args} =
        execWriter $ runReaderT (codeGenExpr l_body) (argumentVariableAssignment machineDesc l_args)



