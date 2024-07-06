{-# LANGUAGE OverloadedStrings #-}

module Main where

import Control.Monad.State
import qualified Data.Map as Map
import qualified Data.Text as T
import Ir
import ClosureConversion
import CodeGen
import qualified Data.Set as Set

-- register spilling
-- abstract instruction generation
-- assembly
exMod :: Module
exMod = Module {m_funcs = Map.fromList [(Symbol "baz" 0, bazDef)]}
  where
    symA = Symbol "a" 0
    symB = Symbol "b" 0
    symC = Symbol "c" 0
    symD = Symbol "d" 0
    symF = Symbol "f" 0
    symCont = Symbol "k" 0
    bazDef =
        Lambda
            { l_args =
                  [ Binding symA TyInt
                  , Binding symF
                        $ TyFn [TyFn [TyInt] (TyCont $ Just TyInt), TyInt] (TyCont $ Just TyInt)
                  ]
            , l_cont = Binding symCont (TyCont $ Just TyInt)
            , l_body =
                  UCall
                      { uc_func = UVar symF
                      , uc_args =
                            [ ULambda
                                  Lambda
                                      { l_args = [Binding symB TyInt]
                                      , l_cont = Binding symCont (TyCont $ Just TyInt)
                                      , l_body = KCall {kc_cont = KVar symCont, kc_arg = UVar symA}
                                      }
                            , UVar symA
                            ]
                      , uc_cont = KVar symCont
                      }
            }

cloCovMod :: Module
cloCovMod = evalState (convertClosures exMod) 1

testMachine :: MachineDesc
testMachine = MachineDesc {
    argumentRegisters=[Reg x | x <- [1..15]],
    returnRegister=Reg 0,
    argumentVariableAssignment= \names -> VarAssign
        (Map.fromList $ zip names [Reg x | x <- [1..15]])
        (Set.fromList $ Reg 0 : [Reg x | x <- [(length names)..15]]),
    numRegisters=16
}

genMod :: Map.Map Symbol [Instr]
genMod = codeGen testMachine cloCovMod

main :: IO ()
main = putStrLn "Hello, Haskell!"
