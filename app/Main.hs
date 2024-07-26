{-# LANGUAGE OverloadedStrings #-}

module Main where

import ClosureConversion
import CodeGen
import Control.Monad.State
import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified Data.Text as T
import Ir
import qualified XIr

-- register spilling
-- abstract instruction generation
-- assembly
exMod :: Module
exMod = Module {m_funcs = Map.fromList [(Symbol "baz", bazDef)]}
  where
    symA = Symbol "a"
    symB = Symbol "b"
    symC = Symbol "c"
    symD = Symbol "d"
    symF = Symbol "f"
    symCont = Symbol "k"
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

exModX :: XIr.Module
exModX = evalState (XIr.preprocess exMod) 0

cloCovMod :: XIr.Module
cloCovMod = evalState (convertClosures exModX) 1

testMachine :: MachineDesc
testMachine =
    MachineDesc
        { argumentRegisters = [Reg x | x <- [1 .. 15]]
        , returnRegister = Reg 0
        , argumentVariableAssignment =
              \bindings ->
                  VarAssign
                      (Map.fromList $ zip (map XIr.bindingName bindings) [Reg x | x <- [1 .. 15]])
                      (Set.fromList $ Reg 0 : [Reg x | x <- [(length bindings) .. 15]])
        , numRegisters = 16
        }

genMod :: Map.Map XIr.Symbol [Instr]
genMod = codeGen cloCovMod testMachine

main :: IO ()
main = putStrLn "Hello, Haskell!"
