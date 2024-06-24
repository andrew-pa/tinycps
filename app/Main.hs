{-# LANGUAGE OverloadedStrings #-}
module Main where
import Ir
import qualified Data.Text as T
import qualified Data.Map as Map
-- register spilling
-- abstract instruction generation
-- assembly
symA = Symbol "a" 0
symB = Symbol "b" 0
symC = Symbol "c" 0
symD = Symbol "d" 0
symF = Symbol "f" 0
symCont = Symbol "k" 0

-- Define a lambda with free variables
lambdaWithFreeVar = Lambda {
    l_args = [symA, symB],
    l_cont = symCont,
    l_body = UCall {
        uc_func = UVar symF,
        uc_args = [UVar symA, UVar symB],
        uc_cont = KVar symCont
    }
}

lambdaClosure = Lambda {
    l_args = [symC],
    l_cont = symCont,
    l_body = UCall {
        uc_func = ULambda (Lambda {
            l_args = [symD],
            l_cont = symCont,
            l_body = UCall {
                uc_func = UVar $ Symbol "foo" 0,
                uc_args = [UVar symC, UVar symD],
                uc_cont = KVar symCont
            }
        }),
        uc_args = [ULambda lambdaWithFreeVar],
        uc_cont = KVar symCont
    }
}

-- Define the module
moduleClosureConversion = Module {
    m_funcs = Map.fromList [
        (Symbol "baz" 0, lambdaClosure)
    ]
}
main :: IO ()
main = putStrLn "Hello, Haskell!"
