module Synquid.Bounds where

import Data.List
import Data.Set
import Data.Maybe
import Synquid.Logic
import Synquid.Type
import Debug.Trace
import Synquid.Pretty
import Synquid.Program
import Synquid.Util
import Data.Char
import Synquid.Util
import qualified Data.Map as Map

swap f a b = f b a

-- Turns "A => B => C => D" into ("A & B & C", "D")
getConditions :: Formula -> (Formula, Formula)
getConditions (Binary Implies x y) = 
  let (b, d) = getConditions y in
    (Binary And x b, d)
getConditions u = (BoolLit True, u)

-- Turns bound into ghost function
translateBound :: RBound -> RType
translateBound (Parameter x t (BaseBound bb)) = 
  let (r1, r2) = getConditions bb in
    FunctionT x (ScalarT t (substitute (Map.singleton x (Var (toSort t) valueVarName)) r1)) (
      ScalarT t (
        Binary And r2 (
          Binary Eq (Var (toSort t) x) (
            Var (toSort t) valueVarName)
        )
      )
    )
translateBound (Parameter x t b) = FunctionT x (ScalarT t (BoolLit True)) (translateBound b)

-- Turns all bounds on a schema into ghost functions
translateBounded :: RSchema -> Maybe RSchema
translateBounded = flip translateBounded' []
  where
    translateBounded' :: RSchema -> [RBound] -> Maybe RSchema
    translateBounded' (Bounded b y) bs = translateBounded' y $ b:bs
    translateBounded' (ForallT x y) bs = do
        z <- translateBounded' y bs
        return $ ForallT x z
    translateBounded' (ForallP x y) bs = do
        z <- translateBounded' y bs
        return $ ForallP x z
    translateBounded' (Monotype t) [] = Nothing
    translateBounded' (Monotype t) bs = Just $ Monotype( Data.List.foldr 
        (\b s -> FunctionT "TODO" (translateBound b) s) 
        t 
        bs
      )

boundToProgram :: RBound -> UProgram
boundToProgram (Parameter x t (BaseBound bb)) = Program (PFun x (Program (PSymbol x) AnyT)) AnyT
boundToProgram (Parameter x t b) = Program (PFun dontCare (boundToProgram b)) AnyT

unTranslateBounded :: RSchema -> RProgram -> RProgram
unTranslateBounded (ForallT x y) p = unTranslateBounded y p
unTranslateBounded (ForallP x y) p = unTranslateBounded y p
unTranslateBounded (Bounded b y) p = Program (PApp (unTranslateBounded y p) (boundToProgram b)) AnyT
unTranslateBounded (Monotype t) p = p

-- Not really a RProgram
discardBounds :: RSchema -> Id -> RProgram
discardBounds (ForallT x y) i = discardBounds y i
discardBounds (ForallP x y) i = discardBounds y i
discardBounds (Bounded b y) i = Program (PFun dontCare (discardBounds y i)) AnyT
discardBounds (Monotype t) i = Program (PSymbol i) AnyT


untransUsages :: Goal -> RProgram -> RProgram
untransUsages g p =
  let symbols = symbolsOf p in
  let bounded_symbols = Data.Set.filter (swap Map.member (_bounds (gEnvironment g))) symbols in
  Data.Set.foldr (\bs -> programSubstituteSymbol bs (discardBounds (fromJust $ Map.lookup bs (_bounds (gEnvironment g))) bs)) p bounded_symbols

untransWhole :: Goal -> RProgram -> RProgram
untransWhole g p = case (Map.lookup (gName g) (_bounds (gEnvironment g))) of
    Just x -> unTranslateBounded x p
    Nothing -> p

untranslate :: Goal -> RProgram -> RProgram
untranslate goal = untransWhole goal . untransUsages goal
  -- let symbols = symbolsOf p in
  -- let bounded_symbols = Data.Set.filter (swap Map.member (_bounds (gEnvironment g))) symbols in
  -- Data.Set.foldr (\bs -> \acc -> Program (PFun bs acc) AnyT) (Program (PSymbol dontCare) AnyT) bounded_symbols
  -- 