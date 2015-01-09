import Synquid.Util
import Synquid.Logic
import Synquid.Solver

import Data.List
import qualified Data.Set as Set
import Data.Set (Set)
import qualified Data.Map as Map
import Data.Map (Map)
import Control.Monad

-- testOptimalSolutions = do
  -- let quals = Map.fromList [
                  -- ("k", [Var "x" |>=| IntLit 0, Var "x" |<=| IntLit 0]),
                  -- ("l", [Var "x" |>| IntLit 0, Var "x" |<| IntLit 0, Var "x" |=| IntLit 0])]
  -- let fml = Unknown "l" |=>| Unknown "k"
  -- putStr $ intercalate "\n" (map (show . flip substitute fml) $ optimalSolutions quals fml)
  
-- stdQuals :: [Id] -> [Formula]  
-- stdQuals vars = do
  -- lhs <- [Var "v"] ++ map Var vars -- [Var "v", IntLit 0] ++ 
  -- op <- [Ge, Gt, Eq]
  -- rhs <- [Var "v"] ++ map Var vars
  -- guard $ lhs /= rhs
  -- return $ Binary op lhs rhs

-- varQual = AnyVar |=| Var "v"
    
-- testMaxSynthesize = do
  -- let vars = ["x", "y"]
  -- let quals = Map.fromList [
                -- ("condT", [Var "x" |>| Var "y", Var "x" |=| Var "y"]), --stdQuals ["x", "y"]),
                -- ("condF", [Var "x" |<=| Var "y", Var "x" |/=| Var "y"])
                -- -- ("then", instantiateVars vars varQual),
                -- -- ("else", instantiateVars vars varQual)
              -- ]
  -- let maxType = (Var "x" |<=| Var "v") |&| (Var "y" |<=| Var "v")
  -- -- let fmls = [  (Unknown "cond" |&| Unknown "then") |=>| maxType,
                -- -- (fnot (Unknown "cond") |&| Unknown "else") |=>| maxType  ]
  -- let fmls = [  (Unknown "condT" |&| (Var "v" |=| Var "x")) |=>| maxType,
                -- (Unknown "condF" |&| (Var "v" |=| Var "y")) |=>| maxType,
                -- BoolLit True |=>| (Unknown "condT" ||| Unknown "condF")
                -- ]                
  -- -- let fmls = [  (Var "x" |>| Var "y" |&| Unknown "then") |=>| maxType,
                -- -- (fnot (Var "x" |>| Var "y") |&| Unknown "else") |=>| maxType  ]                                
  -- print $ greatestFixPoint quals fmls
  
testStrengthen = do
    let quals = Map.fromList [
                ("u", [Var "x" |>| Var "y", Var "x" |>=| Var "y", Var "x" |=| Var "y"]),
                ("v", [Var "x" |<| Var "y", Var "x" |<=| Var "y"]),
                ("w", [Var "x" |<| Var "y", Var "x" |<=| Var "y"])
              ]
    let fml = (Unknown "u" |&| Unknown "v") |=>| (Var "x" |=| Var "y")
    -- let sol = topSolution quals    
    let sol = Map.fromList [
                ("u", Set.fromList [Var "x" |>=| Var "y"]),
                ("v", Set.fromList []),
                ("w", Set.fromList [])
              ]
    print $ strengthen quals fml sol
    
main = testStrengthen -- testMaxSynthesize  
  
  