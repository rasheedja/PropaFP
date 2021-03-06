module PropaFP.Eliminator where

import MixedTypesNumPrelude
import qualified Prelude as P
import Data.List
import PropaFP.Expression

minMaxAbsEliminatorF :: F -> F
minMaxAbsEliminatorF f' = aux f'
  where
    -- hasMinMaxAbsE could be removed
    aux :: F -> F
    aux fToElim =
      case fToElim of
        FConn conn f1 f2 -> FConn conn (aux f1) (aux f2)
        FComp comp e1 e2 ->
          let
            qualifiedE1s = minMaxAbsEliminator $ ENonStrict e1
            qualifiedE2s = minMaxAbsEliminator $ ENonStrict e2

            eListToConjunction [] = error "undefined"
            eListToConjunction [ENonStrict e] = FComp Ge e (Lit 0.0)
            eListToConjunction [EStrict e]    = FComp Gt e (Lit 0.0)
            eListToConjunction (e : es)       = FConn And (eListToConjunction [e]) (eListToConjunction es)

            fListToConjunction [] = error "undefined"
            fListToConjunction [f]      = f
            fListToConjunction (f : fs) = FConn And f (fListToConjunction fs)

            build :: ([ESafe], ESafe) -> [([ESafe], ESafe)] -> F
            build _                        [] = error "Empty qualified list given in minMaxAbsEliminator"
            build e1Q@(e1C, e1G) [(e2C, e2G)] =
              let
                combinedL = e1C ++ e2C
                combinedF = eListToConjunction (nub combinedL)
                combinedG = FComp comp (extractSafeE e1G) (extractSafeE e2G)
                combinedQ = FConn Impl combinedF combinedG
              in
                if null combinedL
                  then combinedG
                  else combinedQ
            build e1Q@(e1C, e1G) ((e2C, e2G) : e2Qs) =
              let
                combinedL = e1C ++ e2C
                combinedF = eListToConjunction (nub combinedL)
                combinedG = FComp comp (extractSafeE e1G) (extractSafeE e2G)
                combinedQ = FConn Impl combinedF combinedG
              in
                if null combinedL
                  then combinedG
                  else FConn And combinedQ $ build e1Q e2Qs

            combinedQualifiedEsAsF = fListToConjunction $ map (`build` qualifiedE2s) qualifiedE1s
          in
            combinedQualifiedEsAsF

        FNot f -> FNot (aux f)
        FTrue  -> FTrue
        FFalse -> FFalse

-- | Given an expression, eliminate all Min, Max, and Abs
-- occurences. This is done by:
-- 
-- When we come across a Min e1 e2:
-- 1) We have two cases
-- 1a) if e2 >= e1, then choose e1
-- 1b) if e1 >= e2, then choose e2
-- 2) So, we eliminate min and add two elements to the qualified list
-- 2a) Add e2 - e1 to the list of premises, call the eliminiator on e1 and e2
-- recursively, add any new premises from the recursive call to the list of premises,
-- set the qualified value of e1 from the recursive call to be the qualified value
-- in this case
-- 2b) similar to 2a
-- 
-- Max e1 e2 is similar to Min e1 e2
-- Abs is treated as Max e (-e)
-- 
-- If we come across any other operator, recursively call the eliminator on any
-- expressions, add any resulting premises, and set the qualified value to be
-- the operator called on the resulting Es 
minMaxAbsEliminator :: ESafe -> [([ESafe],ESafe)]
minMaxAbsEliminator (ENonStrict (EBinOp op e1 e2)) =
  case op of
    Min ->
      concat
      [
        [
          (nub ((p1 ++ p2) ++ [ENonStrict (EBinOp Sub (extractSafeE e2') (extractSafeE e1'))]), e1'), -- e2' >= e1'
          (nub ((p2 ++ p1) ++ [ENonStrict (EBinOp Sub (extractSafeE e1') (extractSafeE e2'))]), e2')  -- e1' >= e2'
        ]
        |
        (p1, e1') <- branch1, (p2, e2') <- branch2
      ]
    Max ->
      concat
      [
        [
          (nub ((p1 ++ p2) ++ [ENonStrict (EBinOp Sub (extractSafeE e1') (extractSafeE e2'))]), e1'), -- e1' >= e2'
          (nub ((p2 ++ p1) ++ [ENonStrict (EBinOp Sub (extractSafeE e2') (extractSafeE e1'))]), e2')  -- e2' >= e1'
        ]
        |
        (p1, e1') <- branch1, (p2, e2') <- branch2
      ]
    op' ->
      [(nub (p1 ++ p2), ENonStrict (EBinOp op' (extractSafeE e1') (extractSafeE e2'))) | (p1, e1') <- branch1, (p2, e2') <- branch2]
  where
    branch1 = minMaxAbsEliminator (ENonStrict e1)
    branch2 = minMaxAbsEliminator (ENonStrict e2)
minMaxAbsEliminator (ENonStrict (EUnOp op e)) =
  case op of
    Abs ->
      minMaxAbsEliminator (ENonStrict (EBinOp Max e (EUnOp Negate e)))
    op' ->
      [(p, ENonStrict (EUnOp op' (extractSafeE e'))) | (p, e') <- minMaxAbsEliminator (ENonStrict e)]
minMaxAbsEliminator (ENonStrict (PowI e i))            =
  [(p, ENonStrict (PowI (extractSafeE e') i)) | (p, e') <- minMaxAbsEliminator (ENonStrict e)]
minMaxAbsEliminator (ENonStrict (Float mode e))        =
  [(p, ENonStrict (Float mode (extractSafeE e'))) | (p, e') <- minMaxAbsEliminator (ENonStrict e)]
minMaxAbsEliminator (ENonStrict (Float32 mode e))        =
  [(p, ENonStrict (Float32 mode (extractSafeE e'))) | (p, e') <- minMaxAbsEliminator (ENonStrict e)]
minMaxAbsEliminator (ENonStrict (Float64 mode e))        =
  [(p, ENonStrict (Float64 mode (extractSafeE e'))) | (p, e') <- minMaxAbsEliminator (ENonStrict e)]
minMaxAbsEliminator (ENonStrict (RoundToInteger mode e)) =
  [(p, ENonStrict (RoundToInteger mode (extractSafeE e'))) | (p, e') <- minMaxAbsEliminator (ENonStrict e)]
minMaxAbsEliminator e@(ENonStrict (Lit _))             = [([],e)]
minMaxAbsEliminator e@(ENonStrict (Var _))             = [([],e)]
minMaxAbsEliminator e@(ENonStrict Pi)                  = [([],e)]


minMaxAbsEliminator (EStrict (EBinOp op e1 e2)) =
  case op of
    Min ->
      concat
      [
        [                      --Min/Max should always be non-strict here
          (nub ((p1 ++ p2) ++ [ENonStrict (EBinOp Sub (extractSafeE e2') (extractSafeE e1'))]), e1'), -- e2' > e1'
          (nub ((p2 ++ p1) ++ [ENonStrict (EBinOp Sub (extractSafeE e1') (extractSafeE e2'))]), e2')  -- e1' > e2'
        ]
        |
        (p1, e1') <- branch1, (p2, e2') <- branch2
      ]
    Max ->
      concat
      [
        [
          (nub ((p1 ++ p2) ++ [ENonStrict (EBinOp Sub (extractSafeE e1') (extractSafeE e2'))]), e1'), -- e1' > e2'
          (nub ((p2 ++ p1) ++ [ENonStrict (EBinOp Sub (extractSafeE e2') (extractSafeE e1'))]), e2')  -- e2' > e1'
        ]
        |
        (p1, e1') <- branch1, (p2, e2') <- branch2
      ]
    op' ->
      [(nub (p1 ++ p2), EStrict (EBinOp op' (extractSafeE e1') (extractSafeE e2'))) | (p1, e1') <- branch1, (p2, e2') <- branch2]
  where
    branch1 = minMaxAbsEliminator (EStrict e1)
    branch2 = minMaxAbsEliminator (EStrict e2)
minMaxAbsEliminator (EStrict (EUnOp op e)) =
  case op of
    Abs ->
      minMaxAbsEliminator (EStrict (EBinOp Max e (EUnOp Negate e)))
    op' ->
      [(p, EStrict (EUnOp op' (extractSafeE e'))) | (p, e') <- minMaxAbsEliminator (EStrict e)]
minMaxAbsEliminator (EStrict (PowI e i))            =
  [(p, EStrict (PowI (extractSafeE e') i)) | (p, e') <- minMaxAbsEliminator (EStrict e)]
minMaxAbsEliminator (EStrict (Float mode e))        =
  [(p, EStrict (Float mode (extractSafeE e'))) | (p, e') <- minMaxAbsEliminator (EStrict e)]
minMaxAbsEliminator (EStrict (Float32 mode e))        =
  [(p, EStrict (Float32 mode (extractSafeE e'))) | (p, e') <- minMaxAbsEliminator (EStrict e)]
minMaxAbsEliminator (EStrict (Float64 mode e))        =
  [(p, EStrict (Float64 mode (extractSafeE e'))) | (p, e') <- minMaxAbsEliminator (EStrict e)]
minMaxAbsEliminator (EStrict (RoundToInteger mode e)) =
  [(p, EStrict (RoundToInteger mode (extractSafeE e'))) | (p, e') <- minMaxAbsEliminator (ENonStrict e)]
minMaxAbsEliminator e@(EStrict (Lit _))             = [([],e)]
minMaxAbsEliminator e@(EStrict (Var _))             = [([],e)]
minMaxAbsEliminator e@(EStrict Pi)                  = [([],e)]
-- If we extractSafeE, then strictness does not matter

-- [[[[E]]]] where [[E]] = [e1 /\ (e2 \/ e3) /\ e4]
-- [[[e1 /\ (e2 \/ e3) /\ e4]] \/ [e1 /\ (e2 \/ e3) /\ e4]]
-- [[[[e1 /\ (e2 \/ e3) /\ e4]] \/ [e1 /\ (e2 \/ e3) /\ e4]] /\ [[[e1 /\ (e2 \/ e3) /\ e4]] \/ [e1 /\ (e2 \/ e3) /\ e4]]]
minMaxAbsEliminatorECNF :: [[ESafe]] -> [[ESafe]]
minMaxAbsEliminatorECNF ecnf = and $ map or (map (map (qualifiedEsToCNF2 . minMaxAbsEliminator)) ecnf)
  where
    and2 = (++)
    or2 ecnf1 ecnf2 = [d1 ++ d2 | d1 <- ecnf1, d2 <- ecnf2]
    and :: [[[ESafe]]] -> [[ESafe]]
    and = foldl and2 []
    or :: [[[ESafe]]] -> [[ESafe]]
    or = foldl or2 [[]]

-- | Translate the qualified Es list to a single expression
-- The qualified Es list is basically the following formula:
-- e >= 0 == (p1 >= 0 /\ p2 >= 0 /\ p3 >=0 -> q1 >= 0) /\ repeat...
-- where e is the expression passed to minMaxAbsEliminator
-- 
-- This can be rewritten to
-- (-p1 >= 0 \/ - p2 >= 0 \/ -p3 >= 0 \/ q1 >= 0)
-- This is incorrect, strictness is not dealt with correctly
-- qualifiedEsToCNF :: [([E],E)] -> E
-- qualifiedEsToCNF []               = undefined
-- qualifiedEsToCNF [([], q)]        = q
-- qualifiedEsToCNF [(ps, q)]        = EBinOp Max (buildPs ps) q
--   where
--     buildPs :: [E] -> E
--     buildPs []  = undefined
--     buildPs [p] = (EUnOp Negate p)
--     buildPs (p : ps) = EBinOp Max (EUnOp Negate p) (buildPs ps) 
-- qualifiedEsToCNF ((ps, q) : es) = EBinOp Min (qualifiedEsToCNF [(ps, q)]) (qualifiedEsToCNF es)

-- | Convert a list of qualified Es to a CNF represented as a list of lists
qualifiedEsToCNF2 :: [([ESafe],ESafe)] -> [[ESafe]]
qualifiedEsToCNF2 =
  map
  (\(ps,q) ->
    q : map negateSafeE ps
  )
  -- The negation of ps turns it into ps < 0, which is equivalent to -ps > 0

-- Disjunction of Conjunction of Disjunction 

qualifiedEsToDisjunction :: ([ESafe], ESafe) -> [ESafe]
qualifiedEsToDisjunction (context, goal) = goal : map negateSafeE context

qualifiedEsToF :: [([ESafe], ESafe)] -> F
qualifiedEsToF []                         = undefined
qualifiedEsToF [qualifiedE]               = qualifiedEToF qualifiedE
qualifiedEsToF (qualifiedE : qualifiedEs) = FConn And (qualifiedEToF qualifiedE) (qualifiedEsToF qualifiedEs)

qualifiedEToF :: ([ESafe], ESafe) -> F
qualifiedEToF ([],      goal) = eSafeToF goal
qualifiedEToF (context, goal) = FConn Impl (aux context) $ eSafeToF goal
  where
    aux []       = undefined
    aux [c]      = eSafeToF c
    aux (c : cs) = FConn And (eSafeToF c) (aux cs)
-- TODO:

-- Translate to this type
-- Vector (Differential (CN MPBall)) -> [[Differential (CN MPBall)]]
-- We'd give this type some domain

-- type EvalE = Vector (Differential (CN MPBall)) -> Differential (CN MPBall)
-- type EvalECNF = Vector (Differential (CN MPBall)) -> [[Differential (CN MPBall)]]
