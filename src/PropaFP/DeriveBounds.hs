{-# LANGUAGE PartialTypeSignatures #-}
{-# OPTIONS_GHC -Wno-partial-type-signatures #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use camelCase" #-}
{-|
    Module      :  PropaFP.DeriveBounds
    Description :  Deriving ranges for variables from hypotheses inside a formula
    Copyright   :  (c) Michal Konecny 2013, 2021
    License     :  BSD3

    Maintainer  :  mikkonecny@gmail.com
    Stability   :  experimental
    Portability :  portable

    Deriving ranges for variables from hypotheses inside a formula
-}
module PropaFP.DeriveBounds 
where

import MixedTypesNumPrelude
import qualified Numeric.CollectErrors as CN

import qualified Prelude as P

import qualified Data.Map as Map
import qualified Data.List as List
-- import qualified Data.Bifunctor as Bifunctor
import AERN2.MP.Ball
import AERN2.MP.Dyadic

import PropaFP.Expression
import PropaFP.VarMap

import Debug.Trace (trace)
import Data.List

-- examples:

_f1 :: F -- eliminates "x"
_f1 = FConn Impl (FConn And (FComp Le (Var "x") (Lit 1.0)) (FComp Le (Lit 0.0) (Var "x"))) (FComp Eq (Lit 0.0) (Lit 0.0))

_f2 :: F
_f2 = FConn Impl (FConn And (FComp Le (Var "x") (Lit 1.0)) (FComp Le (Lit 0.0) (Var "x"))) (FComp Eq (Var "x") (Lit 0.0))

_f3 :: F -- underivable "x"
_f3 = FConn Impl (FConn And (FComp Le (Var "x") (Lit 1.0)) (FComp Le (Var "x") (Lit 0.0))) (FComp Eq (Var "x") (Lit 0.0))

_f4 :: F -- nested implication containing bound on "x" guarded by a condition on "n"
_f4 =
  FConn Impl 
    (FConn And 
      (FConn And 
        (FComp Le (Var "x") (Lit 1.0)) 
        (FComp Eq (Var "n") (Lit 1.0)))
      (FConn Impl (FComp Eq (Var "n") (Lit 1.0)) (FComp Le (Lit 0.0) (Var "x"))))
    (FComp Eq (Var "x") (Lit 0.0))

_f5 :: F -- two opposing implications which contain the same bound on "x"
_f5 =
  FConn And
  (
    FConn And
      (FConn And
        (FComp Ge (Var "n") (Lit 0.0))
        (FComp Le (Var "n") (Lit 2.0))
      )
      (FConn And
        (FConn Impl
          (FComp Le (Var "n") (Lit 1.0))
          (FConn And
            (FComp Ge (Var "x") (Lit (-1.0)))
            (FComp Le (Var "x") (Lit 1.0))
          )
        )
        (FConn Impl
          ((FComp Gt (Var "n") (Lit 1.0)))
          (FConn And
            (FComp Ge (Var "x") (Lit (-1.0)))
            (FComp Le (Var "x") (Lit 1.0))
          )
        )
      )
  )
  $
  FComp Ge (EUnOp Sin (Var "x")) (Lit 0.0)

type VarName = String

deriveBoundsAndSimplify :: F -> (F, VarMap, [VarName])
deriveBoundsAndSimplify form' =
  (finalSimplifiedF, derivedRangesWithoutPoints, map fst underivedRanges)
    where
    finalSimplifiedF = simplifyF simplifiedFWithSubstitutedPoints
   

    simplifiedFWithSubstitutedPoints = substitutePoints simplifiedF varsWithPoints

    simplifiedF = (\(FConn Impl f FFalse) -> f) simplifiedFImpliesFalse
    -- undo implies false on simplifiedFImpliesFalse

    (derivedRangesWithoutPoints, varsWithPoints) = seperatePoints derivedRanges

    derivedRanges = map removeJust mDerivedRanges

    (mDerivedRanges, underivedRanges) = List.partition isGood varRanges

    isPoint (l, r) = l == r


    substitutePoints :: F -> [(String, Rational)] -> F
    substitutePoints f [] = f
    substitutePoints f ((var, val) : varPoints) = substitutePoints (substVarFWithLit f var val) varPoints

    seperatePoints :: VarMap -> (VarMap, [(String, Rational)])
    seperatePoints [] = ([], [])
    seperatePoints ((var, bounds) : varMap) = 
      if isPoint bounds
        then (resultingVarMap, (var, fst bounds) : resultingPoints)
        else ((var, bounds) : resultingVarMap, resultingPoints)
      where
        (resultingVarMap, resultingPoints) = seperatePoints varMap

    form = FConn Impl form' FFalse -- Make the given form imply false for derivation of bounds
    removeJust (v, (Just l, Just r)) = (v, (l, r))
    removeJust _ = error "deriveBounds: removeJust failed"
    varRanges = Map.toList box
    isGood (_v, (Just _,Just _)) = True
    isGood _ = False
    initBox = Map.fromList $ zip (extractVariablesF form) (repeat (Nothing, Nothing))
    (box, simplifiedFImpliesFalse) = aux initBox $ form
      where
      aux b f 
        | b P.== b2 = (b, f2)
        | otherwise = aux b2 f2
        where
        f2 = (\(FConn Impl form2 _falseTerm) -> FConn Impl (simplifyF form2) _falseTerm) (evalF_comparisons b f)
              -- simplify where possible with the knowledge we are restricted to box b
              -- avoid simplifying form2 -> false, only simplify form2
        b' = Map.intersection b $ Map.fromList $ zip (extractVariablesF f2) (repeat ())
              -- remove variables that do not appear in f2
        b2 = scanHypotheses f2 b'
              -- attempt to improve the bounds on the variables

type VarBoundMap = Map.Map VarName (Maybe Rational, Maybe Rational)

-- TODO: Could refactor this to remove need of form -> false
scanHypotheses :: F -> VarBoundMap -> VarBoundMap
scanHypotheses (FConn Impl h c) =
    scanHypotheses c . scanHypothesis h False 
scanHypotheses _ = id

scanHypothesis :: F -> Bool -> VarBoundMap -> VarBoundMap
scanHypothesis (FNot h) isNegated intervals = scanHypothesis h (not isNegated) intervals 
scanHypothesis (FConn And (FConn Impl cond1 branch1) (FConn Impl (FNot cond2) branch2)) False intervals 
  | cond1 P.== cond2 = scanHypothesis (FConn Or branch1 branch2) False intervals
  | normalizeBoolean cond1 P.== normalizeBoolean cond2 = scanHypothesis (FConn Or branch1 branch2) False intervals
  | sort (simplifyESafeDoubleList (fToEDNF (simplifyF cond1))) P.== sort (simplifyESafeDoubleList (fToEDNF (simplifyF cond2))) = scanHypothesis (FConn Or branch1 branch2) False intervals
-- scanHypothesis f@(FConn And h1@(FConn Impl cond1 branch1) h2@(FConn Impl cond2 branch2)) False intervals 
--   =
--   trace (show f) $
--   trace (show intervals) $
--   trace (show (checkFWithEval cond1 intervals)) $
--   trace (show (checkFWithEval cond2 intervals)) $
--   -- doesn't work because cond1/2 is indeterminate most of the time
--   case checkFWithEval cond1 intervals of
--     Nothing -> (scanHypothesis h1 False . scanHypothesis h2 False) intervals
--     result1 -> 
--       case checkFWithEval cond2 intervals of
--         Nothing -> (scanHypothesis h1 False . scanHypothesis h2 False) intervals
--         result2 ->
--           if result1 P./= result2
--             then scanHypothesis (FConn Or branch1 branch2) False intervals
--             else (scanHypothesis h1 False . scanHypothesis h2 False) intervals
scanHypothesis (FConn And h1 h2) isNegated intervals = 
  if isNegated
    then scanHypothesis (FConn Or (FNot h1) (FNot h2)) False intervals
    else (scanHypothesis h1 isNegated . scanHypothesis h2 isNegated) intervals
scanHypothesis (FConn Or h1 h2) isNegated intervals = 
  if isNegated
    then scanHypothesis (FConn And (FNot h1) (FNot h2)) False intervals
    else Map.unionWith mergeWorse box1 box2
      where
      box1 = iterateUntilNoChange (scanHypothesis h1 isNegated) intervals
      box2 = iterateUntilNoChange (scanHypothesis h2 isNegated) intervals
      mergeWorse (l1,r1) (l2,r2) = (min <$> l1 <*> l2, max <$> r1 <*> r2)

      -- mergeWorse (l1,r1) (l2,r2) = 
      --   case (l1, r1, l2, r2) of
      --     (Nothing, Nothing, Just _, Just _) -> (l2, r2) -- FIXME: hack, should only do this if variable of interest only exists in one branch
      --     (Just _, Just _, Nothing, Nothing) -> (l1, r1) -- FIXME: hack, should only do this if variable of interest only exists in one branch
      --     _ -> (min <$> l1 <*> l2, max <$> r1 <*> r2)

      iterateUntilNoChange refineBox b1
        | b1 P.== b2 = b1
        | otherwise = iterateUntilNoChange refineBox b2
        where
          b2 = refineBox b1
      -- iterateUntilNoChange b1 f
      --   | b1 P.== b2 = b1
      --   | otherwise = scanHypothesis f isNegated b1
scanHypothesis (FConn Impl h1 h2) isNegated intervals = scanHypothesis (FConn Or (FNot h1) h2) isNegated intervals
-- We need: data Comp = Gt | Ge | Lt | Le | Eq
scanHypothesis (FComp Eq _ _) True intervals = intervals
scanHypothesis (FComp Eq _e1@(Var v1) _e2@(Var v2)) False intervals = 
    Map.insert v1 val $
    Map.insert v2 val $
    intervals
    where
    Just val1 = Map.lookup v1 intervals
    Just val2 = Map.lookup v2 intervals
    val = updateUpper val1 $ updateLower val1 $ val2

scanHypothesis (FComp Eq (Var v) e) False intervals = 
    Map.insertWith updateUpper v val $
    Map.insertWith updateLower v val intervals
    where
    val = evalE_Rational intervals e

scanHypothesis (FComp Eq e (Var v)) False intervals = 
    Map.insertWith updateUpper v val $
    Map.insertWith updateLower v val intervals
    where
    val = evalE_Rational intervals e

-- Deal with negated inequalites
scanHypothesis (FComp Le e1 e2) True intervals =
  scanHypothesis (FComp Gt e1 e2) False intervals 
  
scanHypothesis (FComp Lt e1 e2) True intervals =
  scanHypothesis (FComp Ge e1 e2) False intervals 
  
scanHypothesis (FComp Gt e1 e2) True intervals =
  scanHypothesis (FComp Le e1 e2) False intervals 
  
scanHypothesis (FComp Ge e1 e2) True intervals =
  scanHypothesis (FComp Lt e1 e2) False intervals 

scanHypothesis (FComp Le _e1@(Var v1) _e2@(Var v2)) False intervals = 
    Map.insert v1 (updateUpper val2 val1) $
    Map.insert v2 (updateLower val1 val2) $
    intervals
    where
    Just val1 = Map.lookup v1 intervals
    Just val2 = Map.lookup v2 intervals

scanHypothesis (FComp Le (Var v) e) False intervals = 
    Map.insertWith updateUpper v (evalE_Rational intervals e) intervals
scanHypothesis (FComp Le e (Var v)) False intervals = 
    Map.insertWith updateLower v (evalE_Rational intervals e) intervals
-- Bounds for absolute values of Vars
scanHypothesis (FComp Le (EUnOp Abs (Var v)) e) False intervals =
  -- trace (show bounds)
    Map.insertWith updateLower v bounds $ Map.insertWith updateUpper v bounds intervals
    where
    (eValL, eValR) = evalE_Rational intervals e
    bounds         = (fmap negate eValL, eValR)
-- reduce Le, Geq, Ge on equivalent Leq (note that we treat strict and non-strict the same way):
-- Fixme: Some way to treat strict/non-strict with integer variables differently
scanHypothesis (FComp Lt e1 e2) False intervals = scanHypothesis (FComp Le e1 e2) False intervals 
scanHypothesis (FComp Ge e1 e2) False intervals = scanHypothesis (FComp Le e2 e1) False intervals
scanHypothesis (FComp Gt e1 e2) False intervals = scanHypothesis (FComp Le e2 e1) False intervals
scanHypothesis _ _False intervals = intervals

{-|
  Replace within a formula some comparisons with FTrue/FFalse, namely
  those comparisons that on the given box can be easily seen to be true/false.
  -}
evalF_comparisons :: VarBoundMap -> F -> F
evalF_comparisons intervals = eC
  where
  eC FTrue  = FTrue
  eC FFalse = FFalse
  eC (FNot f) = FNot (eC f)
  eC (FConn op f1 f2) = FConn op (eC f1) (eC f2)
  eC (FComp Gt e1 e2) = eC $ FComp Lt e2 e1
  eC (FComp Ge e1 e2) = eC $ FComp Le e2 e1
  eC (FComp Eq e1 e2) = eC $ FConn And (FComp Le e2 e1) (FComp Le e1 e2)
  eC f@(FComp Le e1 e2) =
    case (eE e1, eE e2) of
      ((_, Just e1R), (Just e2L, _)) | e1R <= e2L -> FTrue
      ((Just e1L, _), (_, Just e2R)) | e2R <  e1L -> FFalse 
      _ -> f
  eC f@(FComp Lt e1 e2) =
    case (eE e1, eE e2) of
      ((_, Just e1R), (Just e2L, _)) | e1R <  e2L -> FTrue
      ((Just e1L, _), (_, Just e2R)) | e2R <= e1L -> FFalse 
      _ -> f
  eE = evalE_Rational intervals
-- x is inconsistent
-- since we have exists x in empty set
-- x > y is False 
-- we use exists instead of forall because we're looking for a model for x

evalE_Rational :: 
  VarBoundMap -> E -> (Maybe Rational, Maybe Rational)
evalE_Rational intervals =
  rationalBounds . evalE (cn . mpBallP p) intervalsMPBall p
  where
  intervalsMPBall = Map.map toMPBall intervals
  toMPBall :: (Maybe Rational, Maybe Rational) -> CN MPBall
  toMPBall (Just l, Just r) = cn $ (mpBallP p l) `hullMPBall` (mpBallP p r) --FIXME: deal with contradictions, inconsistent intervals, directly
  -- If we have an overlapping interval, turn conjunction into False
  -- l = 1, r = 0
  toMPBall _ = CN.noValueNumErrorCertain $ CN.NumError "no bounds"
  p = prec 60 -- Needs to be at least 54 for turning double pi from Why3 into real pi FIXME: behaviour with very high prec (say prec 1000)?
  rationalBounds :: CN MPBall -> (Maybe Rational, Maybe Rational)
  rationalBounds cnBall =
    case CN.toEither cnBall of
      Right ball -> 
        let (l,r) = endpoints ball in
        (Just (rational l), Just (rational r)) 
      _ -> (Nothing, Nothing)

updateUpper :: 
    CanMinMaxSameType a =>
    (t, Maybe a) -> (t1, Maybe a) -> (t1, Maybe a)
updateUpper (_,Just u2) (l, Just u1) = (l, Just $ min u1 u2)
updateUpper (_,Just u2) (l, Nothing) = (l, Just $ u2)
updateUpper (_,Nothing) (l, Just u1) = (l, Just $ u1)
updateUpper (_,Nothing) (l, Nothing) = (l, Nothing)
--updateUpper _ _ = error "DeriveBounds: updateUpper failed"

updateLower :: 
    CanMinMaxSameType a =>
    (Maybe a, t) -> (Maybe a, t1) -> (Maybe a, t1)
updateLower (Just l2,_) (Just l1,u) = (Just $ max l1 l2, u)
updateLower (Just l2,_) (Nothing,u) = (Just $ l2, u)
updateLower (Nothing,_) (Just l1,u) = (Just $ l1, u)
updateLower (Nothing,_) (Nothing,u) = (Nothing, u)
--updateLower _ _ = error "DeriveBounds: updateLower failed"

-- | compute the value of E with Vars at specified points
-- | (a generalised version of computeE)
evalE :: 
  (Ring v, CanDivSameType v, CanPowBy v Integer,
   CanMinMaxSameType v, CanAbsSameType v, 
   CanPowBy v v, CanSqrtSameType v, CanSinCosSameType v,
   IsInterval v, CanAddThis v Integer, HasDyadics v, CanMinMaxSameType (IntervalEndpoint v),
   v ~ CN MPBall 
  ) 
  =>
  (Rational -> v) ->
  Map.Map VarName v -> Precision -> E -> v
evalE fromR (varMap :: Map.Map VarName v) p = evalVM
  where
  evalVM :: E -> v
  evalVM (EBinOp op e1 e2) = 
    case op of
      Min -> evalVM e1 `min` evalVM e2
      Max -> evalVM e1 `max` evalVM e2
      Add -> evalVM e1 + evalVM e2
      Sub -> evalVM e1 - evalVM e2
      Mul -> evalVM e1 * evalVM e2
      Div -> evalVM e1 / evalVM e2
      Pow -> evalVM e1 ^ evalVM e2 
      Mod -> evalVM e1 `mod` evalVM e2
  evalVM (EUnOp op e) =
    case op of
      Abs -> abs (evalVM e)
      Sqrt -> sqrt (evalVM e)
      Negate -> negate (evalVM e)
      Sin -> sin (evalVM e)
      Cos -> cos (evalVM e)
  evalVM (Var v) = 
    case Map.lookup v varMap of
      Nothing -> 
        error ("evalE: varMap does not contain variable " ++ show v)
      Just r -> r
  evalVM Pi      = cn (piBallP p)
  evalVM (Lit i) = (fromR i)
  evalVM (PowI e i) = evalVM e  ^ i
  evalVM (Float32 _ e) = (onePlusMinusEpsilon * (evalVM e)) + zeroPlusMinusEpsilon
    where
      eps :: v
      eps = convertExactly $ dyadic $ 0.5^23
      onePlusMinusEpsilon :: v
      onePlusMinusEpsilon = fromEndpointsAsIntervals (1 + (-eps)) (1 + eps)
      epsD :: v
      epsD = convertExactly $ dyadic $ 0.5^149
      zeroPlusMinusEpsilon :: v
      zeroPlusMinusEpsilon = fromEndpointsAsIntervals (-epsD) epsD
  evalVM (Float64 _ e) = (onePlusMinusEpsilon * (evalVM e)) + zeroPlusMinusEpsilon
    where
      eps :: v
      eps = convertExactly $ dyadic $ 0.5^52
      onePlusMinusEpsilon :: v
      onePlusMinusEpsilon = fromEndpointsAsIntervals  (1 + (-eps)) (1 + eps)
      epsD :: v
      epsD = convertExactly $ dyadic $ 0.5^1074
      zeroPlusMinusEpsilon :: v
      zeroPlusMinusEpsilon = fromEndpointsAsIntervals (-epsD) epsD
  evalVM (RoundToInteger mode e) = fmap (roundMPBall mode) (evalVM e)
  evalVM e = error $ "evalE: undefined for: " ++ show e

roundMPBall :: (Real (IntervalEndpoint i), IsInterval i, IsInterval p,
 ConvertibleExactly Integer (IntervalEndpoint p)) =>
  RoundingMode -> i -> p
roundMPBall mode i =
        let 
          (l', r') = endpoints i
          l = toRational l'
          r = toRational r'
          lFloor = floor l
          lCeil = ceiling l
          rFloor = floor r
          rCeil = ceiling r
        in case mode of 
          RNE ->
            fromEndpoints
              (if l - lFloor == 0.5
                then (if even lFloor then convertExactly lFloor else convertExactly lCeil) 
                else (if l - lFloor < 0.5 then convertExactly lFloor else convertExactly lCeil))
              (if r - rFloor == 0.5
                then (if even rFloor then convertExactly rFloor else convertExactly rCeil)
                else (if r - rFloor < 0.5 then convertExactly rFloor else convertExactly rCeil))
          RTP -> fromEndpoints (convertExactly lCeil)  (convertExactly rCeil)
          RTN -> fromEndpoints (convertExactly lFloor) (convertExactly rFloor)
          RTZ -> 
            fromEndpoints 
              (if isCertainlyPositive l then convertExactly lFloor else convertExactly lCeil) -- FIXME: check isCertainNegative?
              (if isCertainlyPositive r then convertExactly rFloor else convertExactly rCeil)
          RNA ->
            fromEndpoints
              (if l - lFloor == 0.5
                then (if isCertainlyPositive l then convertExactly lCeil else convertExactly lFloor) -- FIXME: check isCertainNegative?
                else (if l - lFloor < 0.5 then convertExactly lFloor else convertExactly lCeil))
              (if r  - rFloor == 0.5
                then (if isCertainlyPositive r then convertExactly rCeil else convertExactly rFloor)
                else (if r - rFloor < 0.5 then convertExactly rFloor else convertExactly rCeil))

checkFWithEval :: F -> VarBoundMap -> Maybe Bool
checkFWithEval f' varBoundMap = aux f'
  where
    aux (FComp op e1 e2) =
      case (mE1L, mE1R, mE2L, mE2R) of
        (Just e1L, Just e1R, Just e2L, Just e2R) -> decideKleenean op (e1L, e1R) (e2L, e2R)
        (_, _, _, _) -> Nothing
      where
        (mE1L, mE1R) = evalE_Rational varBoundMap e1
        (mE2L, mE2R) = evalE_Rational varBoundMap e2

        decideKleenean Lt (l1, r1) (l2, r2)
          | r1 < l2   = Just True
          | r2 <= l1  = Just False
          | otherwise = Nothing
        decideKleenean Le (l1, r1) (l2, r2)
          | r1 <= l2  = Just True
          | r2 < l1   = Just False
          | otherwise = Nothing
        decideKleenean Ge x y = decideKleenean Le y x
        decideKleenean Gt x y = decideKleenean Lt y x
        decideKleenean Eq x y = --TODO: Use guards here
          case decideKleenean Ge y x of
            Just False -> Just False
            Just True  -> decideKleenean Le y x
            Nothing    -> 
              case decideKleenean Le y x of
                Just False -> Just False
                _          -> Nothing
        
    aux (FConn op f1 f2) =
      case op of
        And   -> 
          case (f1Val, f2Val) of
            (Just r1, Just r2) -> Just $ r1 && r2
            (_, _)             -> Nothing
        Or    -> 
          case (f1Val, f2Val) of
            (Just r1, Just r2) -> Just $ r1 || r2
            (_, _)             -> Nothing
        Impl  -> 
          case (f1Val, f2Val) of
            (Just r1, Just r2) -> Just $ not r1 || r2
            (_, _)             -> Nothing
      where
        f1Val = aux f1
        f2Val = aux f2
    aux (FNot f) = not <$> aux f
    aux FTrue    = Just True
    aux FFalse   = Just False