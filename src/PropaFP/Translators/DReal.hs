{-# LANGUAGE LambdaCase #-}
module PropaFP.Translators.DReal where

import MixedTypesNumPrelude

import PropaFP.Expression

import Data.Ratio
import System.IO.Unsafe (unsafePerformIO)
import PropaFP.VarMap (TypedVarInterval(TypedVar), VarType (Real, Integer), TypedVarMap)

fToConjunction :: F -> [F]
fToConjunction (FConn And f1 f2) = fToConjunction f1 ++ fToConjunction f2
fToConjunction (FNot (FConn Or f1 f2)) = fToConjunction (FNot f1) ++ fToConjunction (FNot f2)
fToConjunction (FNot (FConn Impl f1 f2)) = fToConjunction f1 ++ fToConjunction (FNot f2)
fToConjunction f = [f]

conjunctionToSMT :: [F] -> String
conjunctionToSMT []       = ""
conjunctionToSMT (f : fs) = "(assert " ++ formulaToSMT f 1 ++ ")\n" ++ conjunctionToSMT fs

formulaToSMT :: F -> Integer -> String
formulaToSMT (FConn op f1 f2) numTabs = 
  case op of
    And   -> "\n" ++ concat (replicate numTabs "\t") ++ "(and " ++ formulaToSMT f1 (numTabs + 1) ++ " " ++ formulaToSMT f2 (numTabs + 1) ++ ")"
    Or    -> "\n" ++ concat (replicate numTabs "\t") ++ "(or " ++ formulaToSMT f1 (numTabs + 1) ++ " " ++ formulaToSMT f2 (numTabs + 1) ++ ")"
    Impl  -> "\n" ++ concat (replicate numTabs "\t") ++ "(or " ++ formulaToSMT (FNot f1) (numTabs + 1) ++ formulaToSMT f2 (numTabs + 1) ++ ")"
formulaToSMT (FComp op e1 e2) numTabs = 
  case op of
    Ge -> "\n" ++ concat (replicate numTabs "\t") ++ "(>= " ++ "\n" ++ concat (replicate (numTabs + 1) "\t") ++ expressionToSMT e1 ++ "\n" ++ concat (replicate (numTabs + 1) "\t") ++ expressionToSMT e2 ++ ")"
    Gt -> "\n" ++ concat (replicate numTabs "\t") ++ "(> "  ++ "\n" ++ concat (replicate (numTabs + 1) "\t") ++ expressionToSMT e1 ++ "\n" ++ concat (replicate (numTabs + 1) "\t") ++ expressionToSMT e2 ++ ")"
    Lt -> "\n" ++ concat (replicate numTabs "\t") ++ "(< "  ++ "\n" ++ concat (replicate (numTabs + 1) "\t") ++ expressionToSMT e1 ++ "\n" ++ concat (replicate (numTabs + 1) "\t") ++ expressionToSMT e2 ++ ")"
    Le -> "\n" ++ concat (replicate numTabs "\t") ++ "(<= " ++ "\n" ++ concat (replicate (numTabs + 1) "\t") ++ expressionToSMT e1 ++ "\n" ++ concat (replicate (numTabs + 1) "\t") ++ expressionToSMT e2 ++ ")"
    Eq -> "\n" ++ concat (replicate numTabs "\t") ++ "(= "  ++ "\n" ++ concat (replicate (numTabs + 1) "\t") ++ expressionToSMT e1 ++ "\n" ++ concat (replicate (numTabs + 1) "\t") ++ expressionToSMT e2 ++ ")"
formulaToSMT (FNot f) numTabs = "\n" ++ concat (replicate numTabs "\t") ++ "(not " ++ formulaToSMT f (numTabs + 1) ++ ")"
formulaToSMT FTrue numTabs = "\n" ++ concat (replicate numTabs "\t") ++ "true"
formulaToSMT FFalse numTabs = "\n" ++ concat (replicate numTabs "\t") ++ "false"

expressionToSMT :: E -> String
expressionToSMT (EBinOp op e1 e2) =
  case op of
    Add -> "(+ " ++ expressionToSMT e1 ++ " " ++ expressionToSMT e2 ++ ")"
    Sub -> "(- " ++ expressionToSMT e1 ++ " " ++ expressionToSMT e2 ++ ")"
    Mul -> "(* " ++ expressionToSMT e1 ++ " " ++ expressionToSMT e2 ++ ")"
    Div -> "(/ " ++ expressionToSMT e1 ++ " " ++ expressionToSMT e2 ++ ")"
    Min -> "(min " ++ expressionToSMT e1 ++ " " ++ expressionToSMT e2 ++ ")"
    Max -> "(max " ++ expressionToSMT e1 ++ " " ++ expressionToSMT e2 ++ ")"
    Pow -> "(^ "  ++ expressionToSMT e1 ++ " " ++ expressionToSMT e2 ++ ")"
    Mod -> "(mod "  ++ expressionToSMT e1 ++ " " ++ expressionToSMT e2 ++ ")" --TODO: Warn dreal users
expressionToSMT (EUnOp op e) =
  case op of
    Sqrt -> "(sqrt " ++ expressionToSMT e ++ ")"
    Negate -> "(* -1 " ++ expressionToSMT e ++ ")"
    Abs -> "(abs " ++ expressionToSMT e ++ ")"
    Sin -> "(sin " ++ expressionToSMT e ++ ")"
    Cos -> "(cos " ++ expressionToSMT e ++ ")"
expressionToSMT (PowI e i) = "(^ " ++ expressionToSMT e ++ " " ++ show i ++ ")"
expressionToSMT (Var e) = e
expressionToSMT (Lit e) = 
  case denominator e of
    1 -> show numE
    _ -> "(/ " ++ show numE ++ " " ++ show denE ++ ")"
    where
      numE = numerator e
      denE = denominator e
expressionToSMT Pi = "(* 4.0 (atan 1.0))" -- Equivalent to pi
expressionToSMT (RoundToInteger mode e) = 
  -- TODO: Warn about non-standard SMT
  case mode of
    RNE -> "(to_int_rne " ++ expressionToSMT e ++ ")"
    RTP -> "(to_int_rtp " ++ expressionToSMT e ++ ")"
    RTN -> "(to_int_rtn " ++ expressionToSMT e ++ ")"
    RTZ -> "(to_int_rtz " ++ expressionToSMT e ++ ")"
    RNA -> "(to_int_rna " ++ expressionToSMT e ++ ")"
expressionToSMT (Float mode e)   = error "Float with unknown precision not supported"
  -- TODO: Warn about non-standard SMT
--   case mode of
--     RNE -> "(float_rne " ++ expressionToSMT e ++ ")"
--     RTP -> "(float_rtp " ++ expressionToSMT e ++ ")"
--     RTN -> "(float_rtn " ++ expressionToSMT e ++ ")"
--     RTZ -> "(float_rtz " ++ expressionToSMT e ++ ")"
--     RNA -> "(float_rne " ++ expressionToSMT e ++ ")"
expressionToSMT (Float32 mode e) =
  -- TODO: Warn about non-standard SMT
  case mode of
    RNE -> "(float32_rne " ++ expressionToSMT e ++ ")"
    RTP -> "(float32_rtp " ++ expressionToSMT e ++ ")"
    RTN -> "(float32_rtn " ++ expressionToSMT e ++ ")"
    RTZ -> "(float32_rtz " ++ expressionToSMT e ++ ")"
    RNA -> "(float32_rne " ++ expressionToSMT e ++ ")"
expressionToSMT (Float64 mode e) =
  -- TODO: Warn about non-standard SMT
  case mode of
    RNE -> "(float64_rne " ++ expressionToSMT e ++ ")"
    RTP -> "(float64_rtp " ++ expressionToSMT e ++ ")"
    RTN -> "(float64_rtn " ++ expressionToSMT e ++ ")"
    RTZ -> "(float64_rtz " ++ expressionToSMT e ++ ")"
    RNA -> "(float64_rne " ++ expressionToSMT e ++ ")"

formulaAndVarMapToDReal :: F -> TypedVarMap -> String
formulaAndVarMapToDReal f typedVarMap =
  "(set-logic QF_NRA)\n" ++
  variablesAsString typedVarMap ++
  (conjunctionToSMT . fToConjunction) f ++
  "(check-sat)\n" ++
  "(get-model)\n" ++
  "(exit)\n"
  where
    showVarType Integer = "Int"
    showVarType Real = "Real"
      
    showRational x = "(/ " ++ show (numerator x) ++ " " ++ show (denominator x) ++ ")"

    variablesAsString [] = ""
    variablesAsString ((TypedVar (varName, (leftBound, rightBound)) varType) : typedVarIntervals) =
      "(declare-fun " ++ varName ++ " () " ++ showVarType varType ++ ")\n" ++
      "(assert (<= " ++ showRational leftBound ++ " " ++ varName ++ "))\n" ++
      "(assert (<= " ++ varName ++ " " ++ showRational rightBound ++ "))\n" ++ variablesAsString typedVarIntervals

disjunctionExpressionsToSMT :: [ESafe] -> String
disjunctionExpressionsToSMT es = 
  "\n\t\t\t(or " ++ 
    concatMap 
    (\case
      EStrict e    -> "\n\t\t\t\t(> " ++ expressionToSMT e ++ " 0)"
      ENonStrict e -> "\n\t\t\t\t(>= " ++ expressionToSMT e ++ " 0)"
    ) 
    es ++ 
  ")"

cnfExpressionsToSMT :: [[ESafe]] -> String
cnfExpressionsToSMT disjunctions = "\n\t\t(and " ++ concatMap disjunctionExpressionsToSMT disjunctions ++ ")"

cnfExpressionAndDomainsToDreal :: [[ESafe]] -> [(String, (Rational, Rational))] -> [(String, (Rational, Rational))] -> String
cnfExpressionAndDomainsToDreal cnf realDomains intDomains =
  "(set-option :precision 1e-300)" ++
  "\n(assert " ++ forAll (cnfExpressionsToSMT cnf) ++ ")\n(check-sat)\n(exit)"
  where
    forAll vc =
      "\n(forall (" ++ concatMap (\(v, (_, _)) -> "\n\t(" ++ v ++ " Real)") realDomains ++ concatMap (\(v, (_, _)) -> "\n\t(" ++ v ++ " Int)") intDomains ++ "\n)" ++ 
      "\n\t(=>" ++ 
      "\n\t\t(and " ++ concatMap (\(v, (vL, vR)) -> "\n\t\t\t(>= " ++ v ++ " " ++ expressionToSMT (Lit vL) ++ ") (<= " ++ v ++ " " ++ expressionToSMT (Lit vR) ++ ")") (realDomains ++ intDomains) ++ "\n\t\t)" ++
      vc ++ "))"   
    -- forAll vc =
    --   "(forall (" ++ concatMap (\(v, (_, _)) -> "(" ++ v ++ " Real)") realDomains ++ concatMap (\(v, (_, _)) -> "(" ++ v ++ " Int)") intDomains ++ ")" ++ 
    --   "(=>" ++ 
    --   "(and " ++ concatMap (\(v, (vL, vR)) -> "(>= " ++ v ++ " " ++ expressionToSMT (Lit vL) ++ ")(<= " ++ v ++ " " ++ expressionToSMT (Lit vR) ++ ")") (realDomains ++ intDomains) ++ ")" ++
    --   vc ++ "))"

runDRealTranslatorCNFWithVarMap :: [[ESafe]] -> [(String, (Rational, Rational))] -> [(String, (Rational, Rational))] -> IO ()
runDRealTranslatorCNFWithVarMap cnf realVarMap intVarMap =
  do
  putStrLn "Running Haskell to dReal translator for Expressions"
  putStr "Enter target file name: "
  fileName <- getLine
  writeFile fileName $ cnfExpressionAndDomainsToDreal cnf realVarMap intVarMap

runDRealTranslatorCNF :: [[ESafe]] -> IO ()
runDRealTranslatorCNF cnf = do
  putStrLn "Running Haskell to dReal translator for Expressions"
  -- PutStr "Enter tool: "
  putStr "Enter target file name: "
  fileName <- getLine
  putStr "How many Real vars in expression? "
  numReals <- getLine
  putStr "How many Int vars in expression? "
  numInts <- getLine
  writeFile fileName (cnfExpressionAndDomainsToDreal cnf (parseDomains "real var name? " (read numReals)) (parseDomains "integer var name? " (read numInts)))
  where
    parseDomains :: String -> Integer -> [(String, (Rational, Rational))]
    parseDomains _ 0 = []
    parseDomains msg n =

      (unsafePerformIO (getVar msg), (unsafePerformIO (parseRational "lower bound") :: Rational, unsafePerformIO (parseRational "upper bound") :: Rational))
      : parseDomains msg (n - 1)

    getVar message = do
      putStr message
      getLine

    parseRational message = do
      putStr (message ++ " numerator? ")
      num <- getLine
      putStr (message ++ " denominator? ")
      den <- getLine
      return ((read num :: Integer) / (read den :: Integer))
