{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE LambdaCase #-}
module PropaFP.Expression where

import MixedTypesNumPrelude

import qualified Prelude as P

import qualified Data.Map as Map
import Data.List (nub, delete)

import Test.QuickCheck

import Debug.Trace (trace)
import Test.QuickCheck.State (State(randomSeed))
import Data.Ratio
import PropaFP.VarMap
import AERN2.Normalize (CanNormalize(normalize))

data BinOp = Add | Sub | Mul | Div | Min | Max | Pow | Mod
  deriving (Show, P.Eq, P.Ord)
data UnOp  = Sqrt | Negate | Abs | Sin | Cos
  deriving (Show, P.Eq, P.Ord)

data RoundingMode = RNE | RTP | RTN | RTZ | RNA deriving (Show, P.Eq, P.Ord)
-- | The E type represents the inequality: expression :: E >= 0
-- TODO: Add rounding operator with certain epsilon/floating-point type
data E = EBinOp BinOp E E | EUnOp UnOp E | Lit Rational | Var String | PowI E Integer | Float32 RoundingMode E | Float64 RoundingMode E | Float RoundingMode E | Pi | RoundToInteger RoundingMode E
  deriving (Show, P.Eq, P.Ord)

data ESafe = EStrict E | ENonStrict E
  deriving (Show, P.Eq, P.Ord)
data Comp = Gt | Ge | Lt | Le | Eq
  deriving (Show, P.Eq, P.Ord)

data Conn = And | Or | Impl
  deriving (Show, P.Eq, P.Ord)

-- TODO: Could make prover work on 'Comp E E' (call it EComp)
-- Other method, add flag to E, whether or not it is strict

-- | The F type is used to specify comparisons between E types
-- and logical connectives between F types
data F = FComp Comp E E | FConn Conn F F | FNot F | FTrue | FFalse
  deriving (Show, P.Eq, P.Ord)

lengthF :: F -> Integer
lengthF (FConn _ f1 f2) = lengthF f1 + lengthF f2
lengthF (FComp _ e1 e2) = lengthE e1 + lengthE e2
lengthF (FNot f)        = lengthF f
lengthF FTrue           = 1
lengthF FFalse          = 1

lengthE :: E -> Integer
lengthE (EBinOp _ e1 e2) = lengthE e1 + lengthE e2
lengthE (EUnOp _ e)      = lengthE e
lengthE (Var _) = 1
lengthE (Lit _) = 1
lengthE (PowI e _) = lengthE e
lengthE (Float _ e) = lengthE e
lengthE (Float32 _ e) = lengthE e
lengthE (Float64 _ e) = lengthE e
lengthE Pi = 1
lengthE (RoundToInteger _ e) = lengthE e

newtype Name = Name String deriving Show

instance Arbitrary Name where
  arbitrary =
    oneof
    [
      return (Name "a"),
      return (Name "b"),
      return (Name "c"),
      return (Name "d"),
      return (Name "e"),
      return (Name "f"),
      return (Name "g"),
      return (Name "h"),
      return (Name "i"),
      return (Name "j"),
      return (Name "k"),
      return (Name "l")
    ]

instance Arbitrary UnOp where
  arbitrary =
    frequency [(int 11, return Negate), (int 1, return Abs), (int 4, return Sin), (int 4, return Cos)]

instance Arbitrary BinOp where
  arbitrary =
    frequency [(int 10, return Add), (int 10, return Sub), (int 10, return Mul), (int 10, return Div), (int 1, return Min), (int 1, return Max)]

instance Arbitrary RoundingMode where
  arbitrary =
    oneof [return RNE, return RTP, return RTN, return RTN]
instance Arbitrary E where
  arbitrary = sized eGenerator
    where
      varName :: Gen Name
      varName = arbitrary

      eGenerator :: Int -> Gen E
      eGenerator n | n>0 =
        oneof
        [
          Lit     <$> fmap toRational (arbitrary :: Gen Integer),
          Var     <$> show <$> varName,
          EUnOp   <$> arbitrary <*> subE,
          EUnOp Sqrt . Lit      <$> fmap getPositive (arbitrary :: Gen (Positive Rational)),
          EBinOp  <$> arbitrary <*> subE <*> subE
          -- PowI    <$> subE <*> fmap getPositive (arbitrary :: Gen (Positive Integer)) -- We do not allow Floats here
        ]
        where
          subE = eGenerator (int (floor (n / 20)))
          sqrtG x = EUnOp Sqrt (Lit x)
      eGenerator _        = oneof [Lit <$> (fmap toRational (arbitrary :: Gen Integer)), Var <$> show <$> varName]
          -- subE = eGenerator (pred n)

instance Arbitrary ESafe where
  arbitrary = randomStrictness <*> randomE
    where
      randomE :: Gen E
      randomE = arbitrary

      randomStrictness = oneof [return EStrict, return ENonStrict]

-- data Comp = Gt | Ge | Lt | Le | Eq
--   deriving (Show, P.Eq)

-- data Conn = And | Or | Impl | Equiv
--   deriving (Show, P.Eq)

-- -- | The F type is used to specify comparisons between E types
-- -- and logical connectives between F types
-- data F = FComp Comp E E | FConn Conn F F | FNot F | FTrue | FFalse
--   deriving (Show, P.Eq)

instance Arbitrary Comp where
  arbitrary = oneof [return Gt, return Ge, return Lt, return Le, return Eq]

instance Arbitrary Conn where
  arbitrary = oneof [return And, return Or, return Impl]

instance Arbitrary F where
  arbitrary = sized fGenerator
    where
      varName :: Gen Name
      varName = arbitrary

      fGenerator :: Int -> Gen F
      fGenerator 0 = oneof [FComp <$> arbitrary <*> arbitrary <*> arbitrary]
      fGenerator n =
        frequency
        [
          (int 10, FComp Eq <$> Var <$> show <$> varName <*> arbitrary),
          (int 30, FComp <$> arbitrary <*> arbitrary <*> arbitrary),
          (int 30, FConn <$> arbitrary <*> subF <*> subF),
          (int 30, FNot  <$> subF)
        ]
        where
          subF = fGenerator (int (floor (n / 20)))
-- Note, does not generate FTrue, FFalse

flipStrictness :: ESafe -> ESafe
flipStrictness (EStrict e)    = ENonStrict e
flipStrictness (ENonStrict e) = EStrict e

-- | Equivalent to E * -1
-- Example: ENonStrict e == e >= 0. negateSafeE (ENonStrict e) == e < 0 == -e > 0 == (EStrict (EUnOp Negate e))
negateSafeE :: ESafe -> ESafe
negateSafeE (EStrict e)     = ENonStrict (EUnOp Negate e)
negateSafeE (ENonStrict e)  = EStrict    (EUnOp Negate e)

extractSafeE :: ESafe -> E
extractSafeE (EStrict e)    = e
extractSafeE (ENonStrict e) = e

fmapESafe :: (E -> E) -> ESafe -> ESafe
fmapESafe f (EStrict e)    = EStrict $ f e
fmapESafe f (ENonStrict e) = ENonStrict $ f e

fToECNF :: F -> [[ESafe]]
fToECNF = fToECNFB False
  where
    fToECNFB :: Bool -> F -> [[ESafe]]
    fToECNFB isNegated (FNot f) = fToECNFB (not isNegated) f
    fToECNFB True (FComp op e1 e2)  = case op of
      Le -> fToECNFB False (FComp Gt e1 e2) -- !(f1 <= f2) -> (f1 > f2)
      Lt -> fToECNFB False (FComp Ge e1 e2)
      Ge -> fToECNFB False (FComp Lt e1 e2)
      Gt -> fToECNFB False (FComp Le e1 e2)
      Eq -> fToECNFB True (FConn And (FComp Ge e1 e2) (FComp Le e1 e2)) -- !(f1 = f2)
    fToECNFB False (FComp op e1 e2) = case op of
      Le -> fToECNFB False (FComp Ge e2 e1) -- f1 <  f2 == f1 - f2 <  0 == -f1 + f2 >= 0
      Lt -> fToECNFB False (FComp Gt e2 e1) -- f1 <= f2 == f1 - f2 <= 0 == -f1 + f2 >  0
      Ge -> [[ENonStrict (EBinOp Sub e1 e2)]]                -- f1 >= f2 == f1 - f2 >= 0 
      Gt -> [[EStrict (EBinOp Sub e1 e2)]]      -- f1 >  f2 == f1 - f2 >  0 
      Eq -> fToECNFB False (FConn And (FComp Ge e1 e2) (FComp Le e1 e2)) -- f1 = f2 == f1 >= f2 /\ f1 <= f2
    fToECNFB True (FConn op f1 f2)  = case op of
      And     -> [d1 ++ d2 | d1 <- fToECNFB True f1, d2 <- fToECNFB True f2]
      Or      -> fToECNFB True f1 ++ fToECNFB True f2
      Impl    -> fToECNFB False f1 ++ fToECNFB True f2 -- !(!p \/ q) == p /\ !q
    fToECNFB False (FConn op f1 f2)  = case op of
      And     -> fToECNFB False f1 ++ fToECNFB False f2 -- [e1 /\ e2 /\ (e3 \/ e4)] ++ [p1 /\ (p2 \/ p3) /\ p4] = [e1 /\ e2 /\ (e3 \/ e4) /\ p1 /\ (p2 \/ p3) /\ p4]
      Or      -> [d1 ++ d2 | d1 <- fToECNFB False f1, d2 <- fToECNFB False f2] -- [e1 /\ e2 /\ (e3 \/ e4)] \/ [p1 /\ (p2 \/ p3) /\ p4] 
      Impl    -> [d1 ++ d2 | d1 <- fToECNFB True f1, d2 <- fToECNFB False f2]
    -- fToECNFB isNegated FTrue  _  = error "fToECNFB for FTrue undefined"  $ Lit 1.0
    -- fToECNFB isNegated FFalse _  = error "fToECNFB for FFalse undefined" $ Lit $ -1.0
    fToECNFB True  FTrue   = fToECNFB False FFalse
    fToECNFB True  FFalse  = fToECNFB False FTrue
    fToECNFB False FTrue     = [[ENonStrict (Lit 1.0)]]
    fToECNFB False FFalse    = [[ENonStrict (Lit (-1.0))]]

fToEDNF :: F -> [[ESafe]]
fToEDNF = fToEDNFB False
  where
    fToEDNFB :: Bool -> F -> [[ESafe]]
    fToEDNFB isNegated (FNot f) = fToEDNFB (not isNegated) f
    fToEDNFB True (FComp op e1 e2) = case op of
      Le -> fToEDNFB False (FComp Gt e1 e2)
      Lt -> fToEDNFB False (FComp Ge e1 e2)
      Ge -> fToEDNFB False (FComp Lt e1 e2)
      Gt -> fToEDNFB False (FComp Le e1 e2)
      Eq -> fToEDNFB True (FConn And (FComp Ge e1 e2) (FComp Le e1 e2)) -- !(f1 = f2)
      -- Eq -> [[EStrict (EBinOp Sub e1 e2)], [EStrict (EBinOp Sub e2 e1)]]
    fToEDNFB False (FComp op e1 e2) = case op of
      Le -> fToEDNFB False (FComp Ge e2 e1)
      Lt -> fToEDNFB False (FComp Gt e2 e1)
      Ge -> [[ENonStrict (EBinOp Sub e1 e2)]]
      Gt -> [[EStrict (EBinOp Sub e1 e2)]]
      Eq -> fToEDNFB False (FConn And (FComp Ge e1 e2) (FComp Le e1 e2))
      -- Eq -> [[ENonStrict (EBinOp Sub e1 e2), ENonStrict (EBinOp Sub e2 e1)]]
    fToEDNFB True (FConn op f1 f2) = case op of
      And  -> fToEDNFB True f1 ++ fToEDNFB True f2
      Or   -> [d1 ++ d2 | d1 <- fToEDNFB True f1, d2 <- fToEDNFB True f2]
      Impl -> [d1 ++ d2 | d1 <- fToEDNFB False f1, d2 <- fToEDNFB True f2]
    fToEDNFB False (FConn op f1 f2) = case op of
      And  -> [d1 ++ d2 | d1 <- fToEDNFB False f1, d2 <- fToEDNFB False f2]
      Or   -> fToEDNFB False f1 ++ fToEDNFB False f2
      Impl -> fToEDNFB True f1 ++ fToEDNFB False f2
    fToEDNFB True  FTrue   = fToEDNFB False FFalse
    fToEDNFB True  FFalse  = fToEDNFB False FTrue
    fToEDNFB False FTrue   = [[ENonStrict (Lit 1.0)]]
    fToEDNFB False FFalse  = [[ENonStrict (Lit (-1.0))]]

-- Eq -> fToEDNFB True (FConn And (FComp Ge e1 e2) (FComp Le e1 e2)) -- !(f1 = f2)
-- Eq -> fToEDNFB False (FConn And (FComp Ge e1 e2) (FComp Le e1 e2))

fToFDNF :: F -> [[F]]
fToFDNF = fToFDNFB False
  where
    fToFDNFB :: Bool -> F -> [[F]]
    fToFDNFB isNegated (FNot f) = fToFDNFB (not isNegated) f
    fToFDNFB True f@FComp {} =
      case f of
        -- e1 < e2
        FComp Ge e1 e2 -> [[FComp Gt e2 e1]]
        -- e1 <= e2
        FComp Gt e1 e2 -> [[FComp Ge e2 e1]]
        -- e1 > e2
        FComp Le e1 e2 -> [[FComp Gt e1 e2]]
        -- e1 >= e2
        FComp Lt e1 e2 -> [[FComp Ge e1 e2]]
        FComp Eq e1 e2 -> fToFDNFB False $ FConn Or (FComp Gt e1 e2) (FComp Gt e2 e1)
    fToFDNFB False f@FComp {} =
      case f of
        FComp Ge _ _ -> [[f]]
        FComp Gt _ _ -> [[f]]
        FComp Le e1 e2 -> [[FComp Ge e2 e1]]
        FComp Lt e1 e2 -> [[FComp Gt e2 e1]]
        FComp Eq e1 e2 -> [[FComp Ge e1 e2, FComp Ge e2 e1]]
    -- fToFDNFB True  f@FComp {} = [[FNot f]]
    -- fToFDNFB False f@FComp {} = [[f]]
    fToFDNFB True (FConn op f1 f2) = case op of
      And  -> fToFDNFB True f1 ++ fToFDNFB True f2
      Or   -> [d1 ++ d2 | d1 <- fToFDNFB True f1, d2 <- fToFDNFB True f2]
      Impl -> [d1 ++ d2 | d1 <- fToFDNFB False f1, d2 <- fToFDNFB True f2]
    fToFDNFB False (FConn op f1 f2) = case op of
      And  -> [d1 ++ d2 | d1 <- fToFDNFB False f1, d2 <- fToFDNFB False f2]
      Or   -> fToFDNFB False f1 ++ fToFDNFB False f2
      Impl -> fToFDNFB True f1 ++ fToFDNFB False f2
    fToFDNFB True  FTrue   = fToFDNFB False FFalse
    fToFDNFB True  FFalse  = fToFDNFB False FTrue
    fToFDNFB False FTrue     = [[FTrue]]
    fToFDNFB False FFalse    = [[FFalse]]

eSafeToF :: ESafe -> F
eSafeToF (EStrict e)    = FComp Gt e (Lit 0.0)
eSafeToF (ENonStrict e) = FComp Ge e (Lit 0.0)

eSafeDisjToF :: [ESafe] -> F
eSafeDisjToF []       = error "empty disjunction given to eSafeDisjToF" -- Alternatively, this can be false?
eSafeDisjToF [e]      = eSafeToF e
eSafeDisjToF (e : es) = FConn Or (eSafeToF e) (eSafeDisjToF es)

eSafeCNFToF :: [[ESafe]] -> F
eSafeCNFToF []             = error "empty disjunction given to eSafeCNFToF" -- Alternatively, this can be true?
eSafeCNFToF [disj]         = eSafeDisjToF disj
eSafeCNFToF (disj : disjs) = FConn And (eSafeDisjToF disj) (eSafeCNFToF disjs)

eSafeCNFToDNF :: [[ESafe]] -> [[ESafe]]
eSafeCNFToDNF = fToEDNF . eSafeCNFToF

-- eSafeCNFToESafeDNF :: [[ESafe]] -> [[ESafe]]
-- eSafeCNFToESafeDNF [] = []
-- eSafeCNFToESafeDNF [disjunction] = map (\term -> [term]) disjunction

-- | Add bounds for any Float expressions
-- addRoundingBounds :: E -> [[E]]
-- addRoundingBounds (Float e significand) = [[exactExpression - machineEpsilon], [exactExpression + machineEpsilon]]
--   where
--     exactExpression = addRoundingBounds e
--     machineEpsilon = 2^(-23)
-- addRoundingBounds e = e

-- | Various rules to simplify expressions
simplifyE :: E -> E
simplifyE unsimplifiedE = if unsimplifiedE P.== simplifiedE then simplifiedE else simplifyE simplifiedE
  where
    simplifiedE = simplify unsimplifiedE

    simplify (EBinOp Div e (Lit 1.0)) = e
    simplify (EBinOp Div (Lit 0.0) _) = Lit 0.0
    simplify (EBinOp Mul (Lit (-1.0)) e) = simplify (EUnOp Negate e)
    simplify (EBinOp Mul e (Lit (-1.0))) = simplify (EUnOp Negate e)
    simplify (EBinOp Mul (Lit 0.0) _) = Lit 0.0
    simplify (EBinOp Mul _ (Lit 0.0)) = Lit 0.0
    simplify (EBinOp Mul (Lit 1.0) e) = e
    simplify (EBinOp Mul e (Lit 1.0)) = e
    simplify (EBinOp Add (Lit 0.0) e) = e
    simplify (EBinOp Add e (Lit 0.0)) = e
    simplify (EBinOp Sub e (Lit 0.0)) = e
    simplify (EBinOp Sub e1 e2)       = if e1 P.== e2 then Lit 0.0 else EBinOp Sub (simplifyE e1) (simplifyE e2)
    simplify (EBinOp Pow _ (Lit 0.0)) = Lit 1.0
    simplify (EBinOp Pow e (Lit 1.0)) = e
    simplify (EBinOp Pow e (Lit n))   = if denominator n == 1 then PowI e (numerator n) else EBinOp Pow e (Lit n)
    simplify (PowI _e 0)              = Lit 1.0
    simplify (PowI e 1)               = e
    simplify (EUnOp Negate (Lit 0.0)) = Lit 0.0
    simplify (EUnOp Negate (EUnOp Negate e)) = e
    simplify (EUnOp Sqrt (Lit 0.0))   = Lit 0.0
    simplify (EUnOp Sqrt (Lit 1.0))   = Lit 1.0
    simplify (EUnOp Abs (Lit v))      = Lit (abs v)
    simplify (EBinOp Min e1 e2)       = if e1 P.== e2 then e1 else EBinOp Min (simplifyE e1) (simplifyE e2)
    simplify (EBinOp Max e1 e2)       = if e1 P.== e2 then e1 else EBinOp Max (simplifyE e1) (simplifyE e2)
    simplify (EBinOp op e1 e2)        = EBinOp op (simplify e1) (simplify e2)
    simplify (EUnOp op e)             = EUnOp op (simplify e)
    simplify e                        = e

simplifyF :: F -> F
-- Simplify Or
simplifyF unsimplifiedF = if unsimplifiedF P.== simplifiedF then simplifiedF else simplifyF simplifiedF
  where
    simplifiedF = simplify unsimplifiedF

    -- Collapse x < y OR x = y to x <= y (and similar)
    simplify (FConn Or f1@(FComp Lt l1 r1) f2@(FComp Eq l2 r2)) = if l1 P.== l2 P.&& r1 P.== r2 then FComp Le l1 r1 else FConn Or (simplify f1) (simplify f2)
    simplify (FConn Or f1@(FComp Eq l1 r1) f2@(FComp Lt l2 r2)) = if l1 P.== l2 P.&& r1 P.== r2 then FComp Le l1 r1 else FConn Or (simplify f1) (simplify f2)
    simplify (FConn Or f1@(FComp Gt l1 r1) f2@(FComp Eq l2 r2)) = if l1 P.== l2 P.&& r1 P.== r2 then FComp Ge l1 r1 else FConn Or (simplify f1) (simplify f2)
    simplify (FConn Or f1@(FComp Eq l1 r1) f2@(FComp Gt l2 r2)) = if l1 P.== l2 P.&& r1 P.== r2 then FComp Ge l1 r1 else FConn Or (simplify f1) (simplify f2)

    -- Eliminate implications with opposing conditions where the RHS is the same, replacing the two implications with the RHS
    simplify (FConn And f1@(FConn Impl cond1 branch1) f2@(FConn Impl (FNot cond2) branch2)) =
      if cond1 P.== cond2 && branch1 P.== branch2
        then simplify branch1
        else FConn And (simplify f1) (simplify f2)

    simplify (FConn And _ FFalse)                               = FFalse
    simplify (FConn And FFalse _)                               = FFalse
    simplify (FConn And f FTrue)                                = simplify f
    simplify (FConn And FTrue f)                                = simplify f

    -- Collapse x /\ (!x \/ y) into x /\ y
    simplify (FConn And x1 f2@(FConn Or (FNot x2) y)) = if x1 P.== x2 then simplify (FConn And x1 y) else FConn And (simplify x1) (simplify f2)
    -- Collapse (!x \/ y) /\ x into y /\ x
    simplify (FConn And f1@(FConn Or (FNot x1) y) x2) = if x1 P.== x2 then simplify (FConn And y x2) else FConn And (simplify f1) (simplify x2)
    -- Collapse x /\ (y \/ !x) into x /\ y
    simplify (FConn And x1 f2@(FConn Or y (FNot x2))) = if x1 P.== x2 then simplify (FConn And x1 y) else FConn And (simplify x1) (simplify f2)
    -- Collapse (y \/ !x) /\ x into y /\ x
    simplify (FConn And f1@(FConn Or y (FNot x1)) x2) = if x1 P.== x2 then simplify (FConn And y x2) else FConn And (simplify f1) (simplify x2)

    simplify (FConn And f1@(FConn Or v1 v2) f2@(FNot v3))
      -- Collapse (x \/ y) /\ !x into y /\ !x
      | v3 P.== v1 = simplify (FConn And v2 (FNot v3))
      -- Collapse (y \/ x) /\ !x into y /\ !x
      | v3 P.== v2 = simplify (FConn And v1 (FNot v3))
      -- Turn x /\ !x into false
      | f1 P.== v3 = FFalse
      | otherwise = FConn And (simplify f1) (simplify f2)

    simplify (FConn And f1@(FNot v1) f2@(FConn Or v2 v3))
      -- Collapse !x /\ (x \/ y) into !x /\ y
      | v1 P.== v2 = simplify (FConn And (FNot v1) v3)
      -- Collapse !x /\ (y \/ x) into !x /\ y
      | v1 P.== v3 = simplify (FConn And (FNot v1) v2)
      -- Turn !x /\ x into false
      | v1 P.== f2 = FFalse
      | otherwise = FConn And (simplify f1) (simplify f2)

    -- Collapse x /\ (x -> y) into x /\ y
    simplify (FConn And x1 f2@(FConn Impl x2 y)) = if x1 P.== x2 then simplify (FConn And x1 y) else FConn And (simplify x1) (simplify f2)
    -- Collapse (x -> y) /\ x into y /\ x
    simplify (FConn And f1@(FConn Impl x1 y) x2) = if x1 P.== x2 then simplify (FConn And y x2) else FConn And (simplify f1) (simplify x2)

    -- Boolean Rules
    -- And
    -- And contradictions and eliminations
    simplify (FConn And f1 fn2@(FNot f2))                       = if f1 P.== f2 then FFalse else FConn And (simplify f1) (simplify fn2)
    simplify (FConn And fn1@(FNot f1) f2)                       = if f1 P.== f2 then FFalse else FConn And (simplify fn1) (simplify f2)
    -- And collapse to Eq
    simplify (FConn And f1@(FComp Ge l1 r1) f2@(FComp Ge l2 r2)) = if l1 P.== r2 && l2 P.== r1 then simplify (FComp Eq l1 r1) else FConn And (simplify f1) (simplify f2)
    -- simplify (FConn And f1@(FComp Ge e1 (Var v1)) f2@(FComp Ge (Var v2) e2)) = if e1 P.== e2 && v1 == v2 then simplify (FComp Eq (Var v1) e1) else FConn And (simplify f1) (simplify f2)
    simplify (FConn And f1@(FComp Le l1 r1) f2@(FComp Le l2 r2)) = if l1 P.== r2 && l2 P.== r1 then simplify (FComp Eq l1 r1) else FConn And (simplify f1) (simplify f2)
    -- simplify (FConn And f1@(FComp Le e1 (Var v1)) f2@(FComp Le (Var v2) e2)) = if e1 P.== e2 && v1 == v2 then simplify (FComp Eq (Var v1) e1) else FConn And (simplify f1) (simplify f2)
    simplify (FConn And f1@(FComp Ge l1 r1) f2@(FComp Le l2 r2)) = if l1 P.== l2 && r1 P.== r2 then simplify (FComp Eq l1 r1) else FConn And (simplify f1) (simplify f2)
    -- simplify (FConn And f1@(FComp Ge e1 (Var v1)) f2@(FComp Le e2 (Var v2))) = if e1 P.== e2 && v1 == v2 then simplify (FComp Eq (Var v1) e1) else FConn And (simplify f1) (simplify f2)
    simplify (FConn And f1@(FComp Le l1 r1) f2@(FComp Ge l2 r2)) = if l1 P.== l2 && r1 P.== r2 then simplify (FComp Eq l1 r1) else FConn And (simplify f1) (simplify f2)
    -- simplify (FConn And f1@(FComp Le (v1) e1) f2@(FComp Ge (v2) e2)) = if e1 P.== e2 && v1 == v2 then simplify (FComp Eq (Var v1) e1) else FConn And (simplify f1) (simplify f2)
    simplify (FConn And f1 f2)                                  = if f1 P.== f2 then simplify f1 else FConn And (simplify f1) (simplify f2)
    -- Or
    simplify (FConn Or _ FTrue)                                 = FTrue
    simplify (FConn Or FTrue _)                                 = FTrue
    simplify (FConn Or f FFalse)                                = simplify f
    simplify (FConn Or FFalse f)                                = simplify f

    simplify (FConn Or f1 fn2@(FNot f2))                        = if f1 P.== f2 then FTrue else FConn Or (simplify f1) (simplify fn2)
    simplify (FConn Or fn1@(FNot f1) f2)                        = if f1 P.== f2 then FTrue else FConn Or (simplify fn1) (simplify f2)

    simplify (FConn Or f1 f2)                                   = if f1 P.== f2 then simplify f1 else FConn Or (simplify f1) (simplify f2)
    -- Impl
    simplify (FConn Impl FFalse _)                              = FTrue
    simplify (FConn Impl _ FTrue)                               = FTrue
    simplify (FConn Impl f FFalse)                              = simplify (FNot f)
    simplify (FConn Impl FTrue f)                               = simplify f
    -- Impl tautologies and eliminations
    simplify (FConn Impl f1 fn2@(FNot f2))                      = if f1 P.== f2 then simplify (FNot f1) else FConn Impl (simplify f1) (simplify fn2)
    simplify (FConn Impl fn1@(FNot f1) f2)                      = if f1 P.== f2 then simplify f1 else FConn Impl (simplify fn1) (simplify f2)
    simplify (FConn Impl f1 f2)                                 = if f1 P.== f2 then FTrue else FConn Impl (simplify f1) (simplify f2)

    -- Evaluate rational comparisons
    simplify (FComp op (Lit l1) (Lit l2)) =
      case op of
        Gt -> boolToF $ l1 >  l2
        Ge -> boolToF $ l1 >= l2
        Lt -> boolToF $ l1 <  l2
        Le -> boolToF $ l1 <= l2
        Eq -> boolToF $ l1 == l2
      where
        boolToF True  = FTrue
        boolToF False = FFalse


    -- Comp tautologies and eliminations
    -- Eliminate double not
    simplify (FNot (FNot f))                                    = simplify f
    simplify (FComp Eq e1 e2)                                   = if e1 P.== e2 || simplifyE e1 P.== simplifyE e2 then FTrue else FComp Eq (simplifyE e1) (simplifyE e2)
    simplify (FComp op e1 e2)                                   = FComp op (simplifyE e1) (simplifyE e2)
    simplify FTrue                                              = FTrue
    simplify FFalse                                             = FFalse
    simplify (FNot FTrue)                                       = FFalse
    simplify (FNot FFalse)                                      = FTrue
    simplify (FNot f)                                           = FNot (simplify f)
    -- simplifyF FTrue = error "FTrue was not eliminated"
    -- simplifyF FFalse = error "FFalse was not eliminated"

simplifyEDoubleList :: [[E]] -> [[E]]
simplifyEDoubleList = nub . map (nub . map simplifyE)

-- simplify all fs
-- look through, symbolic
-- f fnot, fnot f, etc.
-- nothing else, too complicated


simplifyFDNF :: [[F]] -> [[F]]
simplifyFDNF [] = []
simplifyFDNF (c : cs) =
  case simplifyFConjunction c of
    Nothing -> simplifyFDNF cs
    Just [] -> simplifyFDNF cs
    Just [checkedConjunctionHead] -> [checkedConjunctionHead] : simplifyFDNF cs
    Just checkedConjunction@(checkedConjunctionHead : checkedConjunctionTail) ->
      let
        currentEqualities = findEqualities checkedConjunctionHead checkedConjunctionTail checkedConjunctionTail
      in
        case currentEqualities of
          []     -> checkedConjunction : simplifyFDNF cs
          [_eq1] -> checkedConjunction : simplifyFDNF cs
          (currentEqualitiesHead : currentEqualitiesTail)  ->
            let
              newEqualities = findEqZero currentEqualitiesHead currentEqualitiesTail currentEqualitiesTail
            in
              nub (checkedConjunction ++ newEqualities) : simplifyFDNF cs
  where

    -- look for equalities like x == y and x == -y
    -- x == 0, y == 0
    findEqZero :: (E,E) -> [(E,E)] -> [(E,E)] -> [F]
    findEqZero _ [] [] = []
    findEqZero _ [] (eq : conj) = findEqZero eq conj conj
    findEqZero eq1 (eq2 : eqs) conj =
      case eq1 of
        (EUnOp Negate l1, EUnOp Negate r1) ->
          case eq2 of
            (EUnOp Negate l2, r2)
              | l1 P.== l2 && r1 P.== r2 -> [FComp Ge l1 (Lit 0.0), FComp Ge (Lit 0.0) l1, FComp Ge r1 (Lit 0.0), FComp Ge (Lit 0.0) r1] ++ findEqZero eq1 eqs conj
              | l1 P.== r2 && r1 P.== l2 -> [FComp Ge l1 (Lit 0.0), FComp Ge (Lit 0.0) l1, FComp Ge r1 (Lit 0.0), FComp Ge (Lit 0.0) r1] ++ findEqZero eq1 eqs conj
              | otherwise -> findEqZero eq1 eqs conj
            (l2, EUnOp Negate r2)
              | l1 P.== l2 && r1 P.== r2 -> [FComp Ge l1 (Lit 0.0), FComp Ge (Lit 0.0) l1, FComp Ge r1 (Lit 0.0), FComp Ge (Lit 0.0) r1] ++ findEqZero eq1 eqs conj
              | l1 P.== r2 && r1 P.== l2 -> [FComp Ge l1 (Lit 0.0), FComp Ge (Lit 0.0) l1, FComp Ge r1 (Lit 0.0), FComp Ge (Lit 0.0) r1] ++ findEqZero eq1 eqs conj
              | otherwise -> findEqZero eq1 eqs conj
            _ -> findEqZero eq1 eqs conj
        (EUnOp Negate l1, r1) ->
          case eq2 of
            (EUnOp Negate l2, EUnOp Negate r2)
              | l1 P.== l2 && r1 P.== r2 -> [FComp Ge l1 (Lit 0.0), FComp Ge (Lit 0.0) l1, FComp Ge r1 (Lit 0.0), FComp Ge (Lit 0.0) r1] ++ findEqZero eq1 eqs conj
              | l1 P.== r2 && r1 P.== l2 -> [FComp Ge l1 (Lit 0.0), FComp Ge (Lit 0.0) l1, FComp Ge r1 (Lit 0.0), FComp Ge (Lit 0.0) r1] ++ findEqZero eq1 eqs conj
              | otherwise -> findEqZero eq1 eqs conj
            (l2, r2)
              | l1 P.== l2 && r1 P.== r2 -> [FComp Ge l1 (Lit 0.0), FComp Ge (Lit 0.0) l1, FComp Ge r1 (Lit 0.0), FComp Ge (Lit 0.0) r1] ++ findEqZero eq1 eqs conj
              | l1 P.== r2 && r1 P.== l2 -> [FComp Ge l1 (Lit 0.0), FComp Ge (Lit 0.0) l1, FComp Ge r1 (Lit 0.0), FComp Ge (Lit 0.0) r1] ++ findEqZero eq1 eqs conj
              | otherwise -> findEqZero eq1 eqs conj
        (l1, EUnOp Negate r1) ->
          case eq2 of
            (EUnOp Negate l2, EUnOp Negate r2)
              | l1 P.== l2 && r1 P.== r2 -> [FComp Ge l1 (Lit 0.0), FComp Ge (Lit 0.0) l1, FComp Ge r1 (Lit 0.0), FComp Ge (Lit 0.0) r1] ++ findEqZero eq1 eqs conj
              | l1 P.== r2 && r1 P.== l2 -> [FComp Ge l1 (Lit 0.0), FComp Ge (Lit 0.0) l1, FComp Ge r1 (Lit 0.0), FComp Ge (Lit 0.0) r1] ++ findEqZero eq1 eqs conj
              | otherwise -> findEqZero eq1 eqs conj
            (l2, r2)
              | l1 P.== l2 && r1 P.== r2 -> [FComp Ge l1 (Lit 0.0), FComp Ge (Lit 0.0) l1, FComp Ge r1 (Lit 0.0), FComp Ge (Lit 0.0) r1] ++ findEqZero eq1 eqs conj
              | l1 P.== r2 && r1 P.== l2 -> [FComp Ge l1 (Lit 0.0), FComp Ge (Lit 0.0) l1, FComp Ge r1 (Lit 0.0), FComp Ge (Lit 0.0) r1] ++ findEqZero eq1 eqs conj
              | otherwise -> findEqZero eq1 eqs conj
        (l1, r1) ->
          case eq2 of
            (l2, EUnOp Negate r2)
              | l1 P.== l2 && r1 P.== r2 -> [FComp Ge l1 (Lit 0.0), FComp Ge (Lit 0.0) l1, FComp Ge r1 (Lit 0.0), FComp Ge (Lit 0.0) r1] ++ findEqZero eq1 eqs conj
              | l1 P.== r2 && r1 P.== l2 -> [FComp Ge l1 (Lit 0.0), FComp Ge (Lit 0.0) l1, FComp Ge r1 (Lit 0.0), FComp Ge (Lit 0.0) r1] ++ findEqZero eq1 eqs conj
              | otherwise -> findEqZero eq1 eqs conj
            (EUnOp Negate l2, r2)
              | l1 P.== l2 && r1 P.== r2 -> [FComp Ge l1 (Lit 0.0), FComp Ge (Lit 0.0) l1, FComp Ge r1 (Lit 0.0), FComp Ge (Lit 0.0) r1] ++ findEqZero eq1 eqs conj
              | l1 P.== r2 && r1 P.== l2 -> [FComp Ge l1 (Lit 0.0), FComp Ge (Lit 0.0) l1, FComp Ge r1 (Lit 0.0), FComp Ge (Lit 0.0) r1] ++ findEqZero eq1 eqs conj
              | otherwise -> findEqZero eq1 eqs conj
            _ -> findEqZero eq1 eqs conj


    -- finds equalities in a conjunction (x >= y and y >= x)
    findEqualities :: F -> [F] -> [F] -> [(E, E)]
    findEqualities _ [] [] = []
    findEqualities _ [] (f : conj) = findEqualities f conj conj
    findEqualities f1 (f2 : fs) conj =
      case f1 of
        -- say we have x >=y
        FComp Ge l1 r1 ->
          case f2 of
            -- y >= x is an equality
            FComp Ge l2 r2 ->
              if l1 P.== r2 && r1 P.== l2
                then (l1, r1) : findEqualities f1 fs conj
                else findEqualities f1 fs conj
            _ -> findEqualities f1 fs conj
        _ -> findEqualities f1 fs conj


    simplifyFConjunction :: [F] -> Maybe [F]
    simplifyFConjunction [] = Just []
    simplifyFConjunction (simplifiedConjunctionHead : simplifiedConjunctionTail) =
      let
        -- Returns Nothing if a conjunction contains a contradiction
        removeContradictions :: F -> [F] -> [F] -> Maybe [F]
        removeContradictions f1 [] [] = Just [f1]
        removeContradictions f1 [] (f : conj) = (f1 :) <$> removeContradictions f conj conj
        removeContradictions f1 (f2 : fs) conj =
          -- Can be Ge or Gt
          case f1 of
            -- say this is x >= y
            FComp Ge l1 r1 ->
              case f2 of
                -- possible contradictions
                --  y > x
                FComp Gt l2 r2 ->
                  if l1 P.== r2 && r1 P.== l2 then Nothing else removeContradictions f1 fs conj
                -- possible = 0
                -- y >= x (then x and y = 0)
                -- FComp Ge l2 r2 ->
                --   if l1 P.== r2 && r1 P.== l2 
                --     then ([FComp Ge l1 (Lit 0.0), FComp Ge (Lit 0.0) l1, FComp Ge l2 (Lit 0.0), FComp Ge (Lit 0.0) l2] ++) <$> aux f1 fs conj
                --     else aux f1 fs conj
                _ -> removeContradictions f1 fs conj
            -- say this is x > y
            FComp Gt l1 r1 ->
              case f2 of
                -- possible contradictions
                -- y >  x
                -- y >= x
                FComp Ge l2 r2 ->
                  if l1 P.== r2 && r1 P.== l2 then Nothing else removeContradictions f1 fs conj
                FComp Gt l2 r2 ->
                  if l1 P.== r2 && r1 P.== l2 then Nothing else removeContradictions f1 fs conj
                _ -> removeContradictions f1 fs conj
            _ -> removeContradictions f1 fs conj
      in
        nub <$> removeContradictions simplifiedConjunctionHead simplifiedConjunctionTail simplifiedConjunctionTail

fDNFToFDNFWithoutEq :: [[F]] -> [[F]] -> [[F]]
fDNFToFDNFWithoutEq [] dnf = dnf
fDNFToFDNFWithoutEq (c : cs) dnf =
  case mNewDNF of -- Same length means no FNot (FComp Eq _ _)
    Just newDNF -> fDNFToFDNFWithoutEq newDNF []
    Nothing -> fDNFToFDNFWithoutEq cs (cWithoutEq : dnf)
  where
    cWithoutEq = elimEq False c
    mNewDNF = elimNotEq cWithoutEq

    elimNotEq [] = Nothing
    elimNotEq (f@(FNot (FComp Eq e1 e2)) : _) = Just newDNF
      where
        currentDNF = c : cs ++ dnf
        currentDNFWithoutF = map (delete f) currentDNF
        newF1 = FNot (FComp Ge e1 e2)
        newF2 = FNot (FComp Ge e2 e1)

        newDNF = map (newF1 :) currentDNFWithoutF ++ map (newF2 :) currentDNFWithoutF
        -- cWithoutEqWithoutF = delete f cWithoutEq
        -- currentDNFWithoutC = cs ++ dnf
        -- newC1 = FNot (FComp Ge e1 e2) : cWithoutEqWithoutF
        -- newC2 = FNot (FComp Ge e2 e1) : cWithoutEqWithoutF
        -- newDNF = (newC1 : currentDNFWithoutC) ++ (newC2 : currentDNFWithoutC)
    elimNotEq (_ : fs) = elimNotEq fs

    elimEq _ [] = []
    elimEq isNegated (FNot f : fs) = elimEq (not isNegated) (f : fs)
    elimEq False (FComp Eq e1 e2 : fs) = FComp Ge e1 e2 : FComp Ge e2 e1 : elimEq False fs
    elimEq True (f : fs) = FNot f : elimEq False fs
    elimEq False (f : fs) = f : elimEq False fs

fDNFToEDNF :: [[F]] -> [[ESafe]]
fDNFToEDNF = map fConjToE
-- fDNFToEDNF = map (fConjToE False)
  where
    fConjToE :: [F] -> [ESafe]
    fConjToE [] = []
    fConjToE (FComp Ge e1 e2 : fs) = ENonStrict (EBinOp Sub e1 e2)   : fConjToE fs
    fConjToE (FComp Gt e1 e2 : fs) = EStrict    (EBinOp Sub e1 e2)   : fConjToE fs
    fConjToE (FComp {} : _)        = error "Non-normalized FComp found in DNF"
    fConjToE (FConn {} : _)        = error "Non-atomic F found in DNF"
    fConjToE (FNot f : fs)         = error "Negated f found in DNF"
    fConjToE (FTrue : fs)          = ENonStrict (Lit 1.0)    : fConjToE fs
    fConjToE (FFalse : fs)         = ENonStrict (Lit (-1.0)) : fConjToE fs

    -- fConjToE :: Bool -> [F] -> [ESafe]
    -- fConjToE _ [] = []
    -- fConjToE True  (FComp Eq e1 e2 : fs) = error "Negated FComp with Eq found in DNF" 
    -- fConjToE False (FComp Eq e1 e2 : fs) = fConjToE False $ [FComp Ge e1 e2, FComp Ge e2 e1] ++ fs
    -- fConjToE False (FComp Ge e1 e2 : fs) = ENonStrict (EBinOp Sub e1 e2)   : fConjToE False fs
    -- fConjToE False (FComp Gt e1 e2 : fs) = EStrict    (EBinOp Sub e1 e2)   : fConjToE False fs
    -- fConjToE False (FComp Le e1 e2 : fs) = fConjToE False $ FComp Ge e2 e1 : fs
    -- fConjToE False (FComp Lt e1 e2 : fs) = fConjToE False $ FComp Gt e2 e1 : fs
    -- fConjToE True  (FComp Ge e1 e2 : fs) = fConjToE False $ FComp Lt e1 e2 : fs
    -- fConjToE True  (FComp Gt e1 e2 : fs) = fConjToE False $ FComp Le e1 e2 : fs
    -- fConjToE True  (FComp Le e1 e2 : fs) = fConjToE False $ FComp Gt e1 e2 : fs
    -- fConjToE True  (FComp Lt e1 e2 : fs) = fConjToE False $ FComp Ge e1 e2 : fs
    -- fConjToE _ (FConn {} : _)           = error "non-atomic f found in DNF"
    -- fConjToE isNegated (FNot f : fs)     = fConjToE (not isNegated) (f : fs)
    -- fConjToE False (FTrue : fs)            = ENonStrict (Lit 1.0) : fConjToE False fs
    -- fConjToE False (FFalse : fs)           = ENonStrict (Lit (-1.0)) : fConjToE False fs
    -- fConjToE True (FTrue : fs)             = ENonStrict (Lit (-1.0)) : fConjToE False fs
    -- fConjToE True (FFalse : fs)            = ENonStrict (Lit 1.0) : fConjToE False fs

    compFToE :: Bool -> F -> ESafe
    compFToE _     (FComp Eq _ _)   = error "FComp with Eq found in DNF"
    compFToE False (FComp Ge e1 e2) = ENonStrict $ EBinOp Sub e1 e2
    compFToE False (FComp Gt e1 e2) = EStrict    $ EBinOp Sub e1 e2
    compFToE False (FComp Le e1 e2) = compFToE False (FComp Ge e2 e1)
    compFToE False (FComp Lt e1 e2) = compFToE False (FComp Gt e2 e1)
    compFToE True  (FComp Ge e1 e2) = compFToE False (FComp Lt e2 e1)
    compFToE True  (FComp Gt e1 e2) = compFToE False (FComp Le e2 e1)
    compFToE True  (FComp Le e1 e2) = compFToE False (FComp Gt e2 e1)
    compFToE True  (FComp Lt e1 e2) = compFToE False (FComp Ge e2 e1)
    compFToE _ FConn {}             = error "non-atomic f found in DNF"
    compFToE isNegated (FNot f)     = compFToE (not isNegated) f
    compFToE False FTrue            = ENonStrict $ Lit 1.0
    compFToE False FFalse           = ENonStrict $ Lit $ -1.0
    compFToE True FTrue             = ENonStrict $ Lit $ -1.0
    compFToE True FFalse            = ENonStrict $ Lit 1.0


simplifyFDoubleList :: [[F]] -> [[F]]
simplifyFDoubleList = nub . map (nub . map simplifyF)

simplifyESafeDoubleList :: [[ESafe]] -> [[ESafe]]
simplifyESafeDoubleList = nub . map (nub . map (fmapESafe simplifyE))

-- | compute the value of E with Vars at specified points
computeE :: E -> [(String, Rational)] -> CN Double
computeE (EBinOp op e1 e2) varMap =
  case op of
    Min -> computeE e1 varMap `min` computeE e2 varMap
    Max -> computeE e1 varMap `max` computeE e2 varMap
    Add -> computeE e1 varMap + computeE e2 varMap
    Sub -> computeE e1 varMap - computeE e2 varMap
    Mul -> computeE e1 varMap * computeE e2 varMap
    Div -> computeE e1 varMap / computeE e2 varMap
    Pow -> computeE e1 varMap ^ computeE e2 varMap
computeE (EUnOp op e) varMap =
  case op of
    Abs -> abs (computeE e varMap)
    Sqrt -> sqrt (computeE e varMap)
    Negate -> negate (computeE e varMap)
    Sin -> sin (computeE e varMap)
    Cos -> cos (computeE e varMap)
computeE (Var v) varMap =
  case Map.lookup v (Map.fromList varMap) of
    Nothing -> error ("map does not contain variable " ++ show v)
    Just r -> cn (double r)
computeE (Lit i) _ = cn (double i)
computeE (PowI e i) varMap = computeE e varMap  ^ i
computeE (Float _ _) _   = error "computeE for Floats not supported"
computeE (Float32 _ _) _ = error "computeE for Floats not supported"
computeE (Float64 _ _) _ = error "computeE for Floats not supported"

-- | Given a list of qualified Es and points for all Vars,
-- compute a list of valid values. 
-- 
-- A value is the computed result of the second element of 
-- the tuple and is valid if all the expressions in the list 
-- at the first element of the tuple compute to be above 0.
computeQualifiedEs :: [([E], E)] -> [(String, Rational)] -> [CN Double]
computeQualifiedEs [] _ = []
computeQualifiedEs ((ps, q) : es) varMap =
  if all (\p -> computeE p varMap !>=! 0) ps
    then computeE q varMap : computeQualifiedEs es varMap
    else computeQualifiedEs es varMap

computeEDisjunction :: [E] -> [(String, Rational)] -> [CN Double]
computeEDisjunction es varMap = map (`computeE` varMap) es

computeECNF :: [[E]] -> [(String, Rational)] -> [[CN Double]]
computeECNF cnf varMap = map (`computeEDisjunction` varMap) cnf

prettyShowESafeCNF :: [[ESafe]] -> String
prettyShowESafeCNF cnf = "AND" ++ concatMap (\d -> "\n\t" ++ prettyShowDisjunction d) cnf
  where
    -- |Show a disjunction of expressions > 0 in a human-readable format
    -- This is shown as an OR with each term tabbed in
    -- If there is only one term, the expression is shown without an OR 
    prettyShowDisjunction :: [ESafe] -> String
    prettyShowDisjunction []  = []
    prettyShowDisjunction [e'] =
      case e' of
        EStrict e -> prettyShowE e ++ " > 0"
        ENonStrict e -> prettyShowE e ++ " >= 0"
    prettyShowDisjunction es  =
      "OR" ++
      concatMap
      (\case
        EStrict e -> "\n\t\t" ++ prettyShowE e ++ " > 0"
        ENonStrict e -> "\n\t\t" ++ prettyShowE e ++ " >= 0")
      es

prettyShowESafeDNF :: [[ESafe]] -> String
prettyShowESafeDNF cnf = "OR" ++ concatMap (\d -> "\n\t" ++ prettyShowDisjunction d) cnf
  where
    -- |Show a disjunction of expressions > 0 in a human-readable format
    -- This is shown as an OR with each term tabbed in
    -- If there is only one term, the expression is shown without an OR 
    prettyShowDisjunction :: [ESafe] -> String
    prettyShowDisjunction []  = []
    prettyShowDisjunction [e'] =
      case e' of
        EStrict e -> prettyShowE e ++ " > 0"
        ENonStrict e -> prettyShowE e ++ " >= 0"
    prettyShowDisjunction es  =
      "AND" ++
      concatMap
      (\case
        EStrict e -> "\n\t\t" ++ prettyShowE e ++ " > 0"
        ENonStrict e -> "\n\t\t" ++ prettyShowE e ++ " >= 0")
      es

prettyShowFSafeDNF :: [[F]] -> String
prettyShowFSafeDNF dnf = "OR" ++ concatMap (\c -> "\n\t" ++ prettyShowConjunction c) dnf
  where
    -- |Show a disjunction of expressions > 0 in a human-readable format
    -- This is shown as an OR with each term tabbed in
    -- If there is only one term, the expression is shown without an OR 
    prettyShowConjunction :: [F] -> String
    prettyShowConjunction []  = []
    prettyShowConjunction [f] = prettyShowF f 2
    prettyShowConjunction fs  =
      "AND" ++
      concatMap
      (\f -> "\n\t\t" ++ prettyShowF f 3)
      fs

-- prettyShowF :: F -> Integer -> String
-- prettyShowF (FComp op e1 e2) numTabs = "\n" ++ concat (replicate numTabs "\t") ++ prettyShowE e1 ++ " " ++ prettyShowComp op ++ " " ++ prettyShowE e2
-- prettyShowF (FConn op f1 f2) numTabs = "\n" ++ concat (replicate numTabs "\t") ++ prettyShowConn op ++ prettyShowF f1 (numTabs + 1) ++ prettyShowF f2 (numTabs + 1)
-- prettyShowF (FNot f)         numTabs = "\n" ++ concat (replicate numTabs "\t") ++ "NOT" ++ prettyShowF f (numTabs + 1)
-- prettyShowF FTrue            numTabs = "\n" ++ concat (replicate numTabs "\t") ++ "True"
-- prettyShowF FFalse           numTabs = "\n" ++ concat (replicate numTabs "\t") ++ "False"

-- pretty show a Why3 VC which is typically a bunch of conjunctions
prettyShowVC :: F -> TypedVarMap -> String
prettyShowVC vc vm =
  "Bounds on variables: \n" ++
  prettyShowRanges vm ++ "\n" ++
  "exact NVC: \n" ++
  prettyShowConjunction (conjunctionToList vc)
  where
    prettyShowRanges :: TypedVarMap -> String
    prettyShowRanges [] = ""
    prettyShowRanges ((TypedVar (vName, (vLower, vUpper)) vType) : vm) =
      vName ++ " (" ++ show vType ++ ")" ++ " in [" ++ showRational vLower ++ ", " ++ showRational vUpper ++ "]" ++ "\n" ++ prettyShowRanges vm

    showRational r =
      let
        numer = numerator r
        denom = denominator r
      in
        if denom == 1
          then show numer
          else show numer ++ " / " ++ show denom

    conjunctionToList :: F -> [F]
    conjunctionToList (FConn And f1 f2) = conjunctionToList f1 ++ conjunctionToList f2
    conjunctionToList f = [f]

    prettyShowConjunction :: [F] -> String
    prettyShowConjunction []  = []
    prettyShowConjunction [f] = prettyShowF f 2
    prettyShowConjunction fs  =
      concatMap
      (\f -> prettyShowAssert f 0 ++ "\n\n")
      fs

    prettyShowAssert :: F -> Integer -> String
    prettyShowAssert (FComp op e1 e2) indentTracker = concat (replicate indentTracker "  ") ++ prettyShowE e1 ++ " " ++ prettyShowComp op ++ " " ++ prettyShowE e2
    prettyShowAssert (FConn Impl f1 f2) indentTracker = concat (replicate indentTracker "  ") ++ prettyShowConn Impl ++ "\n" ++ prettyShowAssert f1 (indentTracker + 1) ++ "\n" ++ concat (replicate (indentTracker + 1) "  ") ++ "===========>\n" ++ prettyShowAssert f2 (indentTracker + 1)
    prettyShowAssert (FConn op f1 f2) indentTracker = concat (replicate indentTracker "  ") ++ prettyShowConn op ++ "\n" ++ prettyShowAssert f1 (indentTracker + 1) ++ "\n" ++ prettyShowAssert f2 (indentTracker + 1)
    prettyShowAssert (FNot f)         indentTracker = concat (replicate indentTracker "  ") ++ "NOT" ++ "\n" ++ prettyShowAssert f (indentTracker + 1)
    prettyShowAssert FTrue            indentTracker = concat (replicate indentTracker "  ") ++ "True"
    prettyShowAssert FFalse           indentTracker = concat (replicate indentTracker "  ") ++ "False"

-- latexShowESafeCNF :: [[ESafe]] -> String
-- latexShowESafeCNF cnf = "AND" ++ concatMap (\d -> "\n\t" ++ prettyShowDisjunction d) cnf
--   where
--     -- |Show a disjunction of expressions > 0 in a human-readable format
--     -- This is shown as an OR with each term tabbed in
--     -- If there is only one term, the expression is shown without an OR 
--     prettyShowDisjunction :: [ESafe] -> String
--     prettyShowDisjunction []  = []
--     prettyShowDisjunction [e'] = 
--       case e' of
--         EStrict e -> prettyShowE e ++ " > 0"
--         ENonStrict e -> prettyShowE e ++ " >= 0"
--     prettyShowDisjunction es  =
--       "OR" ++ 
--       concatMap 
--       (\case
--         EStrict e -> "\n\t\t" ++ prettyShowE e ++ " > 0" 
--         ENonStrict e -> "\n\t\t" ++ prettyShowE e ++ " >= 0")
--       es

latexShowE :: E -> String
latexShowE (EBinOp op e1 e2) =
  case op of
    Add -> "$(" ++ latexShowE e1 ++ " + " ++ latexShowE e2 ++ ")$"
    Sub -> "$(" ++ latexShowE e1 ++ " - " ++ latexShowE e2 ++ ")$"
    Div -> "$(" ++ latexShowE e1 ++ " \\div " ++ latexShowE e2 ++ ")$"
    Mul -> "$(" ++ latexShowE e1 ++ " \\times " ++ latexShowE e2 ++ ")$"
    Pow -> "$(" ++ latexShowE e1 ++ "_{" ++ latexShowE e2 ++ ")}$"
    Min -> "$(min " ++ latexShowE e1 ++ " " ++ latexShowE e2 ++ ")$"
    Max -> "$(max " ++ latexShowE e1 ++ " " ++ latexShowE e2 ++ ")$"
    Mod -> "$(mod " ++ latexShowE e1 ++ " " ++ latexShowE e2 ++ ")$"
latexShowE (EUnOp op e) =
  case op of
    Abs    -> "$|" ++ latexShowE e ++ "|$"
    Sqrt   -> "$\\sqrt{" ++ latexShowE e ++ ")}"
    Negate -> "$(-1 \\times " ++ latexShowE e ++ ")$"
    Sin    -> "$(sin " ++ latexShowE e ++ ")$"
    Cos    -> "$(cos " ++ latexShowE e ++ ")$"
latexShowE (PowI e i) = "(" ++ latexShowE e ++ " ^ " ++ show i ++ ")"
latexShowE (Var v) = v
latexShowE (Lit v) = show (double v)
latexShowE (Float32 m e) =
  case m of
    RNE -> "(rnd32_ne " ++ latexShowE e ++ ")"
    RTP -> "(rnd32_tp " ++ latexShowE e ++ ")"
    RTN -> "(rnd32_tn " ++ latexShowE e ++ ")"
    RTZ -> "(rnd32_tz " ++ latexShowE e ++ ")"
    RNA -> "(rnd32_na " ++ latexShowE e ++ ")"
latexShowE (Float64 m e) =
  case m of
    RNE -> "(rnd64_ne " ++ latexShowE e ++ ")"
    RTP -> "(rnd64_tp " ++ latexShowE e ++ ")"
    RTN -> "(rnd64_tn " ++ latexShowE e ++ ")"
    RTZ -> "(rnd64_tz " ++ latexShowE e ++ ")"
    RNA -> "(rnd64_na " ++ latexShowE e ++ ")"
latexShowE (Float m e) =
  case m of
    RNE -> "(rnd_ne " ++ latexShowE e ++ ")"
    RTP -> "(rnd_tp " ++ latexShowE e ++ ")"
    RTN -> "(rnd_tn " ++ latexShowE e ++ ")"
    RTZ -> "(rnd_tz " ++ latexShowE e ++ ")"
    RNA -> "(rnd_na " ++ latexShowE e ++ ")"
latexShowE Pi = "$\\pi$"
latexShowE (RoundToInteger m e) =
  case m of
    RNE -> "(rndToInt_ne " ++ latexShowE e ++ ")"
    RTP -> "(rndToInt_tp " ++ latexShowE e ++ ")"
    RTN -> "(rndToInt_tn " ++ latexShowE e ++ ")"
    RTZ -> "(rndToInt_tz " ++ latexShowE e ++ ")"
    RNA -> "(rndToInt_ta " ++ latexShowE e ++ ")"

latexShowF :: F -> Integer -> String
latexShowF (FComp op e1 e2) numTabs = "\n" ++ concat (replicate numTabs "\t") ++ latexShowE e1 ++ " " ++ latexShowComp op ++ " " ++ latexShowE e2
latexShowF (FConn op f1 f2) numTabs = "\n" ++ concat (replicate numTabs "\t") ++ latexShowF f1 numTabs ++ " " ++ latexShowConn op ++ latexShowF f2 (numTabs + 1)
latexShowF (FNot f)         numTabs = "\n" ++ concat (replicate numTabs "\t") ++ "$\\lnot$" ++ latexShowF f (numTabs + 1)
latexShowF FTrue            numTabs = "\n" ++ concat (replicate numTabs "\t") ++ "$\\top$"
latexShowF FFalse           numTabs = "\n" ++ concat (replicate numTabs "\t") ++ "$\\bot$"

latexShowComp :: Comp -> String
latexShowComp Gt = "$>$"
latexShowComp Ge = "$\\ge$"
latexShowComp Lt = "$<$"
latexShowComp Le = "$\\le$"
latexShowComp Eq = "$=$"

latexShowConn :: Conn -> String
latexShowConn And   = "$\\wedge$"
latexShowConn Or    = "$\\vee$"
latexShowConn Impl  = "$\\implies$"

-- |Show an expression in a human-readable format
-- Rationals are converted into doubles
prettyShowE :: E -> String
prettyShowE (EBinOp op e1 e2) =
  case op of
    Add -> "(" ++ prettyShowE e1 ++ " + " ++ prettyShowE e2 ++ ")"
    Sub -> "(" ++ prettyShowE e1 ++ " - " ++ prettyShowE e2 ++ ")"
    Div -> "(" ++ prettyShowE e1 ++ " / " ++ prettyShowE e2 ++ ")"
    Mul -> "(" ++ prettyShowE e1 ++ " * " ++ prettyShowE e2 ++ ")"
    Pow -> "(" ++ prettyShowE e1 ++ " ^ " ++ prettyShowE e2 ++ ")"
    Min -> "(min " ++ prettyShowE e1 ++ " " ++ prettyShowE e2 ++ ")"
    Max -> "(max " ++ prettyShowE e1 ++ " " ++ prettyShowE e2 ++ ")"
    Mod -> "(mod " ++ prettyShowE e1 ++ " " ++ prettyShowE e2 ++ ")"
prettyShowE (EUnOp op e) =
  case op of
    Abs    -> "|" ++ prettyShowE e ++ "|"
    Sqrt   -> "(sqrt " ++ prettyShowE e ++ ")"
    Negate -> "(-1 * " ++ prettyShowE e ++ ")"
    Sin    -> "(sin " ++ prettyShowE e ++ ")"
    Cos    -> "(cos " ++ prettyShowE e ++ ")"
prettyShowE (PowI e i) = "(" ++ prettyShowE e ++ " ^ " ++ show i ++ ")"
prettyShowE (Var v) = v
prettyShowE (Lit v) =
  if denom == 1
    then show numer
    else show numer ++ " / " ++ show denom
  where
    numer = numerator v
    denom = denominator v
prettyShowE (Float32 m e) =
  case m of
    RNE -> "(rnd32_ne " ++ prettyShowE e ++ ")"
    RTP -> "(rnd32_tp " ++ prettyShowE e ++ ")"
    RTN -> "(rnd32_tn " ++ prettyShowE e ++ ")"
    RTZ -> "(rnd32_tz " ++ prettyShowE e ++ ")"
    RNA -> "(rnd32_na " ++ prettyShowE e ++ ")"
prettyShowE (Float64 m e) =
  case m of
    RNE -> "(rnd64_ne " ++ prettyShowE e ++ ")"
    RTP -> "(rnd64_tp " ++ prettyShowE e ++ ")"
    RTN -> "(rnd64_tn " ++ prettyShowE e ++ ")"
    RTZ -> "(rnd64_tz " ++ prettyShowE e ++ ")"
    RNA -> "(rnd64_na " ++ prettyShowE e ++ ")"
prettyShowE (Float m e) =
  case m of
    RNE -> "(rnd_ne " ++ prettyShowE e ++ ")"
    RTP -> "(rnd_tp " ++ prettyShowE e ++ ")"
    RTN -> "(rnd_tn " ++ prettyShowE e ++ ")"
    RTZ -> "(rnd_tz " ++ prettyShowE e ++ ")"
    RNA -> "(rnd_na " ++ prettyShowE e ++ ")"
prettyShowE Pi = "Pi"
prettyShowE (RoundToInteger m e) =
  case m of
    RNE -> "(rndToInt_ne " ++ prettyShowE e ++ ")"
    RTP -> "(rndToInt_tp " ++ prettyShowE e ++ ")"
    RTN -> "(rndToInt_tn " ++ prettyShowE e ++ ")"
    RTZ -> "(rndToInt_tz " ++ prettyShowE e ++ ")"
    RNA -> "(rndToInt_ta " ++ prettyShowE e ++ ")"

-- |Show a conjunction of expressions in a human-readable format
-- This is shown as an AND with each disjunction tabbed in with an OR
-- If there is only one term in a disjunction, the expression is shown without an OR 
prettyShowECNF :: [[E]] -> String
prettyShowECNF cnf =
  "AND" ++ concatMap (\d -> "\n\t" ++ prettyShowDisjunction d) cnf
  where
    -- |Show a disjunction of expressions > 0 in a human-readable format
    -- This is shown as an OR with each term tabbed in
    -- If there is only one term, the expression is shown without an OR 
    prettyShowDisjunction :: [E] -> String
    prettyShowDisjunction []  = []
    prettyShowDisjunction [e] = prettyShowE e
    prettyShowDisjunction es  =
      "OR" ++ concatMap (\e -> "\n\t\t" ++ prettyShowE e ++ " > 0") es

prettyShowF :: F -> Integer -> String
prettyShowF (FComp op e1 e2) numTabs = "\n" ++ concat (replicate numTabs "\t") ++ prettyShowE e1 ++ " " ++ prettyShowComp op ++ " " ++ prettyShowE e2
prettyShowF (FConn op f1 f2) numTabs = "\n" ++ concat (replicate numTabs "\t") ++ prettyShowConn op ++ prettyShowF f1 (numTabs + 1) ++ prettyShowF f2 (numTabs + 1)
prettyShowF (FNot f)         numTabs = "\n" ++ concat (replicate numTabs "\t") ++ "NOT" ++ prettyShowF f (numTabs + 1)
prettyShowF FTrue            numTabs = "\n" ++ concat (replicate numTabs "\t") ++ "True"
prettyShowF FFalse           numTabs = "\n" ++ concat (replicate numTabs "\t") ++ "False"

prettyShowComp :: Comp -> String
prettyShowComp Gt = ">"
prettyShowComp Ge = ">="
prettyShowComp Lt = "<"
prettyShowComp Le = "<="
prettyShowComp Eq = "=="

prettyShowConn :: Conn -> String
prettyShowConn And   = "AND"
prettyShowConn Or    = "OR"
prettyShowConn Impl  = "IMPL"

-- |Extract all variables in an expression
-- Will not return duplicationes
extractVariablesE :: E -> [String]
extractVariablesE = nub . findAllVars
  where
    findAllVars (Lit _)          = []
    findAllVars Pi               = []
    findAllVars (Var v)          = [v]
    findAllVars (EUnOp _ e)      = findAllVars e
    findAllVars (EBinOp _ e1 e2) = findAllVars e1 ++ findAllVars e2
    findAllVars (PowI e _)       = findAllVars e
    findAllVars (Float32 _ e)    = findAllVars e
    findAllVars (Float64 _ e)    = findAllVars e
    findAllVars (Float _ e)      = findAllVars e
    findAllVars (RoundToInteger _ e) = findAllVars e

-- |Extract all variables in an expression
-- Will not return duplicationes
extractVariablesF :: F -> [String]
extractVariablesF = nub . findAllVars
  where
    findAllVars (FComp _ e1 e2) = extractVariablesE e1 ++ extractVariablesE e2
    findAllVars (FConn _ f1 f2) = findAllVars f1 ++ findAllVars f2
    findAllVars (FNot f)        = findAllVars f
    findAllVars FTrue           = []
    findAllVars FFalse          = []

extractVariablesECNF :: [[E]] -> [String]
extractVariablesECNF = nub . concatMap (concatMap extractVariablesE)

hasVarsE :: E -> Bool
hasVarsE (Float _ _)      = False
hasVarsE (Float32 _ _)    = False
hasVarsE (Float64 _ _)    = False
hasVarsE (EBinOp _ e1 e2) = hasFloatE e1 || hasFloatE e2
hasVarsE (EUnOp _ e)      = hasFloatE e
hasVarsE (PowI e _)       = hasFloatE e
hasVarsE (Lit _)          = False
hasVarsE (Var _)          = True
hasVarsE Pi               = False
hasVarsE (RoundToInteger _ e) = hasFloatE e

hasVarsF :: F -> Bool
hasVarsF (FConn _ f1 f2) = hasVarsF f1 || hasVarsF f2
hasVarsF (FComp _ e1 e2) = hasVarsE e1 || hasVarsE e2
hasVarsF (FNot f)        = hasVarsF f
hasVarsF FTrue           = False
hasVarsF FFalse          = False

hasFloatE :: E -> Bool
hasFloatE (Float _ _)      = True
hasFloatE (Float32 _ _)    = True
hasFloatE (Float64 _ _)    = True
hasFloatE (EBinOp _ e1 e2) = hasFloatE e1 || hasFloatE e2
hasFloatE (EUnOp _ e)      = hasFloatE e
hasFloatE (PowI e _)       = hasFloatE e
hasFloatE (Lit _)          = False
hasFloatE (Var _)          = False
hasFloatE Pi               = False
hasFloatE (RoundToInteger _ e) = hasFloatE e

hasFloatF :: F -> Bool
hasFloatF (FConn _ f1 f2) = hasFloatF f1 || hasFloatF f2
hasFloatF (FComp _ e1 e2) = hasFloatE e1 || hasFloatE e2
hasFloatF (FNot f)        = hasFloatF f
hasFloatF FTrue           = False
hasFloatF FFalse          = False

substVarEWithLit :: E -> String -> Rational -> E
substVarEWithLit (Var x) varToSubst valToSubst = if x == varToSubst then Lit valToSubst else Var x
substVarEWithLit (RoundToInteger m e) var val = RoundToInteger m (substVarEWithLit e var val)
substVarEWithLit Pi _ _ = Pi
substVarEWithLit l@(Lit _) _ _ = l
substVarEWithLit (EBinOp op e1 e2) var val = EBinOp op (substVarEWithLit e1 var val) (substVarEWithLit e2 var val)
substVarEWithLit (EUnOp op e) var val = EUnOp op (substVarEWithLit e var val)
substVarEWithLit (PowI e i) var val = PowI (substVarEWithLit e var val) i
substVarEWithLit (Float m e) var val = Float m (substVarEWithLit e var val)
substVarEWithLit (Float32 m e) var val = Float32 m (substVarEWithLit e var val)
substVarEWithLit (Float64 m e) var val = Float64 m (substVarEWithLit e var val)

substVarFWithLit :: F -> String -> Rational -> F
substVarFWithLit (FConn op f1 f2) var val = FConn op (substVarFWithLit f1 var val) (substVarFWithLit f2 var val)
substVarFWithLit (FComp op e1 e2) var val = FComp op (substVarEWithLit e1 var val) (substVarEWithLit e2 var val)
substVarFWithLit (FNot f)         var val = FNot (substVarFWithLit f var val)
substVarFWithLit FTrue  _ _ = FTrue
substVarFWithLit FFalse _ _ = FFalse

substVarEWithE :: String -> E -> E -> E
substVarEWithE varToSubst (EBinOp op e1 e2)       eToSubst  = EBinOp op (substVarEWithE varToSubst e1 eToSubst) (substVarEWithE varToSubst e2 eToSubst)
substVarEWithE varToSubst (EUnOp op e)            eToSubst  = EUnOp op (substVarEWithE varToSubst e eToSubst)
substVarEWithE varToSubst (Float mode e)          eToSubst  = Float mode $ substVarEWithE varToSubst e eToSubst
substVarEWithE varToSubst (Float32 mode e)        eToSubst  = Float32 mode $ substVarEWithE varToSubst e eToSubst
substVarEWithE varToSubst (Float64 mode e)        eToSubst  = Float64 mode $ substVarEWithE varToSubst e eToSubst
substVarEWithE varToSubst (RoundToInteger mode e) eToSubst  = RoundToInteger mode $ substVarEWithE varToSubst e eToSubst
substVarEWithE varToSubst (PowI e i)              eToSubst  = PowI (substVarEWithE varToSubst e eToSubst) i
substVarEWithE _           Pi                     eToSubst  = Pi
substVarEWithE _           e@(Lit _)              eToSubst  = e
substVarEWithE varToSubst (Var y)                 eToSubst  = if varToSubst == y then eToSubst else Var y

substVarFWithE :: String -> F -> E -> F
substVarFWithE varToSubst (FConn op f1 f2) eToSubst = FConn op (substVarFWithE varToSubst f1 eToSubst) (substVarFWithE varToSubst f2 eToSubst)
substVarFWithE varToSubst (FComp op e1 e2) eToSubst = FComp op (substVarEWithE varToSubst e1 eToSubst) (substVarEWithE varToSubst e2 eToSubst)
substVarFWithE varToSubst (FNot f)         eToSubst = FNot $ substVarFWithE varToSubst f eToSubst
substVarFWithE _ FTrue                     _        = FTrue
substVarFWithE _ FFalse                    _        = FFalse

-- Replaces implications with ORs, i.e. p -> q becomes !p \/ q
transformImplications :: F -> F
transformImplications (FConn Impl f1 f2) = FConn Or (transformImplications (FNot f1)) (transformImplications f2)
transformImplications (FConn op f1 f2) = FConn op (transformImplications f1) (transformImplications f2)
transformImplications f@(FComp op e1 e2) = f
transformImplications (FNot f) = FNot $ transformImplications f
transformImplications FTrue = FTrue
transformImplications FFalse = FFalse

removeVariableFreeComparisons :: F -> F
removeVariableFreeComparisons f =
  aux f False
  where
    expressionContainsVars :: E -> Bool
    expressionContainsVars (EBinOp _ e1 e2)     = expressionContainsVars e1 || expressionContainsVars e2
    expressionContainsVars (EUnOp _ e)          = expressionContainsVars e
    expressionContainsVars (PowI e _)           = expressionContainsVars e
    expressionContainsVars (Float _ e)          = expressionContainsVars e
    expressionContainsVars (Float32 _ e)        = expressionContainsVars e
    expressionContainsVars (Float64 _ e)        = expressionContainsVars e
    expressionContainsVars (RoundToInteger _ e) = expressionContainsVars e
    expressionContainsVars (Lit _)              = False
    expressionContainsVars Pi                   = False
    expressionContainsVars (Var _)              = True


    -- When we say False (unsat), the VC MUST be False
    -- When we say True (sat), the VC might not be True
    -- We safely remove variableFreeComparisons by adhering to the above statements
    aux f'@(FConn And f1 f2)  isNegated = FConn And  (aux f1 isNegated)       (aux f2 isNegated)
    aux f'@(FConn Or f1 f2)   isNegated = FConn Or   (aux f1 isNegated)       (aux f2 isNegated)
    aux f'@(FConn Impl f1 f2) isNegated = FConn Impl (aux f1 (not isNegated)) (aux f2 isNegated)
    aux f'@(FComp _ e1 e2)    isNegated =
      case (expressionContainsVars e1, expressionContainsVars e2) of
        (True, _) -> f'
        (_, True) -> f'
        _         -> if isNegated then FFalse else FTrue
    aux (FNot f') isNegated = FNot (aux f' (not isNegated))
    aux FTrue  _ = FTrue
    aux FFalse _ = FFalse

hasMinMaxAbsE :: E -> Bool
hasMinMaxAbsE (EBinOp Max _ _)     = True
hasMinMaxAbsE (EBinOp Min _ _)     = True
hasMinMaxAbsE (EBinOp _ e1 e2)     = hasMinMaxAbsE e1 || hasMinMaxAbsE e2
hasMinMaxAbsE (EUnOp Abs e)        = True
hasMinMaxAbsE (EUnOp _ e)          = hasMinMaxAbsE e
hasMinMaxAbsE (PowI e _)           = hasMinMaxAbsE e
hasMinMaxAbsE (Float32 _ e)        = hasMinMaxAbsE e
hasMinMaxAbsE (Float64 _ e)        = hasMinMaxAbsE e
hasMinMaxAbsE (Float _ e)          = hasMinMaxAbsE e
hasMinMaxAbsE (RoundToInteger _ e) = hasMinMaxAbsE e
hasMinMaxAbsE (Lit _)              = False
hasMinMaxAbsE (Var _)              = False
hasMinMaxAbsE (Pi)                 = False

hasMinMaxAbsF :: F -> Bool
hasMinMaxAbsF (FComp _ e1 e2) = hasMinMaxAbsE e1 || hasMinMaxAbsE e2
hasMinMaxAbsF (FConn _ f1 f2) = hasMinMaxAbsF f1 || hasMinMaxAbsF f2
hasMinMaxAbsF (FNot f)        = hasMinMaxAbsF f
hasMinMaxAbsF FTrue           = False
hasMinMaxAbsF FFalse          = False

replaceEInE :: E -> E -> E -> E
replaceEInE eContainingE eToFind eToReplace =
  if eContainingE P.== eToFind
    then eToReplace
    else
      case eContainingE of
        EBinOp op e1 e2      -> EBinOp  op  (replaceEInE e1 eToFind eToReplace) (replaceEInE e2 eToFind eToReplace)
        EUnOp op e           -> EUnOp   op  (replaceEInE e eToFind eToReplace)
        Float32 rnd e        -> Float32 rnd (replaceEInE e eToFind eToReplace)
        Float64 rnd e        -> Float64 rnd (replaceEInE e eToFind eToReplace)
        Float rnd e          -> Float64 rnd (replaceEInE e eToFind eToReplace)
        RoundToInteger rnd e -> RoundToInteger rnd (replaceEInE e eToFind eToReplace)
        PowI e i             -> PowI (replaceEInE e eToFind eToReplace) i
        Lit _                -> eContainingE
        Var _                -> eContainingE
        Pi                   -> eContainingE


replaceEInF :: F -> E -> E -> F
replaceEInF fContainingE eToFind eToReplace =
  case fContainingE of
    FConn op f1 f2 -> FConn op (replaceEInF f1 eToFind eToReplace) (replaceEInF f2 eToFind eToReplace)
    FComp op e1 e2 -> FComp op (replaceEInE e1 eToFind eToReplace) (replaceEInE e2 eToFind eToReplace)
    FNot f         -> FNot $ replaceEInF f eToFind eToReplace
    FTrue          -> FTrue
    FFalse         -> FFalse

-- |Normalize to and/or
-- aggressively apply elimination rules
normalizeBoolean :: F -> F
normalizeBoolean form =
  if form P.== simplifiedForm
    then simplifiedForm
    else normalizeBoolean simplifiedForm
  where
    simplifiedForm = aggressiveSimplify $ simplifyF $ normalizeToOr $ aux $ simplifyF form

    -- Turn and/or into or using demorgans laws
    normalizeToOr f =
      let
        -- convertAndToNegatedOr (FConn And (FNot x) y) = FNot $ FConn Or x $ convertAndToNegatedOr y
        convertAndToOr (FConn And x y) = FNot $ FConn Or (FNot x) $ convertAndToOr (FNot y)
        convertAndToOr (FConn Or x y) = FConn Or (convertAndToOr x) (convertAndToOr y)
        -- convertAndToNegatedOr (FNot y) = y
        convertAndToOr y = y
      in
        convertAndToOr f

    -- Aggressively simplify Ors
    aggressiveSimplify (FConn Or x f@(FNot (FConn Or y z)))
      | x P.== y  = aggressiveSimplify (FConn Or x (FNot z))
      | x P.== z  = aggressiveSimplify (FConn Or x (FNot y))
      | otherwise = FConn Or (aggressiveSimplify x) (aggressiveSimplify f)
    aggressiveSimplify (FConn Or f@(FNot (FConn Or y z)) x)
      | x P.== y  = aggressiveSimplify (FConn Or (FNot z) x)
      | x P.== z  = aggressiveSimplify (FConn Or (FNot y) x)
      | otherwise = FConn Or (aggressiveSimplify f) (aggressiveSimplify x)
    aggressiveSimplify (FNot (FNot f)) = aggressiveSimplify f
    -- aggressiveSimplify (FConn Or x f@(FConn And (FNot x') y)) = if x P.== x' then aggressiveSimplify (FConn Or x y) else (FConn Or (aggressiveSimplify x) (aggressiveSimplify f))
    -- aggressiveSimplify (FConn Or x f@(FConn And y (FNot x'))) = if x P.== x' then aggressiveSimplify (FConn Or x y) else (FConn Or (aggressiveSimplify x) (aggressiveSimplify f))
    -- aggressiveSimplify (FConn Or f@(FConn And (FNot x') y) x) = if x P.== x' then aggressiveSimplify (FConn Or x y) else (FConn Or (aggressiveSimplify f) (aggressiveSimplify x))
    -- aggressiveSimplify (FConn Or f@(FConn And y (FNot x')) x) = if x P.== x' then aggressiveSimplify (FConn Or x y) else (FConn Or (aggressiveSimplify f) (aggressiveSimplify x))
    aggressiveSimplify f = f

    -- Eliminate implications and distribute FNots
    -- aux (FConn Or x f@(FConn And (FNot x') y)) = if x P.== x' then FConn And x y else FConn Or (aux x) (aux f)
    aux (FConn Impl x y) = aux $ FConn Or (FNot x) y
    aux (FNot f@(FConn Impl x y)) = aux (FNot (aux f))
    aux (FNot (FConn Or x y)) = aux (FConn And (FNot x) (FNot y))
    aux (FNot (FConn And x y)) = aux (FConn Or (FNot x) (FNot y))
    aux (FConn Or x y) = FConn Or (aux x) (aux y)
    aux (FConn And x y) = FConn And (aux x) (aux y)
    aux (FNot (FNot f)) = aux f
    aux f = f
