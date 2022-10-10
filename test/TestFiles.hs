module TestFiles where

import Prelude
import PropaFP.Expression
import PropaFP.VarMap
import PropaFP.Translators.DReal (formulaAndVarMapToDReal)
import PropaFP.Translators.MetiTarski (formulaAndVarMapToMetiTarski)

-- |Files which PropaFP can process within a few seconds
quickTestFiles :: [(String, String)]
quickTestFiles =
  [
    ("heron", "heron_init"),
    ("heron", "heron_pres"),
    ("hie_sine", "approx_cos_ge"),
    ("hie_sine", "approx_cos_ge_b1"),
    ("hie_sine", "approx_cos_ge_b2"),
    ("hie_sine", "approx_cos_ge_b3"),
    ("hie_sine", "approx_cos_le"),
    ("hie_sine", "approx_cos_le_b1"),
    ("hie_sine", "approx_cos_le_b2"),
    ("hie_sine", "approx_cos_le_b3"),
    ("hie_sine", "approx_sin_ge"),
    ("hie_sine", "approx_sin_ge_b1"),
    ("hie_sine", "approx_sin_ge_b2"),
    ("hie_sine", "approx_sin_ge_b3"),
    ("hie_sine", "approx_sin_le"),
    ("hie_sine", "approx_sin_le_b1"),
    ("hie_sine", "approx_sin_le_b2"),
    ("hie_sine", "approx_sin_le_b3"),
    ("hie_sine", "my_machine_rounding_ge"),
    ("hie_sine", "my_machine_rounding_le"),
    ("hie_sine", "reduce_half_pi_x_ge"),
    ("hie_sine", "reduce_half_pi_x_le"),
    ("hie_sine", "sin_ge"),
    ("hie_sine", "sin_le"),
    ("taylor_sine", "taylor_sin_double"),
    ("taylor_sine", "taylor_sin_p"),
    ("taylor_sine", "taylor_sin_plus"),
    ("taylor_sine", "taylor_sin_swap"),
    ("taylor_sine", "taylor_sin_tight"),
    ("taylor_sine", "taylor_sin"),
    ("taylor_sine", "sinsin"),
    ("taylor_sine", "sinsin_b1"),
    ("taylor_sine", "sinsin_b2"),
    ("taylor_sine", "sinsin_b3")
  ]

-- |Files which take at least a few seconds to process by PropaFP
slowTestFiles :: [(String, String)]
slowTestFiles = 
  [
    ("hie_sine", "reduce_half_pi_ge"),
    ("hie_sine", "reduce_half_pi_le")
  ]

-- |Files unsupported by the MetiTarski translator
unsupportedByMetiTarskiFiles :: [(String, String)]
unsupportedByMetiTarskiFiles =
  [
    ("hie_sine", "my_machine_rounding_ge"),
    ("hie_sine", "my_machine_rounding_le"),
    ("hie_sine", "sin_ge"),
    ("hie_sine", "sin_le"),
    ("taylor_sine", "taylor_sin_double"),
    ("taylor_sine", "taylor_sin_p"),
    ("taylor_sine", "taylor_sin_plus"),
    ("taylor_sine", "taylor_sin_swap"),
    ("taylor_sine", "taylor_sin_tight"),
    ("taylor_sine", "taylor_sin")
  ]

-- |Quick + slow test files
allTestFiles :: [(String, String)]
allTestFiles = quickTestFiles ++ slowTestFiles

-- |Provers for which PropaFP provides translators
data SupportedProver = MetiTarski | DReal

-- |Get the translator function for a chosen prover
getTranslator :: SupportedProver -> (F -> TypedVarMap -> String)
getTranslator MetiTarski = formulaAndVarMapToMetiTarski
getTranslator DReal = formulaAndVarMapToDReal

-- |Check if PropaFP should negate a VC before translating for one of these provers
getNegationStatus :: SupportedProver -> Bool
getNegationStatus MetiTarski = True
getNegationStatus DReal = False

-- |Get the file extension that the PropaFP translator writes to for a certain prover
getFileExtension :: SupportedProver -> String
getFileExtension MetiTarski = "tptp"
getFileExtension DReal = "smt2"

-- |Get the name of the folder under which the translated files are stored in the PropaFP repo
getProverFolderName :: SupportedProver -> String
getProverFolderName MetiTarski = "metit"
getProverFolderName DReal = "smt"