import RevHalt.Theory.Canonicity
import RevHalt.Theory.Categorical
import RevHalt.Theory.Stabilization
import RevHalt.Theory.ScottTopology
import RevHalt.Theory.RECodePred
import RevHalt.Theory.RECodePredExtras
import RevHalt.Theory.REPredExtras
import RevHalt.Theory.Impossibility
import RevHalt.Theory.GodelLens
import RevHalt.Theory.GodelIStandard
import RevHalt.Theory.ArithmeticLanguage
import RevHalt.Theory.ArithmeticLanguagePure
import RevHalt.Theory.ArithmeticEncoding
import RevHalt.Theory.ArithmeticNumerals
import RevHalt.Theory.ArithmeticProvability
import RevHalt.Theory.ArithmeticProofSystem
import RevHalt.Theory.GodelIArithmetic
import RevHalt.Theory.GodelIProofChecker
import RevHalt.Theory.GodelIProofCheckerEvaln
import RevHalt.Theory.GodelIArithEvalnSigma1
import RevHalt.Theory.GodelIArithmeticQ
import RevHalt.Theory.RobinsonQ
import RevHalt.Theory.RobinsonQProvability
import RevHalt.Theory.Complementarity
import RevHalt.Theory.QuantifierSwap
import RevHalt.Theory.ThreeBlocksArchitecture
import RevHalt.Theory.ConvergenceSigma1
import RevHalt.Theory.Arithmetization.HaltsSigma1
import RevHalt.Theory.Arithmetization.HaltsSigma1Pure
import RevHalt.Theory.Arithmetization.BasicNat0
import RevHalt.Theory.Arithmetization.NatPair0
import RevHalt.Theory.Arithmetization.NatUnpair0
import RevHalt.Theory.Arithmetization.PartrecCodeEncoding0
import RevHalt.Theory.Arithmetization.NatMod0
import RevHalt.Theory.Arithmetization.GodelBeta0
import RevHalt.Theory.Arithmetization.EvalnGraphPure
import RevHalt.Theory.AbstractDynamics
import RevHalt.Theory.OrdinalBoundary
import RevHalt.Theory.OrdinalMechanical
import RevHalt.Theory.RelativeFoundations
import RevHalt.Theory.RelativeR1

/-!
# RevHalt.Theory

Entry point for the Theory layer (T1/T2/T3 + extensions).

Exports: T1_traces, T1_uniqueness, T2_impossibility, T3_weak_extension, T3_strong,
  plus architecture (`ThreeBlocksArchitecture`), dynamics (`AbstractDynamics`),
  ordinal boundary files (`OrdinalBoundary`, `OrdinalMechanical`),
  and relative foundation layers (`RelativeFoundations`, `RelativeR1`).
-/
