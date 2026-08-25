import Mathlib.Data.Nat.Factorization.Basic

namespace Statements.Erdos1203OmegaCalibration

abbrev statement : Prop := (Nat.primeFactors 1).card = 0

theorem target : statement := sorry

end Statements.Erdos1203OmegaCalibration
