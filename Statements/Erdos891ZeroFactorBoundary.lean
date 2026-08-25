import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Topology.Instances.Nat

open Nat Filter Finset
open scoped ArithmeticFunction.omega

namespace Statements.Erdos891ZeroFactorBoundary

/-- The zero-factor boundary of Erdős Problem 891. -/
abbrev statement : Prop :=
  ∀ᶠ n : ℕ in atTop,
    ∃ m ∈ Ico n (n + 1), 0 < ω m

theorem target : statement := sorry

end Statements.Erdos891ZeroFactorBoundary
