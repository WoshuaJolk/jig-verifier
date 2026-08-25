import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Order.Lattice.Nat
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open ArithmeticFunction
open Filter Real
open scoped ArithmeticFunction.Omega

namespace Statements.Erdos535PairwiseGcdUpper

/-- `f r N` is the maximum size of a subset of `{1, ..., N}` with no
`r` elements whose pairwise greatest common divisors are all equal. -/
noncomputable def f (r N : ℕ) : ℕ :=
  sSup {k : ℕ | ∃ A : Finset ℕ, A ⊆ Finset.Icc 1 N ∧
    (∀ S ⊆ A, S.card = r →
      ¬ (∃ d, (S : Set ℕ).Pairwise fun a b => Nat.gcd a b = d)) ∧
    A.card = k}

/-- Erdős Problem 535: the conjectural upper bound for every fixed
tuple size `r ≥ 3`. -/
abbrev statement : Prop :=
  ∀ r ≥ 3, ∃ c > (0 : ℝ),
    ∀ᶠ N : ℕ in atTop,
      (f r N : ℝ) ≤ (N : ℝ) ^ (c / log (log (N : ℝ)))

theorem target : statement := sorry

end Statements.Erdos535PairwiseGcdUpper
