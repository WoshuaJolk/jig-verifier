import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Prime.Nth

namespace Statements.Erdos233PrimeGapSquareUpper

open Filter Real
open scoped BigOperators Topology

noncomputable def primeGap (n : ℕ) : ℕ :=
  (n + 1).nth Nat.Prime - n.nth Nat.Prime

/-- Erdős Problem 233: the sum of the squares of the first `N`
consecutive-prime gaps is `O(N (log N)^2)`. -/
abbrev statement : Prop :=
  (fun N : ℕ =>
      (((∑ n ∈ Finset.range N, (primeGap n) ^ 2 : ℕ) : ℕ) : ℝ))
    =O[atTop]
  (fun N : ℕ => (N : ℝ) * (Real.log N) ^ 2)

theorem target : statement := sorry

end Statements.Erdos233PrimeGapSquareUpper
