import Mathlib.Data.Nat.Prime.Nth
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace Statements.Erdos251PrimeGapPartialSums

noncomputable abbrev p (n : ℕ) : ℝ := Nat.nth Nat.Prime n

/-- Finite summation by parts for the prime-weighted binary series. -/
abbrev statement : Prop :=
  ∀ N : ℕ,
    (∑ n ∈ Finset.range (N + 1), p n / 2 ^ n) =
      4 + (∑ n ∈ Finset.range N, (p (n + 1) - p n) / 2 ^ n) -
        p N / 2 ^ N

theorem target : statement := sorry

end Statements.Erdos251PrimeGapPartialSums
