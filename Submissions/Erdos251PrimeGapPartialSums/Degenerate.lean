import Mathlib.Data.Nat.Prime.Nth
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace Submissions.Erdos251PrimeGapPartialSums.Degenerate

noncomputable abbrev p (n : ℕ) : ℝ := Nat.nth Nat.Prime n

theorem proof : False →
    ∀ N : ℕ,
      (∑ n ∈ Finset.range (N + 1), p n / 2 ^ n) =
        4 + (∑ n ∈ Finset.range N, (p (n + 1) - p n) / 2 ^ n) -
          p N / 2 ^ N :=
  False.elim

end Submissions.Erdos251PrimeGapPartialSums.Degenerate
