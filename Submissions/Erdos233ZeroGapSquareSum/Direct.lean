import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.Prime.Nth

namespace Submissions.Erdos233ZeroGapSquareSum.Direct

open scoped BigOperators

noncomputable def primeGap (n : ℕ) : ℕ :=
  (n + 1).nth Nat.Prime - n.nth Nat.Prime

theorem proof :
    (∑ n ∈ Finset.range 0, (primeGap n) ^ 2 : ℕ) = 0 := by
  simp

end Submissions.Erdos233ZeroGapSquareSum.Direct
