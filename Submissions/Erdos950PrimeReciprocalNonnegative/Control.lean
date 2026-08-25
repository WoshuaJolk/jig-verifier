import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic

namespace Submissions.Erdos950PrimeReciprocalNonnegative.Control

noncomputable def f (n : ℕ) : ℝ :=
  ∑ p ∈ (Finset.range n).filter Nat.Prime,
    (1 : ℝ) / (n - p : ℝ)

abbrev claimedStatement : Prop := ∀ n : ℕ, 0 ≤ f n

theorem vacuousHypothesis : False → claimedStatement := False.elim

end Submissions.Erdos950PrimeReciprocalNonnegative.Control
