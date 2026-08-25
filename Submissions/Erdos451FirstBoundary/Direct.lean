import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic

namespace Submissions.Erdos451FirstBoundary.Direct

def GoodBlock (k n : ℕ) : Prop :=
  2 * k < n ∧
    ∀ p : ℕ, p.Prime → k < p → p < 2 * k →
      ¬p ∣ ∏ i ∈ Finset.range k, (n - (i + 1))

def LeastGoodBlock (k n : ℕ) : Prop :=
  GoodBlock k n ∧
    ∀ m : ℕ, GoodBlock k m → n ≤ m

theorem proof : LeastGoodBlock 1 3 := by
  constructor
  · refine ⟨by omega, ?_⟩
    intro p hp h1p hp2
    omega
  · intro m hm
    have hm3 : 2 < m := hm.1
    omega

end Submissions.Erdos451FirstBoundary.Direct
