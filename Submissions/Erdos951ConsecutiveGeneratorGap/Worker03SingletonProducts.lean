import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finsupp.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

namespace Submissions.Erdos951ConsecutiveGeneratorGap.Worker03SingletonProducts

def beurlingInteger (a : ℕ → ℝ) (k : ℕ →₀ ℕ) : ℝ :=
  k.prod fun i e ↦ (a i) ^ e

def Separated (a : ℕ → ℝ) : Prop :=
  ∀ k l : ℕ →₀ ℕ, k ≠ l →
    |beurlingInteger a k - beurlingInteger a l| ≥ 1

theorem proof :
    ∀ a : ℕ → ℝ, StrictMono a → Separated a →
      ∀ n : ℕ, 1 ≤ a (n + 1) - a n := by
  intro a hmono hsep n
  have hlt : a n < a (n + 1) := hmono (by omega)
  have hne :
      (Finsupp.single (n + 1) 1 : ℕ →₀ ℕ) ≠
        Finsupp.single n 1 := by
    intro h
    have := DFunLike.congr_fun h n
    simp at this
  have h : |a (n + 1) - a n| ≥ 1 := by
    simpa [beurlingInteger] using
      hsep (Finsupp.single (n + 1) 1) (Finsupp.single n 1) hne
  rw [abs_of_nonneg (by linarith)] at h
  exact h

end Submissions.Erdos951ConsecutiveGeneratorGap.Worker03SingletonProducts
