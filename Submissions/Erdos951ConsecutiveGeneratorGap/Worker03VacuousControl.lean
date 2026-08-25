import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finsupp.Basic
import Mathlib.Data.Real.Basic

namespace Submissions.Erdos951ConsecutiveGeneratorGap.Worker03VacuousControl

def beurlingInteger (a : ℕ → ℝ) (k : ℕ →₀ ℕ) : ℝ :=
  k.prod fun i e ↦ (a i) ^ e

def Separated (a : ℕ → ℝ) : Prop :=
  ∀ k l : ℕ →₀ ℕ, k ≠ l →
    |beurlingInteger a k - beurlingInteger a l| ≥ 1

theorem proof (h : False) :
    ∀ a : ℕ → ℝ, StrictMono a → Separated a →
      ∀ n : ℕ, 1 ≤ a (n + 1) - a n := h.elim

end Submissions.Erdos951ConsecutiveGeneratorGap.Worker03VacuousControl
