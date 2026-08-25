import Mathlib.Data.Real.Basic
import Mathlib.Order.Interval.Set.Nat
import Mathlib.Tactic

namespace Submissions.Erdos14SingletonExceptions.Direct

def uniquePairSums (A : Set ℕ) : Set ℕ :=
  {n | ∃ p : ℕ × ℕ, p.1 ∈ A ∧ p.2 ∈ A ∧ p.1 + p.2 = n ∧
    ∀ a₁ ∈ A, ∀ a₂ ∈ A, a₁ + a₂ = n →
      (a₁ = p.1 ∧ a₂ = p.2) ∨ (a₁ = p.2 ∧ a₂ = p.1)}

noncomputable def exceptionCount (A : Set ℕ) (N : ℕ) : ℝ :=
  (((Set.Icc 1 N) \ uniquePairSums A).ncard : ℝ)

theorem singleton_uniquePairSums (a : ℕ) :
    uniquePairSums {a} = {2 * a} := by
  ext n
  constructor
  · rintro ⟨⟨x, y⟩, hx, hy, hsum, _⟩
    simp only [Set.mem_singleton_iff] at hx hy ⊢
    subst x
    subst y
    omega
  · simp only [Set.mem_singleton_iff]
    intro h
    subst n
    refine ⟨(a, a), by simp, by simp, by omega, ?_⟩
    intro x hx y hy _
    simp_all

theorem proof : ∀ a N : ℕ, exceptionCount {a} N =
    if 1 ≤ 2 * a ∧ 2 * a ≤ N then (N - 1 : ℕ) else N := by
  intro a N
  rw [exceptionCount, singleton_uniquePairSums]
  split_ifs with h
  · norm_cast
    simp [h]
  · norm_cast
    simp [h]

end Submissions.Erdos14SingletonExceptions.Direct
