import Mathlib.Data.Nat.Prime.Nth
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Tactic

open Filter

namespace Submissions.Erdos238SingletonPrimeBlock.FirstPrime

noncomputable def primeGap (n : ℕ) : ℕ :=
  (n + 1).nth Nat.Prime - n.nth Nat.Prime

theorem proof :
    ∀ c₂ : ℝ, ∀ᶠ (x : ℝ) in atTop,
      ∃ f : Fin 1 → ℕ, ∃ m : ℕ,
        (∀ i, f i ≤ x ∧ f i = (m + i.1).nth Nat.Prime) ∧
        ∀ i : Fin (1 - 1), c₂ < primeGap (m + i.1) := by
  intro c₂
  filter_upwards [eventually_ge_atTop (2 : ℝ)] with x hx
  refine ⟨fun _ ↦ 2, 0, ?_, ?_⟩
  · intro i
    constructor
    · exact_mod_cast hx
    · have hi : i = 0 := Fin.eq_zero i
      subst i
      simpa using Nat.nth_prime_zero_eq_two.symm
  · intro i
    exact Fin.elim0 i

end Submissions.Erdos238SingletonPrimeBlock.FirstPrime
