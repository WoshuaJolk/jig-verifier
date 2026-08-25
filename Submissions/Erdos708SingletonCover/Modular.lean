import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic

open scoped BigOperators

namespace Submissions.Erdos708SingletonCover.Modular

theorem proof :
    ∀ a : ℕ, 2 ≤ a →
      ∀ s : ℕ, 1 ≤ s →
        ∃ B : Finset ℕ,
          B ⊆ Finset.Ico s (s + a) ∧
            B.card ≤ 1 ∧
              a ∣ ∏ b ∈ B, b := by
  intro a ha s _
  let r := (a - s % a) % a
  let b := s + r
  have ha0 : 0 < a := by omega
  have hr : r < a := Nat.mod_lt _ ha0
  have hdvd : a ∣ b := by
    by_cases hzero : s % a = 0
    · dsimp [b, r]
      simp [hzero, Nat.dvd_of_mod_eq_zero hzero]
    · have hle : s % a ≤ a := (Nat.mod_lt s ha0).le
      have hsub : a - s % a < a := by omega
      have hmod : (a - s % a) % a = a - s % a :=
        Nat.mod_eq_of_lt hsub
      refine ⟨s / a + 1, ?_⟩
      dsimp [b, r]
      rw [hmod]
      have hdecomp := Nat.mod_add_div s a
      calc
        s + (a - s % a) =
            (s % a + a * (s / a)) + (a - s % a) :=
          congrArg (fun x => x + (a - s % a)) hdecomp.symm
        _ = a * (s / a + 1) := by
          simp only [Nat.mul_add, Nat.mul_one]
          omega
  refine ⟨{b}, ?_, by simp, ?_⟩
  · intro x hx
    simp only [Finset.mem_singleton] at hx
    subst x
    simp only [Finset.mem_Ico]
    constructor <;> dsimp [b] <;> omega
  · simpa only [Finset.prod_singleton] using hdvd

end Submissions.Erdos708SingletonCover.Modular
