import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic

namespace Submissions.Erdos882InjectiveCountingBound.Direct

open Finset

theorem proof :
    ∀ n : ℕ, ∀ A : Finset ℕ,
      A ⊆ Icc 1 n →
      (∀ B ∈ A.powerset, ∀ C ∈ A.powerset,
        B.sum id = C.sum id → B = C) →
      2 ^ A.card ≤ A.card * n + 1 := by
  intro n A hA hinj
  let sums := A.powerset.image fun B => B.sum id
  have hrange : sums ⊆ Finset.range (A.card * n + 1) := by
    intro x hx
    rw [Finset.mem_image] at hx
    obtain ⟨B, hB, rfl⟩ := hx
    rw [Finset.mem_powerset] at hB
    rw [Finset.mem_range]
    have hsum : B.sum id ≤ A.card * n := by
      calc
        B.sum id ≤ B.card * n := by
          apply Finset.sum_le_card_nsmul
          intro b hb
          exact (Finset.mem_Icc.mp (hA (hB hb))).2
        _ ≤ A.card * n := Nat.mul_le_mul_right n (Finset.card_le_card hB)
    omega
  calc
    2 ^ A.card = A.powerset.card := by simp
    _ = sums.card := by
      symm
      apply Finset.card_image_of_injOn
      intro B hB C hC h
      exact hinj B hB C hC h
    _ ≤ (Finset.range (A.card * n + 1)).card :=
      Finset.card_le_card hrange
    _ = A.card * n + 1 := by simp

end Submissions.Erdos882InjectiveCountingBound.Direct
