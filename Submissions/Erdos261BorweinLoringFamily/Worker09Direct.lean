import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

open scoped BigOperators
open Finset

namespace Submissions.Erdos261BorweinLoringFamily.Worker09Direct

def indices (n m : ℕ) : Finset ℕ :=
  (range m).image fun i => n + i + 1

def HasRepresentation (n : ℕ) : Prop :=
  ∃ A : Finset ℕ,
    2 ≤ A.card ∧
    (∀ a ∈ A, 1 ≤ a) ∧
    (n : ℚ) / (2 : ℚ) ^ n =
      ∑ a ∈ A, (a : ℚ) / (2 : ℚ) ^ a

theorem shift_injective (n : ℕ) :
    Function.Injective fun i : ℕ => n + i + 1 := by
  intro i j h
  exact Nat.add_left_cancel (Nat.add_right_cancel h)

theorem sum_block (n m : ℕ) :
    (∑ i ∈ range m, (n + i + 1 : ℚ) / (2 : ℚ) ^ (n + i + 1)) =
      (n + 2 : ℚ) / (2 : ℚ) ^ n -
        (n + m + 2 : ℚ) / (2 : ℚ) ^ (n + m) := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [sum_range_succ, ih, Nat.add_succ, pow_succ]
      norm_num [Nat.cast_add, Nat.cast_one]
      ring

theorem proof :
    ∀ (n m : ℕ), 2 ≤ m →
      n + m + 2 = 2 ^ (m + 1) →
      HasRepresentation n := by
  intro n m hm hrelation
  refine ⟨indices n m, ?_, ?_, ?_⟩
  · rw [indices, Finset.card_image_of_injective _ (shift_injective n)]
    simpa using hm
  · intro a ha
    simp only [indices, mem_image, mem_range] at ha
    obtain ⟨i, -, rfl⟩ := ha
    exact Nat.zero_lt_succ _
  · rw [show (∑ a ∈ indices n m, (a : ℚ) / (2 : ℚ) ^ a) =
        ∑ i ∈ range m, (n + i + 1 : ℚ) / (2 : ℚ) ^ (n + i + 1) by
          simp [indices]]
    rw [sum_block]
    have hq := congrArg (fun x : ℕ => (x : ℚ)) hrelation
    norm_num [Nat.cast_add] at hq
    rw [hq]
    norm_num [pow_succ, pow_add]
    field_simp
    ring

end Submissions.Erdos261BorweinLoringFamily.Worker09Direct
