import Mathlib.Data.Finset.Card
import Mathlib.Tactic

namespace Submissions.Erdos1145PeriodicClosureUnbounded.ArithmeticProgressions

noncomputable def repCount (A B : Set ℕ) (n : ℕ) : ℕ := by
  classical
  exact ((Finset.range (n + 1)).filter fun a => a ∈ A ∧ n - a ∈ B).card

theorem proof :
    ∀ A B : Set ℕ, ∀ q a b : ℕ, 0 < q → a ∈ A → b ∈ B →
      (∀ x ∈ A, x + q ∈ A) →
      (∀ x ∈ B, x + q ∈ B) →
      ∀ K : ℕ, ∃ n : ℕ, K < repCount A B n := by
  intro A B q a b hq ha hb hA hB K
  classical
  have hAiter : ∀ j : ℕ, a + j * q ∈ A := by
    intro j
    induction j with
    | zero => simpa using ha
    | succ j ih =>
        convert hA (a + j * q) ih using 1 <;>
          simp [Nat.succ_mul, add_assoc]
  have hBiter : ∀ j : ℕ, b + j * q ∈ B := by
    intro j
    induction j with
    | zero => simpa using hb
    | succ j ih =>
        convert hB (b + j * q) ih using 1 <;>
          simp [Nat.succ_mul, add_assoc]
  let n := a + b + K * q
  let witnesses := (Finset.range (K + 1)).image fun j => a + j * q
  have hinj : Function.Injective (fun j : ℕ => a + j * q) := by
    intro i j hij
    have hm : i * q = j * q := Nat.add_left_cancel hij
    exact Nat.eq_of_mul_eq_mul_right hq hm
  have hcard : witnesses.card = K + 1 := by
    simp only [witnesses]
    rw [Finset.card_image_of_injective _ hinj, Finset.card_range]
  have hsub :
      witnesses ⊆
        (Finset.range (n + 1)).filter fun x => x ∈ A ∧ n - x ∈ B := by
    intro x hx
    simp only [witnesses, Finset.mem_image, Finset.mem_range] at hx
    obtain ⟨j, hj, rfl⟩ := hx
    have hjK : j ≤ K := by omega
    have hjq : j * q ≤ K * q := Nat.mul_le_mul_right q hjK
    have hmul : (K - j) * q = K * q - j * q := Nat.sub_mul K j q
    have hsubeq : n - (a + j * q) = b + (K - j) * q := by
      calc
        n - (a + j * q) =
            (a + (b + K * q)) - (a + j * q) := by simp [n, add_assoc]
        _ = (b + K * q) - j * q := Nat.add_sub_add_left _ _ _
        _ = b + (K * q - j * q) := by
          rw [Nat.add_sub_assoc hjq]
        _ = b + (K - j) * q := by rw [hmul]
    rw [Finset.mem_filter, Finset.mem_range]
    refine ⟨?_, hAiter j, ?_⟩
    · dsimp [n]
      omega
    · rw [hsubeq]
      exact hBiter (K - j)
  refine ⟨n, ?_⟩
  have hle := Finset.card_le_card hsub
  rw [hcard] at hle
  unfold repCount
  omega

end Submissions.Erdos1145PeriodicClosureUnbounded.ArithmeticProgressions
