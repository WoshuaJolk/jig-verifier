import Mathlib.Data.Finset.CastCard
import Mathlib.Data.Finset.Interval
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Nat.Sqrt
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic

namespace Submissions.Erdos30DifferenceCountingBound.Direct

open Finset

def IsSidon (A : Finset ℕ) : Prop :=
  ∀ ⦃a b c d : ℕ⦄,
    a ∈ A → b ∈ A → c ∈ A → d ∈ A →
      a + b = c + d →
        (a = c ∧ b = d) ∨ (a = d ∧ b = c)

theorem card_mul_pred_le {A : Finset ℕ} {N : ℕ}
    (hsub : A ⊆ Finset.Icc 1 N) (hsidon : IsSidon A) (hN : 1 ≤ N) :
    (A.card : ℤ) * ((A.card : ℤ) - 1) ≤ 2 * ((N : ℤ) - 1) := by
  let diff : ℕ × ℕ → ℤ := fun x => (x.1 : ℤ) - (x.2 : ℤ)
  have hdiff_inj : Set.InjOn diff A.offDiag := by
    intro x hx y hy hxy
    rcases x with ⟨a, b⟩
    rcases y with ⟨c, d⟩
    have hx' : a ∈ A ∧ b ∈ A ∧ a ≠ b := by
      simpa using hx
    have hy' : c ∈ A ∧ d ∈ A ∧ c ≠ d := by
      simpa using hy
    dsimp [diff] at hxy
    have hsum_int : (a : ℤ) + d = c + b := by
      linarith
    have hsum : a + d = c + b := by
      exact_mod_cast hsum_int
    rcases hsidon hx'.1 hy'.2.1 hy'.1 hx'.2.1 hsum with hpair | hswap
    · rcases hpair with ⟨ha, hd⟩
      ext <;> simp [ha, hd]
    · exact (hx'.2.2 hswap.1).elim
  have hsubset :
      A.offDiag.image diff ⊆ (Finset.Icc (1 - (N : ℤ)) ((N : ℤ) - 1)).erase 0 := by
    intro z hz
    rcases Finset.mem_image.mp hz with ⟨x, hx, rfl⟩
    rcases x with ⟨a, b⟩
    have hx' : a ∈ A ∧ b ∈ A ∧ a ≠ b := by
      simpa using hx
    have ha_nat := Finset.mem_Icc.mp (hsub hx'.1)
    have hb_nat := Finset.mem_Icc.mp (hsub hx'.2.1)
    have ha : (1 : ℤ) ≤ a ∧ (a : ℤ) ≤ N := by exact_mod_cast ha_nat
    have hb : (1 : ℤ) ≤ b ∧ (b : ℤ) ≤ N := by exact_mod_cast hb_nat
    refine Finset.mem_erase.mpr ⟨?_, ?_⟩
    · dsimp [diff]
      exact sub_ne_zero.mpr (by exact_mod_cast hx'.2.2)
    · rw [Finset.mem_Icc]
      dsimp [diff]
      constructor <;> linarith
  have hzero :
      (0 : ℤ) ∈ Finset.Icc (1 - (N : ℤ)) ((N : ℤ) - 1) := by
    have hN_int : (1 : ℤ) ≤ N := by exact_mod_cast hN
    rw [Finset.mem_Icc]
    constructor <;> omega
  have hIcc_card :
      ((Finset.Icc (1 - (N : ℤ)) ((N : ℤ) - 1)).card : ℤ) = 2 * N - 1 := by
    have hN_int : (1 : ℤ) ≤ N := by exact_mod_cast hN
    calc
      ((Finset.Icc (1 - (N : ℤ)) ((N : ℤ) - 1)).card : ℤ) =
          ((N : ℤ) - 1) + 1 - (1 - (N : ℤ)) := by
            exact Int.card_Icc_of_le
              (a := 1 - (N : ℤ)) (b := (N : ℤ) - 1) (by linarith)
      _ = 2 * N - 1 := by ring
  calc
    (A.card : ℤ) * ((A.card : ℤ) - 1) = ((A.offDiag).card : ℤ) := by
      have hmul : A.card ≤ A.card * A.card := by
        by_cases hA0 : A.card = 0
        · omega
        · have hA1 : 1 ≤ A.card := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hA0)
          calc
            A.card = A.card * 1 := by rw [Nat.mul_one]
            _ ≤ A.card * A.card := Nat.mul_le_mul_left _ hA1
      rw [Finset.offDiag_card, Nat.cast_sub hmul, Nat.cast_mul]
      ring
    _ = ((A.offDiag.image diff).card : ℤ) := by
      rw [Finset.card_image_of_injOn hdiff_inj]
    _ ≤ (((Finset.Icc (1 - (N : ℤ)) ((N : ℤ) - 1)).erase 0).card : ℤ) := by
      exact_mod_cast Finset.card_le_card hsubset
    _ = ((Finset.Icc (1 - (N : ℤ)) ((N : ℤ) - 1)).card : ℤ) - 1 := by
      simpa using
        (Finset.cast_card_erase_of_mem (R := ℤ)
          (s := Finset.Icc (1 - (N : ℤ)) ((N : ℤ) - 1)) hzero)
    _ = (2 * (N : ℤ) - 1) - 1 := by rw [hIcc_card]
    _ = 2 * ((N : ℤ) - 1) := by ring

theorem proof :
    ∀ (N : ℕ) (A : Finset ℕ),
      A ⊆ Finset.Icc 1 N →
      IsSidon A →
      A.card ≤ Nat.sqrt (2 * N) + 1 := by
  intro N A hsub hsidon
  by_cases hN : N = 0
  · subst N
    have hA : A = ∅ := by
      ext a
      simp only [Finset.notMem_empty, iff_false]
      intro ha
      have := Finset.mem_Icc.mp (hsub ha)
      omega
    simp [hA]
  have hN1 : 1 ≤ N := Nat.one_le_iff_ne_zero.mpr hN
  by_cases hcard0 : A.card = 0
  · omega
  have hcard1 : 1 ≤ A.card := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hcard0)
  have hmul :
      (A.card : ℤ) * ((A.card : ℤ) - 1) ≤ 2 * ((N : ℤ) - 1) :=
    card_mul_pred_le hsub hsidon hN1
  have hsq :
      (((A.card - 1 : ℕ) : ℤ) * (((A.card - 1 : ℕ) : ℤ))) ≤ (2 * N : ℤ) := by
    have hsq_left :
        ((A.card : ℤ) - 1) * ((A.card : ℤ) - 1) ≤
          (A.card : ℤ) * ((A.card : ℤ) - 1) := by
      have hcard1z : (1 : ℤ) ≤ A.card := by exact_mod_cast hcard1
      have hnonneg : 0 ≤ (A.card : ℤ) - 1 := by omega
      nlinarith
    have hcast :
        ((A.card : ℤ) - 1) * ((A.card : ℤ) - 1) =
          (((A.card - 1 : ℕ) : ℤ) * (((A.card - 1 : ℕ) : ℤ))) := by
      rw [← Int.ofNat_one, ← Int.ofNat_sub hcard1]
    rw [← hcast]
    omega
  have hsq_nat : (A.card - 1) * (A.card - 1) ≤ 2 * N := by
    exact_mod_cast hsq
  have hsqrt : A.card - 1 ≤ Nat.sqrt (2 * N) :=
    Nat.le_sqrt.2 hsq_nat
  omega

end Submissions.Erdos30DifferenceCountingBound.Direct
