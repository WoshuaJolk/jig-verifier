import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Order.Lattice.Nat
import Mathlib.Tactic

open Finset

namespace Submissions.Erdos400PositiveExcess.Worker04

noncomputable def g (k n : ℕ) : ℕ :=
  sSup {x | ∃ a : Fin k → ℕ,
    (∏ i, Nat.factorial (a i)) ∣ Nat.factorial n ∧ x = (∑ i, a i) - n}

theorem proof : ∀ k n : ℕ, 2 ≤ k → 0 < g k n := by
  intro k n hk
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 2 := ⟨k - 2, by omega⟩
  simp only [g]
  set a : Fin (k' + 2) → ℕ := fun i =>
    if (i : ℕ) = 0 then n else if (i : ℕ) = 1 then 1 else 0 with ha_def
  have hprod : ∏ i : Fin (k' + 2), Nat.factorial (a i) = Nat.factorial n := by
    rw [Fin.prod_univ_succ]
    simp [ha_def]
    rw [Fin.prod_univ_succ]
    simp
  have hsum : ∑ i : Fin (k' + 2), a i = n + 1 := by
    rw [Fin.sum_univ_succ]
    simp [ha_def]
  have hmem : 1 ∈ {x | ∃ b : Fin (k' + 2) → ℕ,
      (∏ i, Nat.factorial (b i)) ∣ Nat.factorial n ∧
      x = (∑ i, b i) - n} := by
    refine ⟨a, hprod ▸ dvd_refl (Nat.factorial n), ?_⟩
    omega
  have hbdd : BddAbove {x | ∃ b : Fin (k' + 2) → ℕ,
      (∏ i, Nat.factorial (b i)) ∣ Nat.factorial n ∧
      x = (∑ i, b i) - n} := by
    refine ⟨(k' + 2) * Nat.factorial n, ?_⟩
    rintro x ⟨b, hb, rfl⟩
    calc
      (∑ i, b i) - n ≤ ∑ i, b i := Nat.sub_le _ _
      _ ≤ ∑ i : Fin (k' + 2), Nat.factorial (b i) :=
        Finset.sum_le_sum fun i _ ↦ Nat.self_le_factorial _
      _ ≤ Finset.univ.card • Nat.factorial n := by
        apply Finset.sum_le_card_nsmul
        intro i _
        exact le_trans
          (Finset.single_le_prod' (fun j _ ↦
            Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero _))
            (Finset.mem_univ i))
          (Nat.le_of_dvd (Nat.factorial_pos n) hb)
      _ = (k' + 2) * Nat.factorial n := by simp [smul_eq_mul]
  exact Nat.lt_of_lt_of_le Nat.one_pos (le_csSup hbdd hmem)

end Submissions.Erdos400PositiveExcess.Worker04
