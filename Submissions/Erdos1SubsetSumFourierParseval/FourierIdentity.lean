import Mathlib.Analysis.Fourier.ZMod
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic

open scoped BigOperators ComplexConjugate ZMod

namespace Submissions.Erdos1SubsetSumFourierParseval.FourierIdentity

private lemma char_sum (q : ℕ) [NeZero q] (t : ZMod q) :
    ∑ k : ZMod q, ZMod.stdAddChar (t * k) = if t = 0 then (q : ℂ) else 0 := by
  split_ifs with h
  · simp [h]
  · exact AddChar.sum_eq_zero_of_ne_one (ZMod.isPrimitive_stdAddChar q h)

private lemma char_conj (q : ℕ) [NeZero q] (t : ZMod q) :
    conj (ZMod.stdAddChar t) = ZMod.stdAddChar (-t) := by
  rw [AddChar.map_neg_eq_inv, ZMod.stdAddChar_apply]
  exact (Circle.coe_inv_eq_conj _).symm

private theorem dft_parseval (q : ℕ) [NeZero q] (f : ZMod q → ℂ) :
    ∑ k : ZMod q, conj (ZMod.dft f k) * ZMod.dft f k =
      q * ∑ r : ZMod q, conj (f r) * f r := by
  calc
    _ = ∑ k : ZMod q, ∑ r : ZMod q, ∑ s : ZMod q,
          (conj (f r) * f s) * ZMod.stdAddChar ((r - s) * k) := by
      apply Finset.sum_congr rfl
      intro k _
      rw [ZMod.dft_apply]
      simp only [smul_eq_mul, map_sum, map_mul]
      simp_rw [char_conj]
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro r _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro s _
      have hchar :
          ZMod.stdAddChar (- -(r * k)) * ZMod.stdAddChar (-(s * k)) =
            ZMod.stdAddChar ((r - s) * k) := by
        rw [← AddChar.map_add_eq_mul]
        congr 1
        ring
      rw [← hchar]
      ring
    _ = ∑ r : ZMod q, ∑ s : ZMod q,
          (conj (f r) * f s) * ∑ k : ZMod q, ZMod.stdAddChar ((r - s) * k) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro r _
      rw [Finset.sum_comm]
      simp_rw [← Finset.mul_sum]
    _ = _ := by
      simp_rw [char_sum, sub_eq_zero]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r _
      simp [eq_comm]
      ring

private theorem subset_character_product (q : ℕ) [NeZero q]
    (A : Finset ℕ) (k : ZMod q) :
    ∑ S ∈ A.powerset, ZMod.stdAddChar (-(((S.sum id : ℕ) : ZMod q) * k)) =
      ∏ a ∈ A, (1 + ZMod.stdAddChar (-((a : ZMod q) * k))) := by
  classical
  induction A using Finset.induction_on with
  | empty => simp
  | @insert a A ha ih =>
      have hins :
          (∑ S ∈ A.powerset,
              ZMod.stdAddChar (-((((insert a S).sum id : ℕ) : ZMod q) * k))) =
            ZMod.stdAddChar (-((a : ZMod q) * k)) *
              ∑ S ∈ A.powerset,
                ZMod.stdAddChar (-(((S.sum id : ℕ) : ZMod q) * k)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro S hS
        rw [Finset.sum_insert (Finset.notMem_of_mem_powerset_of_notMem hS ha)]
        push_cast
        simp only [id_eq, ← AddChar.map_add_eq_mul]
        congr 1
        ring
      rw [Finset.sum_powerset_insert ha, Finset.prod_insert ha, hins, ih]
      ring

private noncomputable def residueCount (q : ℕ) (A : Finset ℕ) (r : ZMod q) : ℂ :=
  (((A.powerset.filter fun S => ((S.sum id : ℕ) : ZMod q) = r).card : ℕ) : ℂ)

private theorem dft_residueCount (q : ℕ) [NeZero q]
    (A : Finset ℕ) (k : ZMod q) :
    ZMod.dft (residueCount q A) k =
      ∏ a ∈ A, (1 + ZMod.stdAddChar (-((a : ZMod q) * k))) := by
  rw [← subset_character_product]
  simp only [ZMod.dft_apply, smul_eq_mul, residueCount, Nat.cast_sum]
  calc
    _ = ∑ r : ZMod q, ZMod.stdAddChar (-(r * k)) *
          ∑ S ∈ A.powerset, if ((S.sum id : ℕ) : ZMod q) = r then (1 : ℂ) else 0 := by
      apply Finset.sum_congr rfl
      intro r _
      congr 1
      simp
    _ = _ := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro S _
      simp

private theorem subset_sum_parseval (q : ℕ) [NeZero q] (A : Finset ℕ) :
    ∑ k : ZMod q,
        conj (∏ a ∈ A, (1 + ZMod.stdAddChar (-((a : ZMod q) * k)))) *
          ∏ a ∈ A, (1 + ZMod.stdAddChar (-((a : ZMod q) * k))) =
      (q : ℂ) * ∑ r : ZMod q,
        ((((A.powerset.filter fun S =>
          ((S.sum id : ℕ) : ZMod q) = r).card : ℕ) : ℂ) ^ 2) := by
  simp_rw [← dft_residueCount]
  rw [dft_parseval]
  apply congrArg ((q : ℂ) * ·)
  apply Finset.sum_congr rfl
  intro r _
  simp [residueCount, pow_two]

theorem proof :
    ∀ (q : ℕ) [NeZero q] (A : Finset ℕ),
      (∀ k : ZMod q,
        ∑ S ∈ A.powerset, ZMod.stdAddChar (-(((S.sum id : ℕ) : ZMod q) * k)) =
          ∏ a ∈ A, (1 + ZMod.stdAddChar (-((a : ZMod q) * k)))) ∧
      (∑ k : ZMod q,
          conj (∏ a ∈ A, (1 + ZMod.stdAddChar (-((a : ZMod q) * k)))) *
            ∏ a ∈ A, (1 + ZMod.stdAddChar (-((a : ZMod q) * k))) =
        (q : ℂ) * ∑ r : ZMod q,
          ((((A.powerset.filter fun S =>
            ((S.sum id : ℕ) : ZMod q) = r).card : ℕ) : ℂ) ^ 2)) := by
  intro q _ A
  exact ⟨subset_character_product q A, subset_sum_parseval q A⟩

end Submissions.Erdos1SubsetSumFourierParseval.FourierIdentity
