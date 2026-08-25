import Mathlib.Analysis.Fourier.ZMod
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Finset.Powerset
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Tactic

open scoped BigOperators ComplexConjugate ZMod Polynomial

namespace Submissions.Erdos1FixedSliceFourierParseval.FixedSlice

private noncomputable def marker (q : ℕ) [NeZero q]
    (A : Finset ℕ) (k : ZMod q) : ℂ[X] :=
  ∏ a ∈ A, (1 + Polynomial.C (ZMod.stdAddChar (-((a : ZMod q) * k))) * Polynomial.X)

theorem marker_coeff (q : ℕ) [NeZero q] (A : Finset ℕ) (k : ZMod q) (j : ℕ) :
    (marker q A k).coeff j =
      ∑ S ∈ A.powersetCard j,
        ZMod.stdAddChar (-(((S.sum id : ℕ) : ZMod q) * k)) := by
  classical
  induction A using Finset.induction_on generalizing j with
  | empty =>
      cases j with
      | zero => simp [marker, Finset.powersetCard_zero]
      | succ j =>
          rw [Finset.powersetCard_eq_empty.mpr (by simp)]
          rw [marker]
          simp [Polynomial.coeff_one]
  | @insert a A ha ih =>
      cases j with
      | zero =>
          rw [Finset.powersetCard_zero]
          simp only [Finset.sum_singleton, Finset.sum_empty, Nat.cast_zero, zero_mul,
            neg_zero, AddChar.map_zero_eq_one]
          rw [marker, Polynomial.coeff_zero_prod]
          simp
      | succ j =>
          let c := ZMod.stdAddChar (-((a : ZMod q) * k))
          have hpoly :
              (1 + Polynomial.C c * Polynomial.X) * marker q A k =
                marker q A k + Polynomial.C c * (Polynomial.X * marker q A k) := by
            ring
          rw [marker, Finset.prod_insert ha]
          change
            (((1 + Polynomial.C c * Polynomial.X) * marker q A k).coeff (j + 1)) =
              ∑ S ∈ (insert a A).powersetCard (j + 1),
                ZMod.stdAddChar (-(((S.sum id : ℕ) : ZMod q) * k))
          rw [hpoly, Polynomial.coeff_add, Polynomial.coeff_C_mul,
            Polynomial.coeff_X_mul, ih (j + 1), ih j,
            Finset.powersetCard_succ_insert ha]
          have hd :
              Disjoint (A.powersetCard (j + 1))
                ((A.powersetCard j).image (insert a)) := by
            rw [Finset.disjoint_left]
            intro S hSA hSI
            obtain ⟨T, hTA, hST⟩ := Finset.mem_image.mp hSI
            subst S
            exact ha ((Finset.mem_powersetCard.mp hSA).1 (Finset.mem_insert_self a T))
          rw [Finset.sum_union hd]
          congr 1
          rw [Finset.mul_sum]
          apply Finset.sum_bij (fun T _ => insert a T)
          · intro T hT
            exact Finset.mem_image.mpr ⟨T, hT, rfl⟩
          · intro T₁ hT₁ T₂ hT₂ hEq
            have ha₁ : a ∉ T₁ := fun hmem =>
              ha ((Finset.mem_powersetCard.mp hT₁).1 hmem)
            have ha₂ : a ∉ T₂ := fun hmem =>
              ha ((Finset.mem_powersetCard.mp hT₂).1 hmem)
            have := congrArg (Finset.erase · a) hEq
            simpa [ha₁, ha₂] using this
          · intro S hS
            obtain ⟨T, hT, rfl⟩ := Finset.mem_image.mp hS
            exact ⟨T, hT, rfl⟩
          · intro T hT
            rw [Finset.sum_insert
              (fun hmem => ha ((Finset.mem_powersetCard.mp hT).1 hmem))]
            push_cast
            simp only [id_eq, c, ← AddChar.map_add_eq_mul]
            congr 1
            ring

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

private noncomputable def sliceCount (q : ℕ) (A : Finset ℕ) (j : ℕ)
    (r : ZMod q) : ℂ :=
  ((((A.powersetCard j).filter fun S =>
    ((S.sum id : ℕ) : ZMod q) = r).card : ℕ) : ℂ)

theorem dft_sliceCount (q : ℕ) [NeZero q]
    (A : Finset ℕ) (j : ℕ) (k : ZMod q) :
    ZMod.dft (sliceCount q A j) k = (marker q A k).coeff j := by
  rw [marker_coeff]
  simp only [ZMod.dft_apply, smul_eq_mul, sliceCount, Nat.cast_sum]
  calc
    _ = ∑ r : ZMod q, ZMod.stdAddChar (-(r * k)) *
          ∑ S ∈ A.powersetCard j,
            if ((S.sum id : ℕ) : ZMod q) = r then (1 : ℂ) else 0 := by
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

theorem slice_parseval (q : ℕ) [NeZero q] (A : Finset ℕ) (j : ℕ) :
    ∑ k : ZMod q, conj ((marker q A k).coeff j) * (marker q A k).coeff j =
      (q : ℂ) * ∑ r : ZMod q,
        (((((A.powersetCard j).filter fun S =>
          ((S.sum id : ℕ) : ZMod q) = r).card : ℕ) : ℂ) ^ 2) := by
  simp_rw [← dft_sliceCount]
  rw [dft_parseval]
  apply congrArg ((q : ℂ) * ·)
  apply Finset.sum_congr rfl
  intro r _
  simp [sliceCount, pow_two]

private theorem integer_parabola (x d : ℕ) :
    (((2 * d + 1) * x : ℕ) : ℤ) ≤
      (x : ℤ) ^ 2 + (d : ℤ) * ((d : ℤ) + 1) := by
  by_cases hxd : x ≤ d
  · have h₁ : 0 ≤ (d : ℤ) - (x : ℤ) := by omega
    have h₂ : 0 ≤ (d : ℤ) + 1 - (x : ℤ) := by omega
    have := mul_nonneg h₁ h₂
    push_cast
    nlinarith
  · have hdx : d + 1 ≤ x := by omega
    have h₁ : 0 ≤ (x : ℤ) - (d : ℤ) := by omega
    have h₂ : 0 ≤ (x : ℤ) - (d : ℤ) - 1 := by omega
    have := mul_nonneg h₁ h₂
    push_cast
    nlinarith

theorem balanced_energy (q : ℕ) [NeZero q] (c : ZMod q → ℕ) :
    let M := ∑ r : ZMod q, c r
    M ^ 2 + (M % q) * (q - M % q) ≤ q * ∑ r : ZMod q, (c r) ^ 2 := by
  dsimp only
  let M := ∑ r : ZMod q, c r
  let E := ∑ r : ZMod q, (c r) ^ 2
  let d := M / q
  let s := M % q
  have hp :
      ∑ r : ZMod q, ((((2 * d + 1) * c r : ℕ) : ℤ)) ≤
        ∑ r : ZMod q, ((c r : ℤ) ^ 2 + (d : ℤ) * ((d : ℤ) + 1)) := by
    apply Finset.sum_le_sum
    intro r _
    exact integer_parabola (c r) d
  have hbase :
      ((2 * d + 1 : ℕ) : ℤ) * (M : ℤ) ≤
        (E : ℤ) + (q : ℤ) * ((d : ℤ) * ((d : ℤ) + 1)) := by
    calc
      ((2 * d + 1 : ℕ) : ℤ) * (M : ℤ) =
          ∑ r : ZMod q, ((((2 * d + 1) * c r : ℕ) : ℤ)) := by
            simp [M, Finset.mul_sum]
      _ ≤ ∑ r : ZMod q, ((c r : ℤ) ^ 2 + (d : ℤ) * ((d : ℤ) + 1)) := hp
      _ = (E : ℤ) + (q : ℤ) * ((d : ℤ) * ((d : ℤ) + 1)) := by
        simp [E, Finset.sum_add_distrib]
  have hq : 0 < q := NeZero.pos q
  have hdiv : q * d + s = M := by
    simpa [d, s, Nat.mul_comm] using Nat.div_add_mod M q
  have hslt : s < q := by
    exact Nat.mod_lt M hq
  have hfinal :
      (M : ℤ) ^ 2 + (s : ℤ) * ((q : ℤ) - (s : ℤ)) ≤ (q : ℤ) * (E : ℤ) := by
    have hdivz : (q : ℤ) * (d : ℤ) + (s : ℤ) = (M : ℤ) := by
      exact_mod_cast hdiv
    have hscaled := mul_le_mul_of_nonneg_left hbase (show (0 : ℤ) ≤ (q : ℤ) by positivity)
    push_cast at hscaled
    nlinarith
  change M ^ 2 + s * (q - s) ≤ q * E
  have hsle : s ≤ q := hslt.le
  exact_mod_cast hfinal

theorem slice_integral_energy (q : ℕ) [NeZero q] (A : Finset ℕ) (j : ℕ) :
    let M := Nat.choose A.card j
    M ^ 2 + (M % q) * (q - M % q) ≤
      q * ∑ r : ZMod q,
        (((A.powersetCard j).filter fun S =>
          ((S.sum id : ℕ) : ZMod q) = r).card) ^ 2 := by
  dsimp only
  let c : ZMod q → ℕ := fun r =>
    ((A.powersetCard j).filter fun S => ((S.sum id : ℕ) : ZMod q) = r).card
  have hsum : (∑ r : ZMod q, c r) = Nat.choose A.card j := by
    calc
      _ = ∑ r : ZMod q, ∑ S ∈ A.powersetCard j,
            if ((S.sum id : ℕ) : ZMod q) = r then 1 else 0 := by
          apply Finset.sum_congr rfl
          intro r _
          simp [c]
      _ = ∑ S ∈ A.powersetCard j, ∑ r : ZMod q,
            if ((S.sum id : ℕ) : ZMod q) = r then 1 else 0 := by
          rw [Finset.sum_comm]
      _ = (A.powersetCard j).card := by simp
      _ = Nat.choose A.card j := Finset.card_powersetCard j A
  simpa only [c, hsum] using balanced_energy q c

theorem proof :
    ∀ (q : ℕ) [NeZero q] (A : Finset ℕ) (j : ℕ),
      let P : ZMod q → ℂ[X] := fun k =>
        ∏ a ∈ A, (1 + Polynomial.C (ZMod.stdAddChar (-((a : ZMod q) * k))) *
          Polynomial.X)
      let c : ZMod q → ℕ := fun r =>
        ((A.powersetCard j).filter fun S => ((S.sum id : ℕ) : ZMod q) = r).card
      (∀ k : ZMod q, (P k).coeff j =
        ∑ S ∈ A.powersetCard j,
          ZMod.stdAddChar (-(((S.sum id : ℕ) : ZMod q) * k))) ∧
      (∑ k : ZMod q, conj ((P k).coeff j) * (P k).coeff j =
        (q : ℂ) * ∑ r : ZMod q, ((c r : ℂ) ^ 2)) ∧
      (let M := Nat.choose A.card j
       M ^ 2 + (M % q) * (q - M % q) ≤ q * ∑ r : ZMod q, (c r) ^ 2) := by
  intro q _ A j
  dsimp only
  refine ⟨?_, ?_, ?_⟩
  · intro k
    simpa only [marker] using marker_coeff q A k j
  · simpa only [marker] using slice_parseval q A j
  · exact slice_integral_energy q A j

end Submissions.Erdos1FixedSliceFourierParseval.FixedSlice
