import Mathlib.Analysis.Fourier.ZMod
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic

open scoped BigOperators ComplexConjugate ZMod

namespace Submissions.Erdos1CrossSliceFourierEnergy.PhaseAverage

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

private theorem subset_char_prod (q : ℕ) [NeZero q] (S : Finset ℕ) (k : ZMod q) :
    ∏ a ∈ S, ZMod.stdAddChar (-((a : ZMod q) * k)) =
      ZMod.stdAddChar (-(((S.sum id : ℕ) : ZMod q) * k)) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert a S ha ih =>
      rw [Finset.prod_insert ha, ih, Finset.sum_insert ha]
      push_cast
      simp only [id_eq, ← AddChar.map_add_eq_mul]
      congr 1
      ring

private noncomputable def sliceFourier (q : ℕ) [NeZero q]
    (A : Finset ℕ) (k : ZMod q) (j : ℕ) : ℂ :=
  ∑ S ∈ A.powersetCard j,
    ZMod.stdAddChar (-(((S.sum id : ℕ) : ZMod q) * k))

private noncomputable def phaseProduct (q : ℕ) [NeZero q]
    (A : Finset ℕ) (u : ZMod (A.card + 1)) (k : ZMod q) : ℂ :=
  ∏ a ∈ A, (1 + ZMod.stdAddChar (-u) *
    ZMod.stdAddChar (-((a : ZMod q) * k)))

private theorem phase_product_expansion (q : ℕ) [NeZero q]
    (A : Finset ℕ) (u : ZMod (A.card + 1)) (k : ZMod q) :
    phaseProduct q A u k =
      ∑ S ∈ A.powerset, ZMod.stdAddChar (-u) ^ S.card *
        ZMod.stdAddChar (-(((S.sum id : ℕ) : ZMod q) * k)) := by
  classical
  rw [phaseProduct, Finset.prod_one_add]
  apply Finset.sum_congr rfl
  intro S _
  rw [Finset.prod_mul_distrib, subset_char_prod]
  simp

private noncomputable def phaseSlices (q : ℕ) [NeZero q]
    (A : Finset ℕ) (k : ZMod q) (r : ZMod (A.card + 1)) : ℂ :=
  sliceFourier q A k r.val

theorem phase_dft_bridge (q : ℕ) [NeZero q]
    (A : Finset ℕ) (u : ZMod (A.card + 1)) (k : ZMod q) :
    ZMod.dft (phaseSlices q A k) u = phaseProduct q A u k := by
  rw [phase_product_expansion, ZMod.dft_apply]
  simp only [phaseSlices, smul_eq_mul]
  let e : ZMod (A.card + 1) ≃ Fin (A.card + 1) := Equiv.refl _
  rw [Fintype.sum_equiv e
    (fun r : ZMod (A.card + 1) =>
      ZMod.stdAddChar (-(r * u)) * sliceFourier q A k r.val)
    (fun r : Fin (A.card + 1) =>
      ZMod.stdAddChar (-(((r.val : ℕ) : ZMod (A.card + 1)) * u)) *
        sliceFourier q A k r.val) (by
          intro r
          change ZMod.stdAddChar (-(r * u)) * sliceFourier q A k r.val =
            ZMod.stdAddChar (-(((r.val : ℕ) : ZMod (A.card + 1)) * u)) *
              sliceFourier q A k r.val
          rw [ZMod.natCast_zmod_val])]
  have hfin :
      (∑ r : Fin (A.card + 1),
          ZMod.stdAddChar (-(((r.val : ℕ) : ZMod (A.card + 1)) * u)) *
            sliceFourier q A k r.val) =
        ∑ j ∈ Finset.range (A.card + 1),
          ZMod.stdAddChar (-((j : ZMod (A.card + 1)) * u)) *
            sliceFourier q A k j := by
    simpa using (Fin.sum_univ_eq_sum_range
      (fun j : ℕ =>
        ZMod.stdAddChar (-((j : ZMod (A.card + 1)) * u)) *
          sliceFourier q A k j) (A.card + 1))
  rw [hfin]
  simp only [sliceFourier]
  simp_rw [Finset.mul_sum]
  have hphase (j : ℕ) :
      ZMod.stdAddChar (-((j : ZMod (A.card + 1)) * u)) =
        ZMod.stdAddChar (-u) ^ j := by
    rw [← AddChar.map_nsmul_eq_pow]
    congr 1
    simp [nsmul_eq_mul]
  simp_rw [hphase]
  have hcard :
      ∑ j ∈ Finset.range (A.card + 1), ∑ S ∈ A.powersetCard j,
        ZMod.stdAddChar (-u) ^ j *
          ZMod.stdAddChar (-(((S.sum id : ℕ) : ZMod q) * k)) =
      ∑ j ∈ Finset.range (A.card + 1), ∑ S ∈ A.powersetCard j,
        ZMod.stdAddChar (-u) ^ S.card *
          ZMod.stdAddChar (-(((S.sum id : ℕ) : ZMod q) * k)) := by
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro S hS
    rw [(Finset.mem_powersetCard.mp hS).2]
  rw [hcard]
  rw [← Finset.sum_disjiUnion]
  · rw [← Finset.powerset_card_disjiUnion]
  · exact A.pairwise_disjoint_powersetCard.set_pairwise _

theorem phase_parseval (q : ℕ) [NeZero q]
    (A : Finset ℕ) (k : ZMod q) :
    ∑ u : ZMod (A.card + 1),
        conj (phaseProduct q A u k) * phaseProduct q A u k =
      (A.card + 1 : ℕ) * ∑ j ∈ Finset.range (A.card + 1),
        conj (sliceFourier q A k j) * sliceFourier q A k j := by
  simp_rw [← phase_dft_bridge]
  rw [dft_parseval]
  simp only [phaseSlices]
  have hsum :
      (∑ r : ZMod (A.card + 1),
          conj (sliceFourier q A k r.val) * sliceFourier q A k r.val) =
        ∑ j ∈ Finset.range (A.card + 1),
          conj (sliceFourier q A k j) * sliceFourier q A k j := by
    let e : ZMod (A.card + 1) ≃ Fin (A.card + 1) := Equiv.refl _
    rw [Fintype.sum_equiv e
      (fun r : ZMod (A.card + 1) =>
        conj (sliceFourier q A k r.val) * sliceFourier q A k r.val)
      (fun r : Fin (A.card + 1) =>
        conj (sliceFourier q A k r.val) * sliceFourier q A k r.val)
      (by intro r; rfl)]
    simpa using (Fin.sum_univ_eq_sum_range
      (fun j : ℕ =>
        conj (sliceFourier q A k j) * sliceFourier q A k j) (A.card + 1))
  rw [hsum]

private noncomputable def sliceCount (q : ℕ) (A : Finset ℕ) (j : ℕ)
    (r : ZMod q) : ℂ :=
  ((((A.powersetCard j).filter fun S =>
    ((S.sum id : ℕ) : ZMod q) = r).card : ℕ) : ℂ)

private theorem dft_sliceCount (q : ℕ) [NeZero q]
    (A : Finset ℕ) (j : ℕ) (k : ZMod q) :
    ZMod.dft (sliceCount q A j) k = sliceFourier q A k j := by
  simp only [ZMod.dft_apply, smul_eq_mul, sliceCount, Nat.cast_sum, sliceFourier]
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

private theorem slice_parseval (q : ℕ) [NeZero q] (A : Finset ℕ) (j : ℕ) :
    ∑ k : ZMod q, conj (sliceFourier q A k j) * sliceFourier q A k j =
      (q : ℂ) * ∑ r : ZMod q,
        (((((A.powersetCard j).filter fun S =>
          ((S.sum id : ℕ) : ZMod q) = r).card : ℕ) : ℂ) ^ 2) := by
  simp_rw [← dft_sliceCount]
  rw [dft_parseval]
  apply congrArg ((q : ℂ) * ·)
  apply Finset.sum_congr rfl
  intro r _
  simp [sliceCount, pow_two]

theorem cross_slice_parseval (q : ℕ) [NeZero q] (A : Finset ℕ) :
    ∑ k : ZMod q, ∑ u : ZMod (A.card + 1),
        conj (phaseProduct q A u k) * phaseProduct q A u k =
      ((A.card + 1 : ℕ) : ℂ) * (q : ℂ) *
        ∑ j ∈ Finset.range (A.card + 1), ∑ r : ZMod q,
          (((((A.powersetCard j).filter fun S =>
            ((S.sum id : ℕ) : ZMod q) = r).card : ℕ) : ℂ) ^ 2) := by
  simp_rw [phase_parseval]
  rw [← Finset.mul_sum]
  rw [Finset.sum_comm]
  rw [mul_assoc]
  apply congrArg (((A.card + 1 : ℕ) : ℂ) * ·)
  simp_rw [slice_parseval]
  rw [← Finset.mul_sum]

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

private theorem balanced_energy (q : ℕ) [NeZero q] (c : ZMod q → ℕ) :
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
  have hslt : s < q := Nat.mod_lt M hq
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

private theorem slice_integral_energy (q : ℕ) [NeZero q]
    (A : Finset ℕ) (j : ℕ) :
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

theorem aggregate_integral_energy (q : ℕ) [NeZero q] (A : Finset ℕ) :
    ∑ j ∈ Finset.range (A.card + 1),
        (let M := Nat.choose A.card j
         M ^ 2 + (M % q) * (q - M % q)) ≤
      q * ∑ j ∈ Finset.range (A.card + 1), ∑ r : ZMod q,
        (((A.powersetCard j).filter fun S =>
          ((S.sum id : ℕ) : ZMod q) = r).card) ^ 2 := by
  calc
    _ ≤ ∑ j ∈ Finset.range (A.card + 1),
        q * ∑ r : ZMod q, (((A.powersetCard j).filter fun S =>
          ((S.sum id : ℕ) : ZMod q) = r).card) ^ 2 := by
      apply Finset.sum_le_sum
      intro j _
      exact slice_integral_energy q A j
    _ = _ := by rw [← Finset.mul_sum]

theorem large_modulus_floor_is_diagonal (n : ℕ) :
    let q := 2 ^ n + 1
    ∑ j ∈ Finset.range (n + 1),
        (let M := Nat.choose n j
         M ^ 2 + (M % q) * (q - M % q)) = q * 2 ^ n := by
  dsimp only
  calc
    _ = ∑ j ∈ Finset.range (n + 1), (2 ^ n + 1) * Nat.choose n j := by
      apply Finset.sum_congr rfl
      intro j _
      have hlt : Nat.choose n j < 2 ^ n + 1 :=
        (Nat.choose_le_two_pow n j).trans_lt (Nat.lt_succ_self _)
      rw [Nat.mod_eq_of_lt hlt]
      have hsum :
          Nat.choose n j + (2 ^ n + 1 - Nat.choose n j) = 2 ^ n + 1 := by
        omega
      calc
        Nat.choose n j ^ 2 +
              Nat.choose n j * (2 ^ n + 1 - Nat.choose n j) =
            Nat.choose n j *
              (Nat.choose n j + (2 ^ n + 1 - Nat.choose n j)) := by ring
        _ = Nat.choose n j * (2 ^ n + 1) := by rw [hsum]
        _ = (2 ^ n + 1) * Nat.choose n j := Nat.mul_comm _ _
    _ = (2 ^ n + 1) * 2 ^ n := by
      rw [← Finset.mul_sum, Nat.sum_range_choose]

theorem proof :
    ∀ (q : ℕ) [NeZero q] (A : Finset ℕ),
      let m := A.card + 1
      let P : ZMod m → ZMod q → ℂ := fun u k =>
        ∏ a ∈ A, (1 + ZMod.stdAddChar (-u) *
          ZMod.stdAddChar (-((a : ZMod q) * k)))
      let F : ℕ → ZMod q → ℂ := fun j k =>
        ∑ S ∈ A.powersetCard j,
          ZMod.stdAddChar (-(((S.sum id : ℕ) : ZMod q) * k))
      let c : ℕ → ZMod q → ℕ := fun j r =>
        ((A.powersetCard j).filter fun S => ((S.sum id : ℕ) : ZMod q) = r).card
      (∀ k : ZMod q,
        ∑ u : ZMod m, conj (P u k) * P u k =
          (m : ℂ) * ∑ j ∈ Finset.range m, conj (F j k) * F j k) ∧
      (∑ k : ZMod q, ∑ u : ZMod m, conj (P u k) * P u k =
        (m : ℂ) * (q : ℂ) *
          ∑ j ∈ Finset.range m, ∑ r : ZMod q, ((c j r : ℂ) ^ 2)) ∧
      (∑ j ∈ Finset.range m,
          (let M := Nat.choose A.card j
           M ^ 2 + (M % q) * (q - M % q)) ≤
        q * ∑ j ∈ Finset.range m, ∑ r : ZMod q, (c j r) ^ 2) ∧
      (let Q := 2 ^ A.card + 1
       ∑ j ∈ Finset.range m,
          (let M := Nat.choose A.card j
           M ^ 2 + (M % Q) * (Q - M % Q)) = Q * 2 ^ A.card) := by
  intro q _ A
  dsimp only
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro k
    simpa only [phaseProduct, sliceFourier] using phase_parseval q A k
  · simpa only [phaseProduct] using cross_slice_parseval q A
  · exact aggregate_integral_energy q A
  · exact large_modulus_floor_is_diagonal A.card

end Submissions.Erdos1CrossSliceFourierEnergy.PhaseAverage
