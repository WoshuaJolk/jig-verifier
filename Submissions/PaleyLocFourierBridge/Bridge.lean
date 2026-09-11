import Commons.PaleyLocalizationTheta
import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.RingTheory.IntegralDomain
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Group.Units.Equiv
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Circulant
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Tactic.Linarith

/-!
Exact finite Fourier extraction for both sides of the Paley localization.
The cyclic coordinates reuse square closure credited to woshuajolk's artifact
ccd0ab95-3712-4390-8ca0-bab1ca47c341 and the count from artifact
b3456f5e-e74d-403f-95de-16f405ee39b6. The permutation sum adapts Jig #7
support15. Finite Bochner reuses our support19, whose character orthogonality
follows Mathlib Analysis/Fourier/ZMod.lean (David Loeffler, Apache 2.0).
These audited proof bodies are copied because Submissions imports are forbidden.
This theorem gives an objective-preserving extraction, not a prime atom bound.
-/

open Commons Finset AddChar Matrix

namespace Submissions.PaleyLocFourierBridge.Bridge

namespace Coordinates

variable {p : ℕ} [Fact (Nat.Prime p)]

private lemma sq_mul {s t : ZMod p} (hs : IsNonzeroSq s) (ht : IsNonzeroSq t) :
    IsNonzeroSq (s * t) := by
  obtain ⟨hs0, a, rfl⟩ := hs
  obtain ⟨ht0, b, rfl⟩ := ht
  exact ⟨mul_ne_zero hs0 ht0, a * b, by ring⟩

private lemma sq_inv {s : ZMod p} (hs : IsNonzeroSq s) : IsNonzeroSq s⁻¹ := by
  obtain ⟨hs0, a, rfl⟩ := hs
  exact ⟨inv_ne_zero hs0, a⁻¹, by simp only [mul_inv]⟩

variable [NeZero p]

local instance vertexGroup : CommGroup (PaleyLocV p) where
  mul u v := ⟨(u : ZMod p) * (v : ZMod p), sq_mul u.2 v.2⟩
  one := ⟨1, one_ne_zero, 1, by simp⟩
  inv u := ⟨(u : ZMod p)⁻¹, sq_inv u.2⟩
  mul_assoc u v w := Subtype.ext (mul_assoc (u : ZMod p) v w)
  one_mul u := Subtype.ext (one_mul (u : ZMod p))
  mul_one u := Subtype.ext (mul_one (u : ZMod p))
  inv_mul_cancel u := Subtype.ext (inv_mul_cancel₀ u.2.1)
  mul_comm u v := Subtype.ext (mul_comm (u : ZMod p) v)

private lemma card_sq (hp2 : p ≠ 2) :
    2 * Fintype.card {x : ZMod p // x ≠ 0 ∧ IsSquare x} + 1 = p := by
  classical
  have hchar : ringChar (ZMod p) ≠ 2 := by rw [ZMod.ringChar_zmod_n]; exact hp2
  set χ := quadraticChar (ZMod p) with hχ
  set S := (univ : Finset (ZMod p)).filter (fun x => x ≠ 0 ∧ IsSquare x) with hS
  set N := (univ : Finset (ZMod p)).filter (fun x => x ≠ 0 ∧ ¬ IsSquare x) with hN
  have hpt : ∀ a : ZMod p,
      χ a = (if a ∈ S then (1 : ℤ) else 0) - (if a ∈ N then (1 : ℤ) else 0) := by
    intro a
    by_cases ha : a = 0
    · subst ha; simp [hS, hN, hχ]
    · by_cases hsq : IsSquare a
      · have h1 : χ a = 1 := (quadraticChar_one_iff_isSquare ha).mpr hsq
        simp [hS, hN, ha, hsq, h1]
      · have h1 : χ a = -1 := quadraticChar_neg_one_iff_not_isSquare.mpr hsq
        simp [hS, hN, ha, hsq, h1]
  have h0 : ∑ a : ZMod p, χ a = 0 := quadraticChar_sum_zero hchar
  rw [Finset.sum_congr rfl (fun a _ => hpt a), Finset.sum_sub_distrib] at h0
  simp only [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul, mul_one] at h0
  have hcards : S.card = N.card := by exact_mod_cast sub_eq_zero.mp h0
  have hSe : S = (univ.erase (0 : ZMod p)).filter (fun x => IsSquare x) := by
    ext x; simp [hS, Finset.mem_erase]
  have hNe : N = (univ.erase (0 : ZMod p)).filter (fun x => ¬ IsSquare x) := by
    ext x; simp [hN, Finset.mem_erase]
  have hcardp : Fintype.card (ZMod p) = p := ZMod.card p
  have hp1 : 1 ≤ p := (Fact.out (p := Nat.Prime p)).one_lt.le.trans' (by norm_num)
  have hunion : S.card + N.card = p - 1 := by
    rw [hSe, hNe, Finset.card_filter_add_card_filter_not,
      Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, hcardp]
  have hsub : Fintype.card {x : ZMod p // x ≠ 0 ∧ IsSquare x} = S.card := by
    rw [hS, Fintype.card_subtype]
  rw [hsub]
  omega

private lemma card_vertices (hp2 : p ≠ 2) :
    Nat.card (PaleyLocV p) = (p - 1) / 2 := by
  have h : Fintype.card (PaleyLocV p)
      = Fintype.card {x : ZMod p // x ≠ 0 ∧ IsSquare x} :=
    Fintype.card_congr (Equiv.subtypeEquivRight (fun _ => Iff.rfl))
  have hc := card_sq hp2
  rw [← h] at hc
  rw [Nat.card_eq_fintype_card]
  omega

private lemma adj_ratio (u v : PaleyLocV p) :
    paleyLocAdj p u v ↔ IsNonzeroSq ((u : ZMod p) / (v : ZMod p) - 1) := by
  have hv : (v : ZMod p) ≠ 0 := v.2.1
  constructor
  · intro h
    have h1 := sq_mul h (sq_inv v.2)
    have he : ((u : ZMod p) - (v : ZMod p)) * (v : ZMod p)⁻¹ =
        (u : ZMod p) / (v : ZMod p) - 1 := by field_simp
    exact he ▸ h1
  · intro h
    have h1 := sq_mul h v.2
    have he : ((u : ZMod p) / (v : ZMod p) - 1) * (v : ZMod p) =
        (u : ZMod p) - (v : ZMod p) := by field_simp
    change IsNonzeroSq _
    exact he ▸ h1

private lemma coordinates (hp2 : p ≠ 2) :
    ∃ e : ZMod ((p - 1) / 2) ≃ PaleyLocV p,
      (e 0 : ZMod p) = 1 ∧
      (∀ a b, (e (a - b) : ZMod p) = (e a : ZMod p) / (e b : ZMod p)) ∧
      (∀ a b, paleyLocAdj p (e a) (e b) ↔ IsNonzeroSq ((e (a - b) : ZMod p) - 1)) ∧
      (∀ a b, (e a ≠ e b ∧ ¬ paleyLocAdj p (e a) (e b)) ↔
        a - b ≠ 0 ∧ ¬ IsNonzeroSq ((e (a - b) : ZMod p) - 1)) := by
  let inclusion : PaleyLocV p →* ZMod p :=
    { toFun := Subtype.val, map_one' := rfl, map_mul' := fun _ _ => rfl }
  have : IsCyclic (PaleyLocV p) :=
    isCyclic_of_injective_ringHom inclusion Subtype.val_injective
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := PaleyLocV p)
  let c := zmodMulEquivOfGenerator hg (card_vertices hp2)
  let e : ZMod ((p - 1) / 2) ≃ PaleyLocV p := Multiplicative.ofAdd.trans c.toEquiv
  have he0 : (e 0 : ZMod p) = 1 := by
    change (c 1 : ZMod p) = 1
    rw [c.map_one]
    rfl
  have hesub (a b : ZMod ((p - 1) / 2)) :
      (e (a - b) : ZMod p) = (e a : ZMod p) / (e b : ZMod p) := by
    change (c (Multiplicative.ofAdd a / Multiplicative.ofAdd b) : ZMod p) = _
    rw [c.map_div]
    rfl
  have hadj (a b : ZMod ((p - 1) / 2)) :
      paleyLocAdj p (e a) (e b) ↔ IsNonzeroSq ((e (a - b) : ZMod p) - 1) := by
    rw [hesub]
    exact adj_ratio _ _
  refine ⟨e, he0, hesub, hadj, ?_⟩
  intro a b
  rw [hadj, e.injective.ne_iff, sub_ne_zero]

/-- The nonzero-square vertices have exact cyclic coordinates and ratio masks.
This is finite coordinate glue; it asserts no theta bound or asymptotic estimate. -/
theorem proof (p : ℕ) (hp : Nat.Prime p) (hp4 : p % 4 = 1) :
    letI : Fact (Nat.Prime p) := ⟨hp⟩
    letI : NeZero p := NeZero.of_pos hp.pos
    0 < (p - 1) / 2 ∧
    ∃ e : ZMod ((p - 1) / 2) ≃ PaleyLocV p,
      (e 0 : ZMod p) = 1 ∧
      (∀ a b, (e (a - b) : ZMod p) = (e a : ZMod p) / (e b : ZMod p)) ∧
      (∀ a b, paleyLocAdj p (e a) (e b) ↔ IsNonzeroSq ((e (a - b) : ZMod p) - 1)) ∧
      (∀ a b, (e a ≠ e b ∧ ¬ paleyLocAdj p (e a) (e b)) ↔
        a - b ≠ 0 ∧ ¬ IsNonzeroSq ((e (a - b) : ZMod p) - 1)) := by
  have : Fact (Nat.Prime p) := ⟨hp⟩
  have : NeZero p := NeZero.of_pos hp.pos
  have hp2 : p ≠ 2 := by omega
  have hpgt : 1 < p := hp.one_lt
  exact ⟨by omega, coordinates hp2⟩


end Coordinates

namespace Averaging

variable {n : ℕ} [NeZero n]

noncomputable def cyclicKernel (X : Matrix (ZMod n) (ZMod n) ℝ) (t : ZMod n) : ℝ :=
  ∑ w : ZMod n, X (t + w) w

lemma circulant_cyclicKernel (X : Matrix (ZMod n) (ZMod n) ℝ) :
    Matrix.circulant (cyclicKernel X) =
      ∑ w : ZMod n, X.submatrix (fun u => u + w) (fun u => u + w) := by
  classical
  ext u v
  simp only [Matrix.circulant_apply, cyclicKernel, Matrix.sum_apply,
    Matrix.submatrix_apply]
  exact (Fintype.sum_equiv (Equiv.addLeft v)
    (fun w => X (u + w) (v + w))
    (fun z => X ((u - v) + z) z)
    (fun w => by
      change X (u + w) (v + w) = X ((u - v) + (v + w)) (v + w)
      rw [← add_assoc, sub_add_cancel])).symm

lemma cyclicKernel_zero (X : Matrix (ZMod n) (ZMod n) ℝ) :
    cyclicKernel X 0 = X.trace := by
  simp [cyclicKernel, Matrix.trace, Matrix.diag_apply]

lemma sum_cyclicKernel (X : Matrix (ZMod n) (ZMod n) ℝ) :
    (∑ t : ZMod n, cyclicKernel X t) = ∑ u : ZMod n, ∑ v : ZMod n, X u v := by
  classical
  calc
    (∑ t : ZMod n, cyclicKernel X t) =
        ∑ w : ZMod n, ∑ t : ZMod n, X (t + w) w := by
      simp only [cyclicKernel]
      rw [Finset.sum_comm]
    _ = ∑ w : ZMod n, ∑ u : ZMod n, X u w := by
      apply Finset.sum_congr rfl
      intro w _
      exact Fintype.sum_equiv (Equiv.addRight w) _ _ (fun t => rfl)
    _ = ∑ u : ZMod n, ∑ v : ZMod n, X u v := Finset.sum_comm

/-- Direct input to finite Bochner extraction. D is the allowed off-diagonal mask. -/
theorem kernel_reduction (X : Matrix (ZMod n) (ZMod n) ℝ) (D : ZMod n → Prop)
    (hX : X.PosSemidef) (htr : X.trace = 1)
    (hzero : ∀ u v : ZMod n, u ≠ v → ¬ D (u - v) → X u v = 0) :
    cyclicKernel X 0 = 1 ∧
      (Matrix.circulant (cyclicKernel X)).PosSemidef ∧
      (∀ t : ZMod n, t ≠ 0 → ¬ D t → cyclicKernel X t = 0) ∧
      (∑ t : ZMod n, cyclicKernel X t) = ∑ u : ZMod n, ∑ v : ZMod n, X u v := by
  classical
  refine ⟨(cyclicKernel_zero X).trans htr, ?_, ?_, sum_cyclicKernel X⟩
  · rw [circulant_cyclicKernel]
    exact Matrix.posSemidef_sum _ (fun w _ => hX.submatrix (fun u => u + w))
  · intro t ht hDt
    apply Finset.sum_eq_zero
    intro w _
    apply hzero (t + w) w
    · intro h
      apply ht
      simpa using congrArg (fun z : ZMod n => z - w) h
    · simpa using hDt


end Averaging

namespace Bochner

variable {n : ℕ} [NeZero n]

private lemma character_sum (t : ZMod n) :
    ∑ j : ZMod n, ZMod.stdAddChar (t * j) = if t = 0 then (n : ℂ) else 0 := by
  split_ifs with h
  · simp [h, ZMod.card]
  · exact sum_eq_zero_of_ne_one (ZMod.isPrimitive_stdAddChar n h)

omit [NeZero n] in
private lemma even_of_psd {f : ZMod n → ℝ} (hf : (Matrix.circulant f).PosSemidef) :
    ∀ t, f (-t) = f t := by
  exact Matrix.circulant_isSymm_iff.mp (Matrix.isHermitian_iff_isSymm.mp hf.1)

private noncomputable def coefficient (f : ZMod n → ℝ) (j : ZMod n) : ℝ :=
  ∑ t, f t * (ZMod.stdAddChar (t * j)).re

private lemma coefficient_complex {f : ZMod n → ℝ} (he : ∀ t, f (-t) = f t)
    (j : ZMod n) :
    (coefficient f j : ℂ) = ∑ t, (f t : ℂ) * ZMod.stdAddChar (-(t * j)) := by
  have him : ∑ t : ZMod n, f t * (ZMod.stdAddChar (t * j)).im = 0 := by
    have h := Fintype.sum_equiv (Equiv.neg (ZMod n))
      (fun t => f t * (ZMod.stdAddChar (t * j)).im)
      (fun t => -(f t * (ZMod.stdAddChar (t * j)).im))
      (fun t => by simp [he, neg_mul, AddChar.map_neg_eq_conj])
    simp only [sum_neg_distrib] at h
    linarith
  apply Complex.ext
  · simp [coefficient, AddChar.map_neg_eq_conj]
  · simpa [AddChar.map_neg_eq_conj] using him

private lemma coefficient_nonneg {f : ZMod n → ℝ}
    (hf : (Matrix.circulant f).PosSemidef) (j : ZMod n) : 0 ≤ coefficient f j := by
  let r : ZMod n → ℝ := fun t => (ZMod.stdAddChar (t * j)).re
  let s : ZMod n → ℝ := fun t => (ZMod.stdAddChar (t * j)).im
  have hr := hf.dotProduct_mulVec_nonneg r
  have hs := hf.dotProduct_mulVec_nonneg s
  have hchar (u v : ZMod n) :
      r u * r v + s u * s v = (ZMod.stdAddChar ((u-v)*j)).re := by
    rw [sub_mul, sub_eq_add_neg, AddChar.map_add_eq_mul, AddChar.map_neg_eq_conj]
    simp [r, s, Complex.mul_re]
  have hquad : star r ⬝ᵥ (Matrix.circulant f *ᵥ r) +
      star s ⬝ᵥ (Matrix.circulant f *ᵥ s) = (n : ℝ) * coefficient f j := by
    simp only [dotProduct, Matrix.mulVec, Matrix.circulant_apply, Pi.star_apply,
      star_trivial, mul_sum, ← sum_add_distrib]
    calc
      _ = ∑ u : ZMod n, ∑ v : ZMod n,
          f (u-v) * (ZMod.stdAddChar ((u-v)*j)).re := by
        apply sum_congr rfl
        intro u _
        apply sum_congr rfl
        intro v _
        rw [← hchar]
        ring
      _ = ∑ v : ZMod n, coefficient f j := by
        rw [sum_comm]
        apply sum_congr rfl
        intro v _
        exact Fintype.sum_equiv (Equiv.subRight v) _ _ (fun u => rfl)
      _ = (n : ℝ) * coefficient f j := by simp [ZMod.card]
  have hn : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne n))
  exact (mul_nonneg_iff_of_pos_left hn).mp (hquad ▸ add_nonneg hr hs)

private lemma coefficient_inversion {f : ZMod n → ℝ} (he : ∀ t, f (-t) = f t)
    (t : ZMod n) :
    ∑ j : ZMod n, (coefficient f j : ℂ) * ZMod.stdAddChar (j*t) =
      (n : ℂ) * (f t : ℂ) := by
  simp only [coefficient_complex he, sum_mul]
  rw [sum_comm]
  calc
    _ = ∑ u : ZMod n, (f u : ℂ) * ∑ j : ZMod n,
        ZMod.stdAddChar ((t-u)*j) := by
      apply sum_congr rfl
      intro u _
      rw [mul_sum]
      apply sum_congr rfl
      intro j _
      rw [mul_assoc, ← AddChar.map_add_eq_mul]
      congr 2
      ring
    _ = (n : ℂ) * (f t : ℂ) := by
      simp only [character_sum]
      simp [sub_eq_zero, mul_comm]

/-- A normalized real PSD circulant is a probability mixture of the standard
characters. Its sum is the group order times the trivial-character mass. -/
theorem proof {f : ZMod n → ℝ}
    (hf : (Matrix.circulant f).PosSemidef) (hzero : f 0 = 1) :
    ∃ μ : ZMod n → ℝ,
      (∀ j, 0 ≤ μ j) ∧
      (∑ j, μ j) = 1 ∧
      (∀ t, (f t : ℂ) = ∑ j, (μ j : ℂ) * ZMod.stdAddChar (j*t)) ∧
      (∑ t, f t) = (n : ℝ) * μ 0 := by
  let μ : ZMod n → ℝ := fun j => coefficient f j / (n : ℝ)
  have hn : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
  have hnc : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
  have hinv (t : ZMod n) :
      (f t : ℂ) = ∑ j, (μ j : ℂ) * ZMod.stdAddChar (j*t) := by
    simp only [μ, div_eq_mul_inv, Complex.ofReal_mul, Complex.ofReal_inv,
      Complex.ofReal_natCast]
    calc
      _ = (n : ℂ)⁻¹ * ((n : ℂ) * (f t : ℂ)) := by
        rw [← mul_assoc, inv_mul_cancel₀ hnc, one_mul]
      _ = (n : ℂ)⁻¹ * ∑ j, (coefficient f j : ℂ) * ZMod.stdAddChar (j*t) := by
        rw [coefficient_inversion (even_of_psd hf)]
      _ = _ := by
        rw [mul_sum]
        apply sum_congr rfl
        intro j _
        ring
  refine ⟨μ, fun j => div_nonneg (coefficient_nonneg hf j) (Nat.cast_nonneg n), ?_,
    hinv, ?_⟩
  · have h := congrArg Complex.re (hinv 0)
    simpa [hzero] using h.symm
  · simp only [μ, coefficient, mul_zero, AddChar.map_zero_eq_one, Complex.one_re,
      mul_one]
    exact (mul_div_cancel₀ _ hn).symm


end Bochner

private lemma nonzeroSq_neg_iff {p : ℕ}
    (hminus : IsSquare (-1 : ZMod p)) (y : ZMod p) :
    IsNonzeroSq (-y) ↔ IsNonzeroSq y := by
  have neg_sq {z : ZMod p} (hz : IsNonzeroSq z) : IsNonzeroSq (-z) := by
    refine ⟨neg_ne_zero.mpr hz.1, ?_⟩
    change IsSquare (-z)
    simpa only [neg_one_mul] using hminus.mul hz.2
  constructor
  · intro hy
    simpa only [neg_neg] using neg_sq hy
  · exact neg_sq

private lemma nonzeroSq_sub_one_iff {p : ℕ}
    (hp : Nat.Prime p) (hp4 : p % 4 = 1) (x : ZMod p) :
    IsNonzeroSq (x - 1) ↔ IsNonzeroSq (1 - x) := by
  letI : Fact (Nat.Prime p) := ⟨hp⟩
  have hminus : IsSquare (-1 : ZMod p) :=
    (ZMod.exists_sq_eq_neg_one_iff (p := p)).2 (by simp [hp4])
  simpa only [neg_sub] using (nonzeroSq_neg_iff hminus (x - 1)).symm

/-- Every theta-feasible matrix on either graph side yields a probability
measure with the exact opposite-mask zeros and the same normalized objective.
The coordinates are independent of the graph side and of the matrix. -/
theorem proof (p : ℕ) (hp : Nat.Prime p) (hp4 : p % 4 = 1) :
    letI : Fact (Nat.Prime p) := ⟨hp⟩
    letI : NeZero p := NeZero.of_pos hp.pos
    ∃ hn : 0 < (p - 1) / 2,
    letI : NeZero ((p - 1) / 2) := NeZero.of_pos hn
    ∃ e : ZMod ((p - 1) / 2) ≃ PaleyLocV p,
      (e 0 : ZMod p) = 1 ∧
      (∀ a b, (e (a - b) : ZMod p) = (e a : ZMod p) / (e b : ZMod p)) ∧
      ∀ (side : Bool) (X : Matrix (PaleyLocV p) (PaleyLocV p) ℝ),
        X.PosSemidef → X.trace = 1 →
        (∀ u v, u ≠ v →
          ¬ (if side then (u ≠ v ∧ ¬ paleyLocAdj p u v) else paleyLocAdj p u v) →
          X u v = 0) →
        ∃ μ : ZMod ((p - 1) / 2) → ℝ,
          (∀ j, 0 ≤ μ j) ∧ (∑ j, μ j) = 1 ∧
          (∀ t, t ≠ 0 →
            ¬ (if side then ¬ IsNonzeroSq (1 - (e t : ZMod p))
                else IsNonzeroSq (1 - (e t : ZMod p))) →
            (∑ j, (μ j : ℂ) * ZMod.stdAddChar (j*t)) = 0) ∧
          (∑ u, ∑ v, X u v) = (((p - 1) / 2 : ℕ) : ℝ) * μ 0 := by
  classical
  letI : Fact (Nat.Prime p) := ⟨hp⟩
  letI : NeZero p := NeZero.of_pos hp.pos
  obtain ⟨hn, e, he0, hesub, hadj, _⟩ := Coordinates.proof p hp hp4
  refine ⟨hn, ?_⟩
  letI : NeZero ((p - 1) / 2) := NeZero.of_pos hn
  refine ⟨e, he0, hesub, ?_⟩
  intro side X hX htr hzero
  let Y := X.submatrix e e
  let D : ZMod ((p - 1) / 2) → Prop := fun t =>
    if side then ¬ IsNonzeroSq (1 - (e t : ZMod p))
    else IsNonzeroSq (1 - (e t : ZMod p))
  have hmask (a b : ZMod ((p - 1) / 2)) :
      paleyLocAdj p (e a) (e b) ↔ IsNonzeroSq (1 - (e (a-b) : ZMod p)) :=
    (hadj a b).trans (nonzeroSq_sub_one_iff hp hp4 _)
  have hYtr : Y.trace = 1 := by
    have h : Y.trace = X.trace := Fintype.sum_equiv e _ _ (fun a => rfl)
    exact h.trans htr
  have hYsum : (∑ a, ∑ b, Y a b) = ∑ u, ∑ v, X u v := by
    apply Fintype.sum_equiv e
    intro a
    exact Fintype.sum_equiv e _ _ (fun b => rfl)
  have hYzero (a b : ZMod ((p - 1) / 2)) (hab : a ≠ b)
      (hD : ¬ D (a-b)) : Y a b = 0 := by
    apply hzero (e a) (e b) (e.injective.ne hab)
    intro hedge
    apply hD
    cases side <;> simpa [D, hmask, e.injective.ne hab] using hedge
  obtain ⟨hf0, hfPSD, hfzero, hfsum⟩ :=
    Averaging.kernel_reduction Y D (hX.submatrix e) hYtr hYzero
  obtain ⟨μ, hμ, hμsum, hμinv, hμmass⟩ := Bochner.proof hfPSD hf0
  refine ⟨μ, hμ, hμsum, ?_, ?_⟩
  · intro t ht hDt
    rw [← hμinv t, hfzero t ht hDt]
    rfl
  · exact hYsum.symm.trans (hfsum.symm.trans hμmass)

end Submissions.PaleyLocFourierBridge.Bridge
