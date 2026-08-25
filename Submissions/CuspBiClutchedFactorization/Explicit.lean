import Mathlib

namespace Submissions.CuspBiClutchedFactorization.Explicit

open Polynomial
open scoped BigOperators

noncomputable def clutch (k : ℕ) (tau z : ℂ) : Fin k → ℂ := fun q =>
  if q.val = 0 then 1 + tau * z ^ k else z ^ q.val

lemma polynomial_eq_folded {k : ℕ} (hk : 1 ≤ k) (tau : ℂ) (P : ℂ[X])
    (hdeg : P.natDegree ≤ k) (htop : P.coeff k = tau * P.coeff 0) :
    P = Polynomial.ofFn k (fun q => P.coeff q.val) +
      Polynomial.C (tau * P.coeff 0) * Polynomial.X ^ k := by
  ext m
  by_cases hm : m < k
  · rw [Polynomial.coeff_add, Polynomial.ofFn_coeff_eq_val_of_lt _ hm,
      Polynomial.coeff_C_mul_X_pow]
    simp [Nat.ne_of_lt hm]
  · have hkm : k ≤ m := Nat.le_of_not_gt hm
    rw [Polynomial.coeff_add, Polynomial.ofFn_coeff_eq_zero_of_ge _ hkm,
      zero_add, Polynomial.coeff_C_mul_X_pow]
    by_cases hmk : m = k
    · subst m
      simp [htop]
    · have hzero : P.coeff m = 0 := by
        apply Polynomial.coeff_eq_zero_of_natDegree_lt
        omega
      simp [hmk, hzero]

lemma eval_eq_clutch_sum {k : ℕ} (hk : 1 ≤ k) (tau z : ℂ) (P : ℂ[X])
    (hdeg : P.natDegree ≤ k) (htop : P.coeff k = tau * P.coeff 0) :
    P.eval z = ∑ q : Fin k, P.coeff q.val * clutch k tau z q := by
  have hP := polynomial_eq_folded hk tau P hdeg htop
  conv_lhs => rw [hP]
  rw [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_pow, Polynomial.eval_X, Polynomial.ofFn_eq_sum_monomial,
    Polynomial.eval_finsetSum]
  simp only [Polynomial.eval_monomial, clutch]
  let q0 : Fin k := ⟨0, hk⟩
  have hsplit (f : Fin k → ℂ) :
      ∑ q, f q = f q0 + ∑ q ∈ Finset.univ.erase q0, f q := by
    exact (Finset.add_sum_erase Finset.univ f (Finset.mem_univ q0)).symm
  rw [hsplit (fun q => P.coeff q.val * z ^ q.val),
    hsplit (fun q => P.coeff q.val *
      (if q.val = 0 then 1 + tau * z ^ k else z ^ q.val))]
  simp only [q0, pow_zero, mul_one, if_pos]
  have hrest :
      ∑ q ∈ Finset.univ.erase q0, P.coeff q.val * z ^ q.val =
        ∑ q ∈ Finset.univ.erase q0,
          P.coeff q.val *
            (if q.val = 0 then 1 + tau * z ^ k else z ^ q.val) := by
    apply Finset.sum_congr rfl
    intro q hq
    have hq0 : q ≠ q0 := by simpa using hq
    have hqv : q.val ≠ 0 := fun h => hq0 (Fin.ext (by simpa [q0] using h))
    simp [hqv]
  rw [← hrest]
  ring

def cOffset {r N : ℕ} (c : Fin r) : ZMod (2 * N) := (2 * c.val : ℕ)

def dOffset {r N : ℕ} (d : Fin r) : ZMod (2 * N) :=
  (2 * d.val + 1 + if d.val + 1 = r then 2 else 0 : ℕ)

noncomputable def cuspProduct {r N : ℕ} (h : NeZero (2 * N))
    (i j : ZMod (2 * N)) : ℂ := by
  letI := h
  exact
    (∏ c : Fin r,
        (ZMod.stdAddChar j - ZMod.stdAddChar (i + cOffset c))) *
      (∏ d : Fin r,
        (ZMod.stdAddChar j - ZMod.stdAddChar (-i + dOffset d)))

noncomputable def directPoly {r N : ℕ} [NeZero (2 * N)]
    (j : ZMod (2 * N)) (c : Fin r) : ℂ[X] :=
  C (ZMod.stdAddChar j) -
    C (ZMod.stdAddChar (cOffset (r := r) (N := N) c)) * X

noncomputable def antiPoly {r N : ℕ} [NeZero (2 * N)]
    (j : ZMod (2 * N)) (d : Fin r) : ℂ[X] :=
  C (ZMod.stdAddChar j) * X -
    C (ZMod.stdAddChar (dOffset (r := r) (N := N) d))

noncomputable def cuspPoly {r N : ℕ} [NeZero (2 * N)]
    (j : ZMod (2 * N)) : ℂ[X] :=
  (∏ c : Fin r, directPoly (r := r) (N := N) j c) *
    (∏ d : Fin r, antiPoly (r := r) (N := N) j d)

lemma anti_eval {r N : ℕ} [NeZero (2 * N)]
    (i j : ZMod (2 * N)) (d : Fin r) :
    (antiPoly j d).eval (ZMod.stdAddChar i) =
      ZMod.stdAddChar i *
        (ZMod.stdAddChar j - ZMod.stdAddChar (-i + dOffset d)) := by
  simp only [antiPoly, eval_sub, eval_mul, eval_C, eval_X]
  rw [AddChar.map_add_eq_mul, AddChar.map_neg_eq_inv]
  have hi : ZMod.stdAddChar i ≠ 0 := by simp [ZMod.stdAddChar_apply]
  field_simp

lemma direct_eval {r N : ℕ} [NeZero (2 * N)]
    (i j : ZMod (2 * N)) (c : Fin r) :
    (directPoly j c).eval (ZMod.stdAddChar i) =
      ZMod.stdAddChar j - ZMod.stdAddChar (i + cOffset c) := by
  simp [directPoly, AddChar.map_add_eq_mul]
  ring

lemma cuspPoly_eval {r N : ℕ} (h : NeZero (2 * N))
    (i j : ZMod (2 * N)) :
    (cuspPoly (r := r) j).eval (ZMod.stdAddChar i) =
      ZMod.stdAddChar i ^ r * cuspProduct (r := r) h i j := by
  letI := h
  simp only [cuspPoly, eval_mul, eval_prod, direct_eval, anti_eval, cuspProduct]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  ring

lemma char_ne_zero {N : ℕ} [NeZero N] (i : ZMod N) :
    ZMod.stdAddChar i ≠ 0 := by
  simp [ZMod.stdAddChar_apply]

lemma direct_natDegree {r N : ℕ} [NeZero (2 * N)]
    (j : ZMod (2 * N)) (c : Fin r) : (directPoly j c).natDegree = 1 := by
  have hc : ZMod.stdAddChar (cOffset (r := r) (N := N) c) ≠ 0 :=
    char_ne_zero _
  have hterm :
      (C (ZMod.stdAddChar (cOffset (r := r) (N := N) c)) * X).natDegree = 1 := by
    rw [natDegree_mul]
    · simp
    · exact C_ne_zero.mpr hc
    · exact (X_ne_zero : (X : ℂ[X]) ≠ 0)
  apply natDegree_eq_of_le_of_coeff_ne_zero
  · exact (natDegree_sub_le _ _).trans (by simp [directPoly, hterm])
  · simp [directPoly, char_ne_zero]

lemma anti_natDegree {r N : ℕ} [NeZero (2 * N)]
    (j : ZMod (2 * N)) (d : Fin r) : (antiPoly j d).natDegree = 1 := by
  simp [antiPoly, char_ne_zero]

lemma direct_leadingCoeff {r N : ℕ} [NeZero (2 * N)]
    (j : ZMod (2 * N)) (c : Fin r) :
    (directPoly j c).leadingCoeff =
      -ZMod.stdAddChar (cOffset (r := r) (N := N) c) := by
  rw [← coeff_natDegree, direct_natDegree]
  simp [directPoly]

lemma anti_leadingCoeff {r N : ℕ} [NeZero (2 * N)]
    (j : ZMod (2 * N)) (d : Fin r) :
    (antiPoly j d).leadingCoeff = ZMod.stdAddChar j := by
  rw [← coeff_natDegree, anti_natDegree]
  simp [antiPoly]

lemma cuspPoly_natDegree {r N : ℕ} [NeZero (2 * N)]
    (j : ZMod (2 * N)) : (cuspPoly (r := r) j).natDegree = 2 * r := by
  have hc (c : Fin r) : directPoly j c ≠ 0 := by
    intro hz
    have hdeg := direct_natDegree j c
    simp [hz] at hdeg
  have hd (d : Fin r) : antiPoly j d ≠ 0 := by
    intro hz
    have hdeg := anti_natDegree j d
    simp [hz] at hdeg
  have hcprod : (∏ c : Fin r, directPoly j c) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun c _ => hc c)
  have hdprod : (∏ d : Fin r, antiPoly j d) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun d _ => hd d)
  simp only [cuspPoly]
  rw [natDegree_mul hcprod hdprod,
    Polynomial.natDegree_prod (s := Finset.univ)
      (f := fun c : Fin r => directPoly j c) (fun c _ => hc c),
    Polynomial.natDegree_prod (s := Finset.univ)
      (f := fun d : Fin r => antiPoly j d) (fun d _ => hd d)]
  simp [direct_natDegree, anti_natDegree]
  omega

noncomputable def cLead (r N : ℕ) [NeZero (2 * N)] : ℂ :=
  ∏ c : Fin r, -ZMod.stdAddChar (cOffset (N := N) c)

noncomputable def dConst (r N : ℕ) [NeZero (2 * N)] : ℂ :=
  ∏ d : Fin r, -ZMod.stdAddChar (dOffset (N := N) d)

noncomputable def tauZ (r N : ℕ) [NeZero (2 * N)] : ℂ :=
  cLead r N / dConst r N

lemma cLead_ne_zero (r N : ℕ) [NeZero (2 * N)] : cLead r N ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro c hc
  simp [char_ne_zero]

lemma dConst_ne_zero (r N : ℕ) [NeZero (2 * N)] : dConst r N ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro d hd
  simp [char_ne_zero]

lemma cuspPoly_coeff_zero {r N : ℕ} [NeZero (2 * N)]
    (j : ZMod (2 * N)) :
    (cuspPoly (r := r) j).coeff 0 = ZMod.stdAddChar j ^ r * dConst r N := by
  rw [coeff_zero_eq_eval_zero]
  simp only [cuspPoly, eval_mul, eval_prod, directPoly, antiPoly,
    eval_sub, eval_C, eval_mul, eval_X, mul_zero, sub_zero, zero_mul, zero_sub]
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rfl

lemma cuspPoly_coeff_top {r N : ℕ} [NeZero (2 * N)]
    (j : ZMod (2 * N)) :
    (cuspPoly (r := r) j).coeff (2 * r) = cLead r N * ZMod.stdAddChar j ^ r := by
  rw [← cuspPoly_natDegree j, coeff_natDegree]
  simp only [cuspPoly, leadingCoeff_mul, Polynomial.leadingCoeff_prod,
    direct_leadingCoeff, anti_leadingCoeff, cLead]
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

lemma cuspPoly_boundary {r N : ℕ} [NeZero (2 * N)]
    (j : ZMod (2 * N)) :
    (cuspPoly (r := r) j).coeff (2 * r) =
      tauZ r N * (cuspPoly (r := r) j).coeff 0 := by
  rw [cuspPoly_coeff_top, cuspPoly_coeff_zero]
  unfold tauZ
  field_simp [dConst_ne_zero]

theorem cusp_left_clutch {r N : ℕ} (hr : 1 ≤ r) (h : NeZero (2 * N))
    (i j : ZMod (2 * N)) :
    ZMod.stdAddChar i ^ r * cuspProduct (r := r) h i j =
      ∑ q : Fin (2 * r),
        (cuspPoly (r := r) j).coeff q.val *
          clutch (2 * r) (tauZ r N)
            (ZMod.stdAddChar i) q := by
  letI := h
  rw [← cuspPoly_eval h i j]
  apply eval_eq_clutch_sum
  · omega
  · rw [cuspPoly_natDegree]
  · exact cuspPoly_boundary j

noncomputable def rightDirect {r N : ℕ} [NeZero (2 * N)]
    (i : ZMod (2 * N)) (c : Fin r) : ℂ[X] :=
  X - C (ZMod.stdAddChar (cOffset (r := r) (N := N) c) * ZMod.stdAddChar i)

noncomputable def rightAnti {r N : ℕ} [NeZero (2 * N)]
    (i : ZMod (2 * N)) (d : Fin r) : ℂ[X] :=
  C (ZMod.stdAddChar i) * X -
    C (ZMod.stdAddChar (dOffset (r := r) (N := N) d))

noncomputable def rightPoly {r N : ℕ} [NeZero (2 * N)]
    (i : ZMod (2 * N)) : ℂ[X] :=
  (∏ c : Fin r, rightDirect (r := r) (N := N) i c) *
    (∏ d : Fin r, rightAnti (r := r) (N := N) i d)

lemma rightDirect_eval {r N : ℕ} [NeZero (2 * N)]
    (i j : ZMod (2 * N)) (c : Fin r) :
    (rightDirect i c).eval (ZMod.stdAddChar j) =
      ZMod.stdAddChar j - ZMod.stdAddChar (i + cOffset c) := by
  simp [rightDirect, AddChar.map_add_eq_mul]
  ring

lemma rightAnti_eval {r N : ℕ} [NeZero (2 * N)]
    (i j : ZMod (2 * N)) (d : Fin r) :
    (rightAnti i d).eval (ZMod.stdAddChar j) =
      ZMod.stdAddChar i *
        (ZMod.stdAddChar j - ZMod.stdAddChar (-i + dOffset d)) := by
  simp only [rightAnti, eval_sub, eval_mul, eval_C, eval_X]
  rw [AddChar.map_add_eq_mul, AddChar.map_neg_eq_inv]
  have hi : ZMod.stdAddChar i ≠ 0 := char_ne_zero i
  field_simp

lemma rightPoly_eval {r N : ℕ} (h : NeZero (2 * N))
    (i j : ZMod (2 * N)) :
    (rightPoly (r := r) i).eval (ZMod.stdAddChar j) =
      ZMod.stdAddChar i ^ r * cuspProduct (r := r) h i j := by
  letI := h
  simp only [rightPoly, eval_mul, eval_prod, rightDirect_eval, rightAnti_eval,
    cuspProduct]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  ring

lemma rightDirect_natDegree {r N : ℕ} [NeZero (2 * N)]
    (i : ZMod (2 * N)) (c : Fin r) : (rightDirect i c).natDegree = 1 := by
  simpa only [rightDirect] using
    (natDegree_X_sub_C
      (ZMod.stdAddChar (cOffset (r := r) (N := N) c) * ZMod.stdAddChar i))

lemma rightAnti_natDegree {r N : ℕ} [NeZero (2 * N)]
    (i : ZMod (2 * N)) (d : Fin r) : (rightAnti i d).natDegree = 1 := by
  simp [rightAnti, char_ne_zero]

lemma rightPoly_natDegree {r N : ℕ} [NeZero (2 * N)]
    (i : ZMod (2 * N)) : (rightPoly (r := r) i).natDegree = 2 * r := by
  have hc (c : Fin r) : rightDirect i c ≠ 0 := by
    intro hz
    have hdeg := rightDirect_natDegree i c
    simp [hz] at hdeg
  have hd (d : Fin r) : rightAnti i d ≠ 0 := by
    intro hz
    have hdeg := rightAnti_natDegree i d
    simp [hz] at hdeg
  have hcprod : (∏ c : Fin r, rightDirect i c) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun c _ => hc c)
  have hdprod : (∏ d : Fin r, rightAnti i d) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun d _ => hd d)
  simp only [rightPoly]
  rw [natDegree_mul hcprod hdprod,
    Polynomial.natDegree_prod (s := Finset.univ)
      (f := fun c : Fin r => rightDirect i c) (fun c _ => hc c),
    Polynomial.natDegree_prod (s := Finset.univ)
      (f := fun d : Fin r => rightAnti i d) (fun d _ => hd d)]
  simp [rightDirect_natDegree, rightAnti_natDegree]
  omega

noncomputable def tauX (r N : ℕ) [NeZero (2 * N)] : ℂ :=
  (cLead r N * dConst r N)⁻¹

lemma rightPoly_coeff_zero {r N : ℕ} [NeZero (2 * N)]
    (i : ZMod (2 * N)) :
    (rightPoly (r := r) i).coeff 0 =
      cLead r N * dConst r N * ZMod.stdAddChar i ^ r := by
  rw [coeff_zero_eq_eval_zero]
  simp only [rightPoly, eval_mul, eval_prod, rightDirect, rightAnti,
    eval_sub, eval_X, eval_C, zero_mul, zero_sub, mul_zero, cLead, dConst]
  simp_rw [show ∀ c : Fin r,
    -(ZMod.stdAddChar (cOffset (N := N) c) * ZMod.stdAddChar i) =
      (-ZMod.stdAddChar (cOffset (N := N) c)) * ZMod.stdAddChar i by
        intro c; ring]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  ring

lemma rightPoly_coeff_top {r N : ℕ} [NeZero (2 * N)]
    (i : ZMod (2 * N)) :
    (rightPoly (r := r) i).coeff (2 * r) = ZMod.stdAddChar i ^ r := by
  rw [← rightPoly_natDegree i, coeff_natDegree]
  simp only [rightPoly, leadingCoeff_mul, Polynomial.leadingCoeff_prod]
  have hc : ∀ c : Fin r, (rightDirect i c).leadingCoeff = 1 := by
    intro c
    rw [← coeff_natDegree, rightDirect_natDegree]
    simp [rightDirect]
  have hd : ∀ d : Fin r, (rightAnti i d).leadingCoeff = ZMod.stdAddChar i := by
    intro d
    rw [← coeff_natDegree, rightAnti_natDegree]
    simp [rightAnti]
  simp_rw [hc, hd]
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  simp

lemma rightPoly_boundary {r N : ℕ} [NeZero (2 * N)]
    (i : ZMod (2 * N)) :
    (rightPoly (r := r) i).coeff (2 * r) =
      tauX r N * (rightPoly (r := r) i).coeff 0 := by
  rw [rightPoly_coeff_top, rightPoly_coeff_zero]
  unfold tauX
  field_simp [cLead_ne_zero r N, dConst_ne_zero r N]

theorem cusp_right_clutch {r N : ℕ} (hr : 1 ≤ r) (h : NeZero (2 * N))
    (i j : ZMod (2 * N)) :
    ZMod.stdAddChar i ^ r * cuspProduct (r := r) h i j =
      ∑ q : Fin (2 * r),
        (rightPoly (r := r) i).coeff q.val *
          clutch (2 * r) (tauX r N)
            (ZMod.stdAddChar j) q := by
  letI := h
  rw [← rightPoly_eval h i j]
  apply eval_eq_clutch_sum
  · omega
  · rw [rightPoly_natDegree]
  · exact rightPoly_boundary i

theorem proof :
    ∀ (r N : ℕ), 1 ≤ r → ∀ h : NeZero (2 * N),
      ∃ (tauL tauR : ℂ)
        (L R : ZMod (2 * N) → Fin (2 * r) → ℂ),
        tauL ≠ 0 ∧ tauR ≠ 0 ∧
        ∀ i j : ZMod (2 * N),
          (ZMod.stdAddChar i ^ r * cuspProduct (r := r) h i j =
            ∑ q, L j q * clutch (2 * r) tauL (ZMod.stdAddChar i) q) ∧
          (ZMod.stdAddChar i ^ r * cuspProduct (r := r) h i j =
            ∑ q, R i q * clutch (2 * r) tauR (ZMod.stdAddChar j) q) := by
  intro r N hr h
  letI := h
  refine ⟨tauZ r N, tauX r N,
    fun j q => (cuspPoly (r := r) j).coeff q.val,
    fun i q => (rightPoly (r := r) i).coeff q.val, ?_, ?_, ?_⟩
  · exact div_ne_zero (cLead_ne_zero r N) (dConst_ne_zero r N)
  · exact inv_ne_zero (mul_ne_zero (cLead_ne_zero r N) (dConst_ne_zero r N))
  · intro i j
    exact ⟨cusp_left_clutch hr h i j, cusp_right_clutch hr h i j⟩

end Submissions.CuspBiClutchedFactorization.Explicit
