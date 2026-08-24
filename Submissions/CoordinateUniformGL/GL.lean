import Mathlib

namespace Submissions.CoordinateUniformGL.GL

open Matrix MvPolynomial

variable {k : ℕ}

noncomputable section

abbrev CoordinateUniform {n : ℕ} (w : Fin n → Fin k → ℂ) : Prop :=
  ∀ (t : ℕ) (b : Fin t → Fin n) (e : Fin t → Fin k),
    Function.Injective b → Function.Injective e →
    LinearIndependent ℂ (fun p => w (b p)) →
    Matrix.det (Matrix.of fun p q => w (b p) (e q)) ≠ 0

abbrev applyMat (U : Matrix (Fin k) (Fin k) ℂ) (x : Fin k → ℂ) : Fin k → ℂ :=
  U.mulVec x

def evalU (U : Matrix (Fin k) (Fin k) ℂ) : Fin k × Fin k → ℂ :=
  fun ij => U ij.1 ij.2

def detPoly : MvPolynomial (Fin k × Fin k) ℂ :=
  (mvPolynomialX (Fin k) (Fin k) ℂ).det

/-- The `t × t` minor of `U · A` on coordinate injection `e`, as a polynomial in `U`. -/
def minorPoly {t : ℕ} (A : Fin t → Fin k → ℂ) (e : Fin t → Fin k) :
    MvPolynomial (Fin k × Fin k) ℂ :=
  (Matrix.of fun p q => ∑ c : Fin k, C (A p c) * X (e q, c)).det

lemma eval_detPoly (U : Matrix (Fin k) (Fin k) ℂ) :
    eval (evalU U) detPoly = U.det := by
  unfold detPoly
  rw [eval_det_mvPolynomialX (m := Fin k) (R := ℂ) (evalU U)]
  simp [evalU]
  have : (Matrix.of fun i j : Fin k => U i j) = U := by
    ext i j
    simp
  simp [this]

lemma eval_minorPoly {t : ℕ} (A : Fin t → Fin k → ℂ) (e : Fin t → Fin k)
    (U : Matrix (Fin k) (Fin k) ℂ) :
    eval (evalU U) (minorPoly A e) =
      (Matrix.of fun p q => (U.mulVec (A p)) (e q)).det := by
  classical
  unfold minorPoly
  rw [(eval (evalU U)).map_det]
  congr 1
  ext p q
  simp [evalU, mulVec, dotProduct, map_sum, map_mul, eval_C, eval_X]
  refine Finset.sum_congr rfl fun _ _ => mul_comm _ _

lemma detPoly_ne_zero : detPoly (k := k) ≠ 0 :=
  det_mvPolynomialX_ne_zero (Fin k) ℂ

/-- Independent `t`-row family in `ℂ^k` has some nonzero `t × t` coordinate minor. -/
lemma exists_nonzero_coord_minor {t : ℕ} (A : Fin t → Fin k → ℂ)
    (hA : LinearIndependent ℂ A) :
    ∃ e : Fin t → Fin k, Function.Injective e ∧
      (Matrix.of fun p q => A p (e q)).det ≠ 0 := by
  classical
  let cols : Fin k → (Fin t → ℂ) := fun j p => A p j
  obtain ⟨κ, a, ha, hspan, hli⟩ := exists_linearIndependent' ℂ cols
  have : Finite κ := LinearIndependent.finite (R := ℂ) (M := Fin t → ℂ) hli
  let : Fintype κ := Fintype.ofFinite κ
  let M : Matrix (Fin t) (Fin k) ℂ := A
  have hfinrank_cols :
      Module.finrank ℂ (Submodule.span ℂ (Set.range cols)) = t := by
    have hA' : LinearIndependent ℂ M.row := hA
    have hr : M.rank = t := by
      simpa [Fintype.card_fin] using (LinearIndependent.rank_matrix (M := M) hA')
    have hcols : cols = M.col := by
      funext j p
      rfl
    rw [hcols, ← rank_eq_finrank_span_cols, hr]
  have hcard : Fintype.card κ = t := by
    have h := (linearIndependent_iff_card_eq_finrank_span (R := ℂ)).mp hli
    rw [Set.finrank] at h
    rw [h, hspan, hfinrank_cols]
  let e : Fin t → Fin k :=
    fun i => a ((Fintype.equivFin κ).symm (Fin.cast hcard.symm i))
  have he : Function.Injective e :=
    ha.comp <| (Fintype.equivFin κ).symm.injective.comp (Fin.cast_injective hcard.symm)
  have hli_e : LinearIndependent ℂ (fun i : Fin t => cols (e i)) :=
    hli.comp _ <| (Fintype.equivFin κ).symm.injective.comp (Fin.cast_injective hcard.symm)
  refine ⟨e, he, ?_⟩
  let B : Matrix (Fin t) (Fin t) ℂ := Matrix.of fun p q => A p (e q)
  have hcol : LinearIndependent ℂ B.col := by
    have : B.col = fun q : Fin t => cols (e q) := by
      funext q p
      rfl
    simpa [this] using hli_e
  exact (nonsingular_iff_det_ne_zero (R := ℂ)).mp
    (Nonsingular.of_linearIndependent_col hcol)

/-- A (possibly singular) matrix that copies coordinates `e0` onto slots `e`. -/
def slotMat {t : ℕ} (e e0 : Fin t → Fin k) : Matrix (Fin k) (Fin k) ℂ :=
  Matrix.of fun i j =>
    ∑ q : Fin t, if i = e q ∧ j = e0 q then (1 : ℂ) else 0

lemma slotMat_mulVec {t : ℕ} {e e0 : Fin t → Fin k} (he : Function.Injective e)
    (x : Fin k → ℂ) (q : Fin t) :
    (slotMat e e0).mulVec x (e q) = x (e0 q) := by
  classical
  have hsum :
      (slotMat e e0).mulVec x (e q) =
        ∑ j : Fin k, (∑ q' : Fin t,
          if e q = e q' ∧ j = e0 q' then (1 : ℂ) else 0) * x j := by
    simp [slotMat, mulVec, dotProduct, Matrix.of_apply]
  have hswap :
      (∑ j : Fin k, (∑ q' : Fin t,
          if e q = e q' ∧ j = e0 q' then (1 : ℂ) else 0) * x j) =
        ∑ q' : Fin t, ∑ j : Fin k,
          (if e q = e q' ∧ j = e0 q' then (1 : ℂ) else 0) * x j := by
    simp_rw [Finset.sum_mul]
    exact Finset.sum_comm
  have hinner :
      ∀ q' : Fin t,
        (∑ j : Fin k, (if e q = e q' ∧ j = e0 q' then (1 : ℂ) else 0) * x j) =
          if e q = e q' then x (e0 q') else (0 : ℂ) := by
    intro q'
    by_cases hqe : e q = e q'
    · have :
          (∑ j : Fin k, (if j = e0 q' then (1 : ℂ) else 0) * x j) = x (e0 q') := by
        simp [Finset.sum_ite_eq']
      simpa [hqe] using this
    · have :
          (∑ j : Fin k, (if e q = e q' ∧ j = e0 q' then (1 : ℂ) else 0) * x j) = 0 := by
        refine Finset.sum_eq_zero fun j _ => ?_
        simp [hqe]
      simpa [hqe] using this
  have hsingle :
      (∑ q' : Fin t, (if e q = e q' then x (e0 q') else (0 : ℂ))) = x (e0 q) := by
    simp [he.eq_iff, Finset.sum_ite_eq']
  rw [hsum, hswap]
  have hfold :
      (∑ q' : Fin t, ∑ j : Fin k,
          (if e q = e q' ∧ j = e0 q' then (1 : ℂ) else 0) * x j) =
        ∑ q' : Fin t, if e q = e q' then x (e0 q') else (0 : ℂ) :=
    Finset.sum_congr rfl fun q' _ => hinner q'
  rw [hfold, hsingle]

lemma minorPoly_ne_zero {t : ℕ} (A : Fin t → Fin k → ℂ)
    (hA : LinearIndependent ℂ A) {e : Fin t → Fin k} (he : Function.Injective e) :
    minorPoly (k := k) A e ≠ 0 := by
  obtain ⟨e0, _he0, hmin⟩ := exists_nonzero_coord_minor (k := k) A hA
  let U := slotMat (k := k) e e0
  have heval :
      eval (evalU U) (minorPoly A e) =
        (Matrix.of fun p q => A p (e0 q)).det := by
    rw [eval_minorPoly]
    congr 1
    ext p q
    simpa using slotMat_mulVec (k := k) (e := e) (e0 := e0) he (A p) q
  intro hz
  have : eval (evalU U) (minorPoly A e) = 0 := by simp [hz]
  exact hmin (heval.symm.trans this)

lemma exists_eval_ne_zero (p : MvPolynomial (Fin k × Fin k) ℂ) (hp : p ≠ 0) :
    ∃ U : Matrix (Fin k) (Fin k) ℂ, eval (evalU U) p ≠ 0 := by
  by_contra h
  push Not at h
  apply hp
  apply MvPolynomial.funext (R := ℂ)
  intro x
  let U : Matrix (Fin k) (Fin k) ℂ := Matrix.of fun i j => x (i, j)
  have hx : evalU U = x := by
    funext ij
    simp [evalU, U]
  simpa [hx] using h U

theorem proof :
    ∀ (k n : ℕ), 2 ≤ k →
      ∀ (v : Fin n → Fin k → ℂ),
        (∀ i, v i ≠ 0) →
        ∃ U : Matrix (Fin k) (Fin k) ℂ,
          IsUnit U.det ∧
          CoordinateUniform (fun i => applyMat U (v i)) := by
  intro k n _hk v _hv
  classical
  let IdxF := (t : Fin (k + 1)) × (Fin t.val → Fin n) × (Fin t.val → Fin k)
  let good : Finset IdxF :=
    Finset.univ.filter fun ⟨_t, b, e⟩ =>
      Function.Injective b ∧ Function.Injective e ∧
        LinearIndependent ℂ (fun p => v (b p))
  let q : MvPolynomial (Fin k × Fin k) ℂ :=
    detPoly (k := k) *
      ∏ x ∈ good, minorPoly (k := k) (fun p => v (x.2.1 p)) x.2.2
  have hq : q ≠ 0 := by
    refine mul_ne_zero detPoly_ne_zero ?_
    refine Finset.prod_ne_zero_iff.mpr ?_
    intro ⟨t, b, e⟩ hx
    have h := (Finset.mem_filter.mp hx).2
    exact minorPoly_ne_zero (k := k) (fun p => v (b p)) h.2.2 h.2.1
  obtain ⟨U, hUq⟩ := exists_eval_ne_zero (k := k) q hq
  have hdet : U.det ≠ 0 := by
    have hsplit :
        eval (evalU U) (detPoly (k := k)) *
          eval (evalU U)
            (∏ x ∈ good, minorPoly (k := k) (fun p => v (x.2.1 p)) x.2.2) ≠ 0 := by
      simpa [q, map_mul] using hUq
    have : eval (evalU U) (detPoly (k := k)) ≠ 0 :=
      fun hz => hsplit (by simp [hz])
    simpa [eval_detPoly] using this
  refine ⟨U, isUnit_iff_ne_zero.mpr hdet, ?_⟩
  intro t b e hb he hli
  have ht : t ≤ k := by
    have := hli.fintype_card_le_finrank (R := ℂ) (M := Fin k → ℂ)
    simpa [Fintype.card_fin, Module.finrank_fintype_fun_eq_card] using this
  -- Independence of `U · v_S` implies independence of `v_S`.
  have hli0 : LinearIndependent ℂ (fun p => v (b p)) := by
    have hcomp :
        mulVecLin U ∘ (fun p => v (b p)) = fun p => U.mulVec (v (b p)) := by
      funext p
      rfl
    have hli' : LinearIndependent ℂ (mulVecLin U ∘ fun p => v (b p)) := by
      rw [hcomp]
      simpa [applyMat] using hli
    exact LinearIndependent.of_comp (mulVecLin U) hli'
  let t' : Fin (k + 1) := ⟨t, Nat.lt_succ_of_le ht⟩
  have hmem : (⟨t', b, e⟩ : IdxF) ∈ good := by
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, hb, he, ?_⟩
    simpa [t'] using hli0
  have hminor :
      eval (evalU U) (minorPoly (k := k) (fun p => v (b p)) e) ≠ 0 := by
    have hprod :
        eval (evalU U)
          (∏ x ∈ good, minorPoly (k := k) (fun p => v (x.2.1 p)) x.2.2) ≠ 0 := by
      intro hz
      apply hUq
      simp [q, map_mul, hz]
    have hne :
        (∏ x ∈ good,
            eval (evalU U) (minorPoly (k := k) (fun p => v (x.2.1 p)) x.2.2)) ≠ 0 := by
      simpa [map_prod] using hprod
    exact Finset.prod_ne_zero_iff.mp hne ⟨t', b, e⟩ hmem
  have : (Matrix.of fun p q => (U.mulVec (v (b p))) (e q)).det ≠ 0 := by
    simpa [eval_minorPoly] using hminor
  simpa [applyMat] using this

end

end Submissions.CoordinateUniformGL.GL
