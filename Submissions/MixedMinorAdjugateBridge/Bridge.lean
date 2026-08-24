import Mathlib

namespace Submissions.MixedMinorAdjugateBridge.Bridge

open Matrix MvPolynomial

noncomputable section

abbrev MatVar (k : ℕ) := Fin k × Fin k

def universalMat {k : ℕ} :
    Matrix (Fin k) (Fin k) (MvPolynomial (MatVar k) ℂ) :=
  fun i j => X (i, j)

def mixedPolyVec {k d : ℕ} (move : Fin d → Prop) [DecidablePred move]
    (v : Fin d → Fin k → ℂ) (q : Fin d) :
    Fin k → MvPolynomial (MatVar k) ℂ :=
  if move q then
    (universalMat (k := k)).adjugate.mulVec (fun i => C (v q i))
  else fun i => C (v q i)

lemma eval_universalMat (k : ℕ) (H : Matrix (Fin k) (Fin k) ℂ) :
    (eval (fun ij => H ij.1 ij.2)).mapMatrix (universalMat (k := k)) = H := by
  ext i j
  simp [universalMat]

lemma eval_mixedPolyVec {k d : ℕ} (move : Fin d → Prop) [DecidablePred move]
    (v : Fin d → Fin k → ℂ) (q : Fin d)
    (H : Matrix (Fin k) (Fin k) ℂ) :
    (fun i => eval (fun ij => H ij.1 ij.2) (mixedPolyVec move v q i)) =
      if move q then H.adjugate.mulVec (v q) else v q := by
  funext i
  by_cases hq : move q
  · simp only [mixedPolyVec, hq, if_true]
    let z : MatVar k → ℂ := fun ij => H ij.1 ij.2
    have hmat :
        (eval z).mapMatrix (universalMat (k := k)).adjugate = H.adjugate := by
      rw [RingHom.map_adjugate, eval_universalMat]
    calc
      eval z ((universalMat (k := k)).adjugate.mulVec
          (fun j => C (v q j)) i) =
          (((eval z).mapMatrix (universalMat (k := k)).adjugate).mulVec
            (fun j => eval z (C (v q j)))) i := by
              exact RingHom.map_mulVec (eval z) _ _ i
      _ = (H.adjugate.mulVec (v q)) i := by rw [hmat]; simp
  · simp [mixedPolyVec, hq]

lemma adjugate_realizes_invertible {k : ℕ}
    (G : Matrix (Fin k) (Fin k) ℂ) (hG : IsUnit G.det) :
    ∃ (H : Matrix (Fin k) (Fin k) ℂ) (c : ℂ),
      IsUnit H.det ∧ c ≠ 0 ∧ H.adjugate = c • G := by
  let H : Matrix (Fin k) (Fin k) ℂ := G⁻¹
  have hH : IsUnit H.det := G.isUnit_nonsing_inv_det hG
  refine ⟨H, H.det, hH, isUnit_iff_ne_zero.mp hH, ?_⟩
  calc
    H.adjugate = 1 * H.adjugate := by rw [Matrix.one_mul]
    _ = (G * H) * H.adjugate := by
      rw [show G * H = 1 by exact G.mul_nonsing_inv hG]
    _ = G * (H * H.adjugate) := by rw [Matrix.mul_assoc]
    _ = G * (H.det • (1 : Matrix (Fin k) (Fin k) ℂ)) := by
      rw [H.mul_adjugate]
    _ = H.det • G := by rw [Matrix.mul_smul, Matrix.mul_one]

lemma exists_adjugate_rank_witness {k d : ℕ}
    (move : Fin d → Prop) [DecidablePred move]
    (v : Fin d → Fin k → ℂ)
    (G : Matrix (Fin k) (Fin k) ℂ) (hG : IsUnit G.det)
    (hli : LinearIndependent ℂ
      (fun q => if move q then G.mulVec (v q) else v q)) :
    ∃ H : Matrix (Fin k) (Fin k) ℂ, IsUnit H.det ∧
      LinearIndependent ℂ
        (fun q => if move q then H.adjugate.mulVec (v q) else v q) := by
  obtain ⟨H, c, hH, hc, hAdj⟩ := adjugate_realizes_invertible G hG
  let base : Fin d → (Fin k → ℂ) :=
    fun q => if move q then G.mulVec (v q) else v q
  let hcUnit : IsUnit c := isUnit_iff_ne_zero.mpr hc
  let scale : Fin d → ℂˣ := fun q => if move q then hcUnit.unit else 1
  have hs : LinearIndependent ℂ (scale • base) := by
    exact hli.units_smul scale
  refine ⟨H, hH, ?_⟩
  convert hs using 1
  funext q i
  by_cases hq : move q
  · simp only [Pi.smul_apply', scale, base, hq, if_true]
    rw [hAdj, Matrix.smul_mulVec]
    simp
  · simp [scale, base, hq]

lemma exists_nonzero_coord_minor {k d : ℕ} (A : Fin d → Fin k → ℂ)
    (hA : LinearIndependent ℂ A) :
    ∃ e : Fin d → Fin k, Function.Injective e ∧
      (Matrix.of fun p q => A q (e p)).det ≠ 0 := by
  classical
  let rows : Fin k → (Fin d → ℂ) := fun i q => A q i
  obtain ⟨κ, a, ha, hspan, hli⟩ := exists_linearIndependent' ℂ rows
  have : Finite κ := LinearIndependent.finite (R := ℂ) (M := Fin d → ℂ) hli
  let : Fintype κ := Fintype.ofFinite κ
  let M : Matrix (Fin d) (Fin k) ℂ := A
  have hfinrank_rows :
      Module.finrank ℂ (Submodule.span ℂ (Set.range rows)) = d := by
    have hA' : LinearIndependent ℂ M.row := hA
    have hr : M.rank = d := by
      simpa [Fintype.card_fin] using (LinearIndependent.rank_matrix (M := M) hA')
    have hrows : rows = M.col := by
      funext i q
      rfl
    rw [hrows, ← rank_eq_finrank_span_cols, hr]
  have hcard : Fintype.card κ = d := by
    have h := (linearIndependent_iff_card_eq_finrank_span (R := ℂ)).mp hli
    rw [Set.finrank] at h
    rw [h, hspan, hfinrank_rows]
  let e : Fin d → Fin k :=
    fun i => a ((Fintype.equivFin κ).symm (Fin.cast hcard.symm i))
  have he : Function.Injective e :=
    ha.comp <| (Fintype.equivFin κ).symm.injective.comp
      (Fin.cast_injective hcard.symm)
  have hli_e : LinearIndependent ℂ (fun i : Fin d => rows (e i)) :=
    hli.comp _ <| (Fintype.equivFin κ).symm.injective.comp
      (Fin.cast_injective hcard.symm)
  refine ⟨e, he, ?_⟩
  let B : Matrix (Fin d) (Fin d) ℂ := Matrix.of fun p q => A q (e p)
  have hrow : LinearIndependent ℂ B.row := by
    have : B.row = fun p : Fin d => rows (e p) := by
      funext p q
      rfl
    simpa [this] using hli_e
  exact (nonsingular_iff_det_ne_zero (R := ℂ)).mp
    (Nonsingular.of_linearIndependent_row hrow)

lemma polynomial_minor_from_eval {k d : ℕ} {σ : Type}
    (w : Fin d → Fin k → MvPolynomial σ ℂ) (ξ : σ → ℂ)
    (hli : LinearIndependent ℂ (fun q i => eval ξ (w q i))) :
    ∃ e : Fin d → Fin k, Function.Injective e ∧
      Matrix.det (Matrix.of fun p q => w q (e p)) ≠ 0 := by
  obtain ⟨e, he, hdet⟩ := exists_nonzero_coord_minor
    (fun q i => eval ξ (w q i)) hli
  refine ⟨e, he, ?_⟩
  intro hp
  have hev : eval ξ (Matrix.det (Matrix.of fun p q => w q (e p))) = 0 := by
    simp [hp]
  rw [(eval ξ).map_det] at hev
  exact hdet hev

/-- An invertible mixed-rank witness produces a nonzero coordinate-minor
polynomial for the universal adjugate family. -/
theorem proof :
    ∀ (k d : ℕ) (move : Fin d → Prop) [DecidablePred move]
      (v : Fin d → Fin k → ℂ) (G : Matrix (Fin k) (Fin k) ℂ),
      IsUnit G.det →
      LinearIndependent ℂ
        (fun q => if move q then G.mulVec (v q) else v q) →
      ∃ e : Fin d → Fin k, Function.Injective e ∧
        Matrix.det (Matrix.of fun p q => mixedPolyVec move v q (e p)) ≠ 0 := by
  intro k d move _ v G hG hli
  obtain ⟨H, _hH, hliH⟩ := exists_adjugate_rank_witness move v G hG hli
  apply polynomial_minor_from_eval (mixedPolyVec move v) (fun ij => H ij.1 ij.2)
  have heval :
      (fun q i => eval (fun ij => H ij.1 ij.2) (mixedPolyVec move v q i)) =
        (fun q => if move q then H.adjugate.mulVec (v q) else v q) := by
    funext q
    exact eval_mixedPolyVec move v q H
  rw [heval]
  exact hliH

end

end Submissions.MixedMinorAdjugateBridge.Bridge
