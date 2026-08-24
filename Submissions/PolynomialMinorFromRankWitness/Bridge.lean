import Mathlib

namespace Submissions.PolynomialMinorFromRankWitness.Bridge

open Matrix MvPolynomial

noncomputable section

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

theorem proof :
    ∀ (k d : ℕ) (σ : Type) (v : Fin d → Fin k → MvPolynomial σ ℂ)
      (z : σ → ℂ),
      LinearIndependent ℂ (fun q i => eval z (v q i)) →
      ∃ e : Fin d → Fin k, Function.Injective e ∧
        Matrix.det (Matrix.of fun p q => v q (e p)) ≠ 0 := by
  intro k d σ v z hli
  obtain ⟨e, he, hdet⟩ := exists_nonzero_coord_minor
    (fun q i => eval z (v q i)) hli
  refine ⟨e, he, ?_⟩
  intro hp
  have hev :
      eval z (Matrix.det (Matrix.of fun p q => v q (e p))) = 0 := by
    simp [hp]
  rw [(eval z).map_det] at hev
  exact hdet hev

end

end Submissions.PolynomialMinorFromRankWitness.Bridge
