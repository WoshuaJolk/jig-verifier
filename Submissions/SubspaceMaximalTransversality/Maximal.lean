import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

namespace Submissions.SubspaceMaximalTransversality.Maximal

open Submodule

noncomputable section

lemma exists_submodule_finrank_eq_of_le
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    (U : Submodule ℂ V) (d : ℕ) (hd : d ≤ Module.finrank ℂ U) :
    ∃ D : Submodule ℂ V, D ≤ U ∧ Module.finrank ℂ D = d := by
  obtain ⟨f, hf⟩ := exists_linearIndependent_of_le_finrank hd
  let g : Fin d → V := fun i => (f i : V)
  have hg : LinearIndependent ℂ g :=
    hf.map' U.subtype U.ker_subtype
  refine ⟨Submodule.span ℂ (Set.range g), ?_, ?_⟩
  · rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact (f i).property
  · simpa [g] using (finrank_span_eq_card hg)

lemma exists_target_subspace
    {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (U : Submodule ℂ V) (b : ℕ) (hbV : b ≤ Module.finrank ℂ V) :
    ∃ W' : Submodule ℂ V,
      Module.finrank ℂ W' = b ∧
      Module.finrank ℂ (U ⊔ W' : Submodule ℂ V) =
        min (Module.finrank ℂ V) (Module.finrank ℂ U + b) := by
  obtain ⟨C, hC⟩ := U.exists_isCompl
  have hdim : Module.finrank ℂ U + Module.finrank ℂ C = Module.finrank ℂ V :=
    Submodule.finrank_add_eq_of_isCompl hC
  by_cases hbC : b ≤ Module.finrank ℂ C
  · obtain ⟨D, hDC, hD⟩ := exists_submodule_finrank_eq_of_le C b hbC
    have hUD : Disjoint U D := hC.disjoint.mono_right hDC
    refine ⟨D, hD, ?_⟩
    have hsum : Module.finrank ℂ (U ⊔ D : Submodule ℂ V) =
        Module.finrank ℂ U + b := by
      have h := Submodule.finrank_sup_add_finrank_inf_eq U D
      rw [hUD.eq_bot, finrank_bot, add_zero, hD] at h
      exact h
    rw [hsum, Nat.min_eq_right]
    omega
  · have hCb : Module.finrank ℂ C < b := Nat.lt_of_not_ge hbC
    have hsub : b - Module.finrank ℂ C ≤ Module.finrank ℂ U := by omega
    obtain ⟨A, hAU, hA⟩ :=
      exists_submodule_finrank_eq_of_le U (b - Module.finrank ℂ C) hsub
    have hCA : Disjoint C A := hC.symm.disjoint.mono_right hAU
    refine ⟨C ⊔ A, ?_, ?_⟩
    · have h := Submodule.finrank_sup_add_finrank_inf_eq C A
      rw [hCA.eq_bot, finrank_bot, add_zero, hA] at h
      omega
    · have htop : U ⊔ (C ⊔ A) = ⊤ := by
        simp [← sup_assoc, hC.codisjoint.eq_top]
      rw [htop, finrank_top, Nat.min_eq_left]
      omega

lemma exists_linearEquiv_map_eq_of_finrank_eq
    {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (W W' : Submodule ℂ V)
    (hrank : Module.finrank ℂ W = Module.finrank ℂ W') :
    ∃ g : V ≃ₗ[ℂ] V, W.map g.toLinearMap = W' := by
  let f : W ≃ₗ[ℂ] W' :=
    Classical.choice (FiniteDimensional.nonempty_linearEquiv_of_finrank_eq hrank)
  obtain ⟨g, hg⟩ := Submodule.exists_linearEquiv_restrict_eq f
  refine ⟨g, Submodule.eq_of_le_of_finrank_eq ?_ ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    have hfx : (f ⟨x, hx⟩ : V) ∈ W' := (f ⟨x, hx⟩).property
    simpa [hg ⟨x, hx⟩] using hfx
  · rw [g.finrank_map_eq, hrank]

theorem proof :
    ∀ k : ℕ, ∀ U W : Submodule ℂ (Fin k → ℂ),
      ∃ g : (Fin k → ℂ) ≃ₗ[ℂ] (Fin k → ℂ),
        Module.finrank ℂ
            (U ⊔ W.map g.toLinearMap : Submodule ℂ (Fin k → ℂ)) =
          min k (Module.finrank ℂ U + Module.finrank ℂ W) := by
  intro k U W
  have hVk : Module.finrank ℂ (Fin k → ℂ) = k := by
    rw [Module.finrank_pi, Fintype.card_fin]
  have hWk : Module.finrank ℂ W ≤ Module.finrank ℂ (Fin k → ℂ) :=
    Submodule.finrank_le W
  obtain ⟨W', hW', hUW'⟩ :=
    exists_target_subspace U (Module.finrank ℂ W) hWk
  obtain ⟨g, hg⟩ := exists_linearEquiv_map_eq_of_finrank_eq W W' hW'.symm
  refine ⟨g, ?_⟩
  rw [hg, hUW', hVk]

end

end Submissions.SubspaceMaximalTransversality.Maximal
