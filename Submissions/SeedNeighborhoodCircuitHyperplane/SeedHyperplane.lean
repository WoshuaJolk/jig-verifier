import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.LinearAlgebra.LinearIndependent.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Tactic

namespace Submissions.SeedNeighborhoodCircuitHyperplane.SeedHyperplane

noncomputable section

def Tight {k m : ℕ} (v : Fin m → EuclideanSpace ℂ (Fin k)) : Prop :=
  ∀ S : Finset (Fin m), S.card + 1 ≤ k →
    LinearIndependent ℂ fun i : (S : Set (Fin m)) => v i.1

def localSpan {k m : ℕ} (v : Fin m → EuclideanSpace ℂ (Fin k))
    (S : Finset (Fin m)) : Submodule ℂ (EuclideanSpace ℂ (Fin k)) :=
  Submodule.span ℂ (Set.range fun i : (S : Set (Fin m)) => v i.1)

lemma neighbor_span_le_polar
    {k m : ℕ} {v : Fin m → EuclideanSpace ℂ (Fin k)}
    {N : Fin m → Finset (Fin m)}
    (hexact : ∀ i j, inner ℂ (v i) (v j) = 0 ↔ j ∈ N i)
    (i : Fin m) :
    localSpan v (N i) ≤ (ℂ ∙ v i)ᗮ := by
  rw [localSpan, Submodule.span_le]
  rintro _ ⟨j, rfl⟩
  apply ((ℂ ∙ v i).mem_orthogonal (v j.1)).2
  intro x hx
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_singleton.mp hx)
  simp [inner_smul_left, (hexact i j).2 j.2]

lemma neighbor_span_finrank_ge
    {k m : ℕ} (hk : 2 ≤ k)
    {v : Fin m → EuclideanSpace ℂ (Fin k)}
    {N : Fin m → Finset (Fin m)}
    (htight : Tight v)
    (hcard : ∀ i, (N i).card = k)
    (i : Fin m) :
    k - 1 ≤ Module.finrank ℂ (localSpan v (N i)) := by
  have hne : (N i).Nonempty := Finset.card_pos.mp (by rw [hcard i]; omega)
  obtain ⟨r, hr⟩ := hne
  let S := (N i).erase r
  have hScard : S.card = k - 1 := by
    simp [S, Finset.card_erase_of_mem hr, hcard i]
  have hSbound : S.card + 1 ≤ k := by omega
  have hli := htight S hSbound
  let K := Submodule.span ℂ
    (Set.range fun j : (S : Set (Fin m)) => v j.1)
  have hKrank : Module.finrank ℂ K = k - 1 := by
    dsimp [K]
    have h := finrank_span_eq_card hli
    simpa [Fintype.card_coe, hScard] using h
  have hSK : K ≤ localSpan v (N i) := by
    dsimp [K, localSpan]
    apply Submodule.span_mono
    rintro _ ⟨j, rfl⟩
    exact ⟨⟨j.1, Finset.mem_of_mem_erase j.2⟩, rfl⟩
  have hmono := Submodule.finrank_mono hSK
  omega

lemma polar_finrank
    {k m : ℕ} {v : Fin m → EuclideanSpace ℂ (Fin k)}
    (hv : ∀ i, v i ≠ 0) (i : Fin m) :
    Module.finrank ℂ ((ℂ ∙ v i)ᗮ) = k - 1 := by
  have hsum := (ℂ ∙ v i).finrank_add_finrank_orthogonal
  rw [finrank_span_singleton (hv i), finrank_euclideanSpace_fin] at hsum
  omega

theorem proof :
    ∀ (k m : ℕ), 2 ≤ k →
      ∀ (v : Fin m → EuclideanSpace ℂ (Fin k))
        (N : Fin m → Finset (Fin m)),
        (∀ i, v i ≠ 0) →
        Tight v →
        (∀ i j, inner ℂ (v i) (v j) = 0 ↔ j ∈ N i) →
        (∀ i, (N i).card = k) →
        ∀ i,
          localSpan v (N i) = (ℂ ∙ v i)ᗮ ∧
          (∀ j, v j ∈ localSpan v (N i) ↔ j ∈ N i) ∧
          ¬ LinearIndependent ℂ
              (fun j : (N i : Set (Fin m)) => v j.1) := by
  intro k m hk v N hv htight hexact hcard i
  have hle := neighbor_span_le_polar hexact i
  have hlow := neighbor_span_finrank_ge hk htight hcard i
  have hpolar := polar_finrank hv i
  have hrank :
      Module.finrank ℂ (localSpan v (N i)) =
        Module.finrank ℂ ((ℂ ∙ v i)ᗮ) := by
    apply Nat.le_antisymm
    · exact Submodule.finrank_mono hle
    · omega
  have hspan : localSpan v (N i) = (ℂ ∙ v i)ᗮ :=
    Submodule.eq_of_le_of_finrank_eq hle hrank
  refine ⟨hspan, ?_, ?_⟩
  · intro j
    constructor
    · intro hj
      have hjpolar : v j ∈ (ℂ ∙ v i)ᗮ := by simpa [hspan] using hj
      have hz : inner ℂ (v i) (v j) = 0 :=
        ((ℂ ∙ v i).mem_orthogonal (v j)).mp hjpolar (v i)
          (Submodule.mem_span_singleton_self (v i))
      exact (hexact i j).mp hz
    · intro hj
      apply Submodule.subset_span
      exact ⟨⟨j, hj⟩, rfl⟩
  · intro hli
    have hneighbor :
        Module.finrank ℂ (localSpan v (N i)) = k := by
      rw [localSpan, finrank_span_eq_card hli]
      simpa [hcard i] using (Fintype.card_coe (N i))
    rw [hspan, hpolar] at hneighbor
    omega

end

end Submissions.SeedNeighborhoodCircuitHyperplane.SeedHyperplane
