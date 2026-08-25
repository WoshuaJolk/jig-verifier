import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Tactic

namespace Submissions.Erdos627OneVertexCalibration.Kernel

noncomputable def ratio {n : ℕ} (G : SimpleGraph (Fin n)) : ℝ :=
  (ENat.toNat G.chromaticNumber : ℝ) / G.cliqueNum

theorem proof :
    ratio (⊤ : SimpleGraph (Fin 1)) = 1 := by
  have hclique : (⊤ : SimpleGraph (Fin 1)).cliqueNum = 1 := by
    apply le_antisymm
    · obtain ⟨s, hs⟩ :=
        (⊤ : SimpleGraph (Fin 1)).exists_isNClique_cliqueNum
      rw [← hs.card_eq]
      simpa using Finset.card_le_card (Finset.subset_univ s)
    · have hc : (⊤ : SimpleGraph (Fin 1)).IsClique ({0} : Finset (Fin 1)) := by
        simp
      simpa using hc.card_le_cliqueNum
  simp [ratio, hclique]

end Submissions.Erdos627OneVertexCalibration.Kernel
