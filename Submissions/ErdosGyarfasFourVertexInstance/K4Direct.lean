import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Paths

/-!
Smoke test for the Erdős–Gyárfás pose: the `n = 4` instance. Every simple graph on four
vertices in which every vertex has degree at least 3 is complete, and the walk
`0 → 1 → 2 → 3 → 0` is a cycle of length `4 = 2 ^ 2`.
-/

namespace Submissions.ErdosGyarfasFourVertexInstance.K4Direct

open SimpleGraph

/-- Degree at least `3` on four vertices forces adjacency to every other vertex. -/
lemma adj_of_degree (G : SimpleGraph (Fin 4)) [DecidableRel G.Adj]
    (h : ∀ v : Fin 4, 3 ≤ G.degree v) {u v : Fin 4} (huv : u ≠ v) : G.Adj u v := by
  by_contra hadj
  have hsub : G.neighborFinset u ⊆ (Finset.univ.erase u).erase v := by
    intro w hw
    rw [mem_neighborFinset] at hw
    refine Finset.mem_erase.mpr ⟨?_, Finset.mem_erase.mpr ⟨?_, Finset.mem_univ _⟩⟩
    · rintro rfl
      exact hadj hw
    · rintro rfl
      exact G.irrefl hw
  have hcard := Finset.card_le_card hsub
  rw [card_neighborFinset_eq_degree] at hcard
  have h2 : ((Finset.univ.erase u).erase v).card = 2 := by
    rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨huv.symm, Finset.mem_univ _⟩),
      Finset.card_erase_of_mem (Finset.mem_univ _)]
    simp
  have := h u
  omega

theorem proof : ∀ (G : SimpleGraph (Fin 4)) [DecidableRel G.Adj],
    (∀ v : Fin 4, 3 ≤ G.degree v) →
      ∃ (v : Fin 4) (c : G.Walk v v) (k : ℕ), c.IsCycle ∧ 2 ≤ k ∧ c.length = 2 ^ k := by
  intro G _ h
  have a01 : G.Adj 0 1 := adj_of_degree G h (by decide)
  have a12 : G.Adj 1 2 := adj_of_degree G h (by decide)
  have a23 : G.Adj 2 3 := adj_of_degree G h (by decide)
  have a30 : G.Adj 3 0 := adj_of_degree G h (by decide)
  refine ⟨0, .cons a01 (.cons a12 (.cons a23 (.cons a30 .nil))), 2, ?_, le_refl 2, rfl⟩
  rw [Walk.isCycle_def]
  refine ⟨?_, by simp, ?_⟩
  · rw [Walk.isTrail_def]
    simp [Walk.edges]
  · simp [Walk.support]

end Submissions.ErdosGyarfasFourVertexInstance.K4Direct

