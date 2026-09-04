import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Paths

/-!
A **restatement attack** (must-fail control). This file proves the `n = 4` instance only
under the extra hypothesis `G = ⊤`. Everything here is true and compiles cleanly; it is
simply not the statement that was asked, and the verifier's anti-restatement bridge must
reject it with `restatement`.
-/

namespace Submissions.ErdosGyarfasFourVertexInstance.WeakenedComplete

open SimpleGraph

theorem proof : ∀ (G : SimpleGraph (Fin 4)) [DecidableRel G.Adj],
    G = ⊤ → (∀ v : Fin 4, 3 ≤ G.degree v) →
      ∃ (v : Fin 4) (c : G.Walk v v) (k : ℕ), c.IsCycle ∧ 2 ≤ k ∧ c.length = 2 ^ k := by
  intro G _ hG _
  subst hG
  have a01 : (⊤ : SimpleGraph (Fin 4)).Adj 0 1 := Fin.ne_of_val_ne (by decide)
  have a12 : (⊤ : SimpleGraph (Fin 4)).Adj 1 2 := Fin.ne_of_val_ne (by decide)
  have a23 : (⊤ : SimpleGraph (Fin 4)).Adj 2 3 := Fin.ne_of_val_ne (by decide)
  have a30 : (⊤ : SimpleGraph (Fin 4)).Adj 3 0 := Fin.ne_of_val_ne (by decide)
  refine ⟨0, .cons a01 (.cons a12 (.cons a23 (.cons a30 .nil))), 2, ?_, le_refl 2, rfl⟩
  rw [Walk.isCycle_def]
  refine ⟨?_, by simp, ?_⟩
  · rw [Walk.isTrail_def]
    simp [Walk.edges]
  · simp [Walk.support]

end Submissions.ErdosGyarfasFourVertexInstance.WeakenedComplete
