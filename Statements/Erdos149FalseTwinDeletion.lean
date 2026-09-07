import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.LineGraph

namespace Statements.Erdos149FalseTwinDeletion

def strongConflict {V : Type*} (G : SimpleGraph V) : SimpleGraph G.edgeSet where
  Adj e f :=
    e ≠ f ∧
      ((G.lineGraph).Adj e f ∨
        ∃ middle : G.edgeSet,
          (G.lineGraph).Adj e middle ∧ (G.lineGraph).Adj middle f)
  symm := ⟨by
    intro e f h
    refine ⟨h.1.symm, ?_⟩
    rcases h.2 with hef | ⟨middle, hem, hmf⟩
    · exact Or.inl hef.symm
    · exact Or.inr ⟨middle, hmf.symm, hem.symm⟩⟩
  loopless := ⟨by intro e h; exact h.1 rfl⟩

open scoped Classical in
abbrev statement : Prop :=
  ∀ n : ℕ, ∀ G : SimpleGraph (Fin n), ∀ p q : Fin n, ∀ U : Finset (Fin n),
    U.card = 4 → p ≠ q → G.maxDegree ≤ 4 →
    (∀ v, G.Adj p v ↔ v ∈ U) → (∀ v, G.Adj q v ↔ v ∈ U) →
    (strongConflict (G.induce {v | v ≠ p ∧ v ≠ q})).Colorable 20 →
      (strongConflict G).Colorable 20

theorem target : statement := sorry
end Statements.Erdos149FalseTwinDeletion
