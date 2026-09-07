import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.LineGraph

namespace Statements.Erdos149RegularCaseReduction

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

noncomputable def maximumDegree {n : ℕ} (G : SimpleGraph (Fin n)) : ℕ :=
  open scoped Classical in G.maxDegree

def StrongColorable {V : Type*} (G : SimpleGraph V) (colors : ℕ) : Prop :=
  (strongConflict G).Colorable colors

abbrev rootStatement : Prop :=
  ∀ n : ℕ, ∀ G : SimpleGraph (Fin n),
    StrongColorable G ((5 * (maximumDegree G) ^ 2) / 4)

open scoped Classical in
def regularStatement : Prop :=
  ∀ n : ℕ, ∀ G : SimpleGraph (Fin n),
    (∃ D : ℕ, G.IsRegularOfDegree D) →
    StrongColorable G ((5 * (maximumDegree G) ^ 2) / 4)

/-- Exact reduction, not a proof of either equivalent conjecture. -/
abbrev statement : Prop := rootStatement ↔ regularStatement

theorem target : statement := sorry
end Statements.Erdos149RegularCaseReduction
