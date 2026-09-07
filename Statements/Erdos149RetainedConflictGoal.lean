import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.LineGraph
import Mathlib.Algebra.Order.BigOperators.Group.Finset

namespace Statements.Erdos149RetainedConflictGoal

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

def Root : Prop :=
  ∀ n : ℕ, ∀ G : SimpleGraph (Fin n),
    StrongColorable G ((5 * (maximumDegree G)^2) / 4)

def RetainedConflictGoal : Prop :=
  ∀ n : ℕ, ∀ G : SimpleGraph (Fin n), ∀ F : Set G.edgeSet,
    ((strongConflict G).induce F).Colorable ((5 * (maximumDegree G)^2) / 4)

theorem root_iff_retained : Root ↔ RetainedConflictGoal := by
  constructor
  · intro h n G F
    exact SimpleGraph.Colorable.of_hom
      (SimpleGraph.Embedding.induce F).toHom (h n G)
  · intro h n G
    exact SimpleGraph.Colorable.of_hom
      (strongConflict G).induceUnivIso.symm.toHom (h n G Set.univ)

abbrev statement : Prop := RetainedConflictGoal

theorem target : statement := sorry
end Statements.Erdos149RetainedConflictGoal
