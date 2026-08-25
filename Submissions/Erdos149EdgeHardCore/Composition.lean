import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.LineGraph

namespace Submissions.Erdos149EdgeHardCore.Composition

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

noncomputable def budget {n : ℕ} (G : SimpleGraph (Fin n)) : ℕ :=
  (5 * (maximumDegree G) ^ 2) / 4

def Root : Prop :=
  ∀ n : ℕ, ∀ G : SimpleGraph (Fin n), StrongColorable G (budget G)

def DegreeZeroCase : Prop :=
  ∀ n : ℕ, ∀ G : SimpleGraph (Fin n),
    maximumDegree G = 0 → StrongColorable G 0

def EdgeCountCase : Prop :=
  ∀ n : ℕ, ∀ G : SimpleGraph (Fin n),
    StrongColorable G (Nat.card G.edgeSet)

def EdgeHardCore : Prop :=
  ∀ n : ℕ, ∀ G : SimpleGraph (Fin n),
    maximumDegree G ≠ 0 →
    budget G < Nat.card G.edgeSet →
    StrongColorable G (budget G)

abbrev statement : Prop :=
  DegreeZeroCase → EdgeCountCase → (Root ↔ EdgeHardCore)

theorem proof : statement := by
  intro hZero hEdges
  constructor
  · intro hRoot n G _ _
    exact hRoot n G
  · intro hCore n G
    by_cases hDegree : maximumDegree G = 0
    · simpa [budget, hDegree] using hZero n G hDegree
    · by_cases hMany : budget G < Nat.card G.edgeSet
      · exact hCore n G hDegree hMany
      · exact SimpleGraph.Colorable.mono (Nat.le_of_not_gt hMany) (hEdges n G)

end Submissions.Erdos149EdgeHardCore.Composition
