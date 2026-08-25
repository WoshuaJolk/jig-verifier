import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.LineGraph

namespace Submissions.Erdos149DegreeZero.Direct

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

theorem proof :
    ∀ n : ℕ, ∀ G : SimpleGraph (Fin n),
      maximumDegree G = 0 → StrongColorable G 0 := by
  intro n G hdegree
  classical
  have hbot : G = ⊥ := by
    apply SimpleGraph.maxDegree_eq_zero_iff.mp
    simpa [maximumDegree] using hdegree
  subst G
  letI : IsEmpty (⊥ : SimpleGraph (Fin n)).edgeSet := ⟨by
    rintro ⟨edge, hedge⟩
    simpa using hedge⟩
  exact SimpleGraph.Colorable.of_isEmpty 0

end Submissions.Erdos149DegreeZero.Direct
