import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.LineGraph

namespace Statements.J5P274FourCutReduction

namespace StructuralAttack
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

end StructuralAttack

namespace K23Regular

open SimpleGraph
open scoped Classical
/-- Every distinct pair has at most two common neighbors. -/
def CommonNeighborsLeTwo {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) : Prop :=
  ∀ x y, x ≠ y → (G.neighborFinset x ∩ G.neighborFinset y).card ≤ 2

end K23Regular

namespace TwoCut

open SimpleGraph Finset
open scoped Classical

section CrossingDefinition
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)

/-- Each edge across S is represented exactly once, oriented out of S. -/
noncomputable def crossingPairs (S : Finset V) : Finset (V × V) :=
  univ.filter (fun e => e.1 ∈ S ∧ e.2 ∉ S ∧ G.Adj e.1 e.2)

end CrossingDefinition

end TwoCut

open SimpleGraph Finset StructuralAttack TwoCut
open scoped Classical

abbrev statement : Prop :=
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)), G.maxDegree ≤ 4 →
      (strongConflict G).Colorable 20) ↔
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)), G.IsRegularOfDegree 4 →
      K23Regular.CommonNeighborsLeTwo G →
      (∀ S : Finset (Fin n), S.Nonempty → Sᶜ.Nonempty → 4 ≤ (crossingPairs G S).card) →
      (strongConflict G).Colorable 20)

end Statements.J5P274FourCutReduction
