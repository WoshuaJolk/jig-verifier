import Mathlib.Combinatorics.SimpleGraph.Extremal.Basic
import Mathlib.Combinatorics.SimpleGraph.Bipartite
import Mathlib.Data.Real.Basic
import Mathlib.Order.Filter.AtTopBot.Basic

open Filter SimpleGraph

namespace Statements.Erdos575BipartiteCompactness

structure FiniteGraph where
  order : ℕ
  graph : SimpleGraph (Fin order)

def FamilyFree (family : Finset FiniteGraph) {n : ℕ}
    (host : SimpleGraph (Fin n)) : Prop :=
  ∀ forbidden ∈ family, forbidden.graph.Free host

open scoped Classical in
noncomputable def familyExtremal (family : Finset FiniteGraph) (n : ℕ) : ℕ :=
  (Finset.univ.filter (FamilyFree family)).sup
    fun host : SimpleGraph (Fin n) => host.edgeFinset.card

def IsControlledByBipartiteMember (family : Finset FiniteGraph) : Prop :=
  ∃ forbidden ∈ family, forbidden.graph.IsBipartite ∧
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop,
      (extremalNumber n forbidden.graph : ℝ) ≤
        C * (familyExtremal family n : ℝ)

/-- Erdős 575 has a negative answer: a finite family containing a
bipartite graph need not be controlled by any bipartite member. -/
abbrev statement : Prop :=
  ∃ family : Finset FiniteGraph,
    family.Nonempty ∧
    (∃ forbidden ∈ family, forbidden.graph.IsBipartite) ∧
    ¬IsControlledByBipartiteMember family

theorem target : statement := sorry

end Statements.Erdos575BipartiteCompactness
