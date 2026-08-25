import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Subgraph
import Mathlib.Data.Set.Card
import Mathlib.Order.Lattice.Nat

open SimpleGraph

namespace Statements.Erdos82SingletonLowerBound

variable {V : Type*} [Fintype V]

def isRegularInduced {G : SimpleGraph V} (S : Subgraph G) : Prop :=
  open scoped Classical in
  S.IsInduced ∧ ∃ k, S.coe.IsRegularOfDegree k

noncomputable def F (n : ℕ) : ℕ :=
  sSup {k | ∀ (G : SimpleGraph (Fin n)), ∃ S : Subgraph G,
    isRegularInduced S ∧ k ≤ S.verts.ncard}

/-- Every nonempty finite graph has a one-vertex regular induced subgraph. -/
abbrev statement : Prop :=
  ∀ n : ℕ, 0 < n → 1 ≤ F n

theorem target : statement := sorry

end Statements.Erdos82SingletonLowerBound
