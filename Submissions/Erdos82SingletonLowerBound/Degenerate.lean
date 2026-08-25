import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Subgraph
import Mathlib.Data.Set.Card
import Mathlib.Order.Lattice.Nat

open SimpleGraph

namespace Submissions.Erdos82SingletonLowerBound.Degenerate

variable {V : Type*} [Fintype V]

def isRegularInduced {G : SimpleGraph V} (S : Subgraph G) : Prop :=
  open scoped Classical in
  S.IsInduced ∧ ∃ k, S.coe.IsRegularOfDegree k

noncomputable def F (n : ℕ) : ℕ :=
  sSup {k | ∀ (G : SimpleGraph (Fin n)), ∃ S : Subgraph G,
    isRegularInduced S ∧ k ≤ S.verts.ncard}

theorem proof : False → ∀ n : ℕ, 0 < n → 1 ≤ F n := by
  intro h
  exact h.elim

end Submissions.Erdos82SingletonLowerBound.Degenerate
