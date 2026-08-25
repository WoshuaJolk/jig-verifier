import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Subgraph
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Order.Lattice.Nat

open SimpleGraph Filter

namespace Statements.Erdos82RegularInducedGrowth

variable {V : Type*} [Fintype V]

/-- `S` is an induced subgraph whose underlying simple graph is regular. -/
def isRegularInduced {G : SimpleGraph V} (S : Subgraph G) : Prop :=
  open scoped Classical in
  S.IsInduced ∧ ∃ k, S.coe.IsRegularOfDegree k

/-- The largest lower bound on the order of a regular induced subgraph which is guaranteed in every graph on `n` vertices. -/
noncomputable def F (n : ℕ) : ℕ :=
  sSup {k | ∀ (G : SimpleGraph (Fin n)), ∃ S : Subgraph G,
    isRegularInduced S ∧ k ≤ S.verts.ncard}

/-- Erdős Problem 82: `F(n) / log n` tends to infinity. -/
abbrev statement : Prop :=
  Tendsto (fun n : ℕ => (F n : ℝ) / Real.log n) atTop atTop

theorem target : statement := sorry

end Statements.Erdos82RegularInducedGrowth
