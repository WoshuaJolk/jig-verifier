import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Data.Set.Card
import Mathlib.Topology.Order.OrderClosed

open Filter
open scoped Topology

/-!
# Erdős problem 84, remaining open part

The number of cycle-length sets realized by graphs on `n` vertices should grow
faster than `2^(n/2)`.
-/

namespace Statements.Erdos84CycleSetGrowth

def CycleSet {V : Type*} (G : SimpleGraph V) : Set ℕ :=
  {length | ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧ c.length = length}

noncomputable def cycleSetCount (n : ℕ) : ℕ :=
  Set.ncard (Set.range (fun G : SimpleGraph (Fin n) => CycleSet G))

abbrev statement : Prop :=
  Tendsto
    (fun n : ℕ =>
      (cycleSetCount n : ℝ) / (2 : ℝ) ^ ((n : ℝ) / 2))
    atTop atTop

theorem target : statement := sorry

end Statements.Erdos84CycleSetGrowth
