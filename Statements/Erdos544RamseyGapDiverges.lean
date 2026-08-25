import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Order.Filter.AtTopBot.CountablyGenerated
import Mathlib.Order.Lattice.Nat

open Filter

namespace Statements.Erdos544RamseyGapDiverges

def IsGraphRamsey (n k l : ℕ) : Prop :=
  ∀ G : SimpleGraph (Fin n), ¬(G.CliqueFree k ∧ (Gᶜ).CliqueFree l)

noncomputable def graphRamseyNumber (k l : ℕ) : ℕ :=
  sInf {n : ℕ | IsGraphRamsey n k l}

/-- Erdős Problem 544, first part. -/
abbrev statement : Prop :=
  Tendsto
    (fun k : ℕ => graphRamseyNumber 3 (k + 1) - graphRamseyNumber 3 k)
    atTop atTop

theorem target : statement := sorry

end Statements.Erdos544RamseyGapDiverges
