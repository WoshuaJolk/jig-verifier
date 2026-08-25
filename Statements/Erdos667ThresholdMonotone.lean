import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.Nat.Find

namespace Statements.Erdos667ThresholdMonotone

open SimpleGraph
open scoped Classical

def LocallyDense (p q : ℕ) {n : ℕ} (G : SimpleGraph (Fin n)) : Prop :=
  ∀ s : Finset (Fin n), s.card = p →
    q ≤ (G.induce s).edgeSet.ncard

noncomputable def H (p q n : ℕ) : ℕ :=
  Nat.findGreatest
    (fun m => ∀ G : SimpleGraph (Fin n),
      LocallyDense p q G → ¬G.CliqueFree m) n

/-- Increasing the required local edge count can only increase the largest
clique size forced in every graph. -/
abbrev statement : Prop :=
  ∀ p q r n : ℕ, q ≤ r → H p q n ≤ H p r n

theorem target : statement := sorry

end Statements.Erdos667ThresholdMonotone
