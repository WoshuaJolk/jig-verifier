import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Tactic

namespace Statements.Erdos810CanonicalEdgesLoopless

def allEdges (n : ℕ) : Finset (Fin n × Fin n) :=
  (Finset.univ ×ˢ Finset.univ).filter fun e => e.1 < e.2

/-- Every canonical edge has distinct endpoints. -/
abbrev statement : Prop :=
  ∀ n : ℕ, ∀ e ∈ allEdges n, e.1 ≠ e.2

theorem target : statement := sorry

end Statements.Erdos810CanonicalEdgesLoopless
