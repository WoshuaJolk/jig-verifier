import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Tactic

namespace Submissions.Erdos810CanonicalEdgesLoopless.Direct

def allEdges (n : ℕ) : Finset (Fin n × Fin n) :=
  (Finset.univ ×ˢ Finset.univ).filter fun e => e.1 < e.2

theorem proof :
    ∀ n : ℕ, ∀ e ∈ allEdges n, e.1 ≠ e.2 := by
  intro n e he
  have hlt : e.1 < e.2 := (Finset.mem_filter.mp he).2
  exact ne_of_lt hlt

end Submissions.Erdos810CanonicalEdgesLoopless.Direct
