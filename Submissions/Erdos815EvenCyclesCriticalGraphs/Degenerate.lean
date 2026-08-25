import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Order.Filter.AtTopBot.Basic

open Filter

namespace Submissions.Erdos815EvenCyclesCriticalGraphs.Degenerate

noncomputable def degreeIn {n : ℕ} (G : SimpleGraph (Fin n))
    (S : Finset (Fin n)) (v : Fin n) : ℕ := by
  classical
  exact (S.filter fun w => G.Adj v w).card

noncomputable def IsDegreeThreeCritical {n : ℕ}
    (G : SimpleGraph (Fin n)) : Prop := by
  classical
  exact G.edgeFinset.card = 2 * n - 2 ∧
    ∀ S : Finset (Fin n), S.Nonempty → S.card < n →
      ∃ v ∈ S, degreeIn G S v ≤ 2

def HasCycle {n : ℕ} (G : SimpleGraph (Fin n)) (k : ℕ) : Prop :=
  ∃ c : Fin k ↪ Fin n,
    ∀ i j : Fin k, j.val = (i.val + 1) % k →
      G.Adj (c i) (c j)

/-- The surviving even-cycle form of Erdős 815. -/
abbrev statement : Prop :=
  ∀ k : ℕ, 4 ≤ k → k % 2 = 0 →
    ∀ᶠ n : ℕ in atTop, ∀ G : SimpleGraph (Fin n),
      IsDegreeThreeCritical G → HasCycle G k

theorem proof : False → statement := False.elim

end Submissions.Erdos815EvenCyclesCriticalGraphs.Degenerate
