import Mathlib.Combinatorics.SimpleGraph.Bipartite
import Mathlib.Combinatorics.SimpleGraph.Copy
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace Statements.Erdos571TuranExponents

open SimpleGraph

def HasTuranExponent (α : ℝ) : Prop :=
  ∃ v : ℕ, ∃ G : SimpleGraph (Fin v),
    G.IsBipartite ∧
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
        (∀ H : SimpleGraph (Fin n), ¬G ⊑ H →
          (H.edgeSet.ncard : ℝ) ≤ C * (n : ℝ) ^ α) ∧
        ∃ H : SimpleGraph (Fin n), ¬G ⊑ H ∧
          c * (n : ℝ) ^ α ≤ (H.edgeSet.ncard : ℝ)

/-- Erdős--Simonovits Turán exponent conjecture, Problem 571. -/
abbrev statement : Prop :=
  ∀ α : ℚ, 1 ≤ α → α < 2 → HasTuranExponent (α : ℝ)

theorem target : statement := sorry

end Statements.Erdos571TuranExponents
