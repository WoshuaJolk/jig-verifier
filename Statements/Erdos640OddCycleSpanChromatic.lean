import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Combinatorics.SimpleGraph.Paths

namespace Statements.Erdos640OddCycleSpanChromatic

/-- Erdős Problem 640. -/
abbrev statement : Prop :=
  ∃ f : ℕ → ℕ, ∀ k : ℕ, 3 ≤ k →
    ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
      (f k : ℕ∞) ≤ G.chromaticNumber →
      ∃ (v : V) (p : G.Walk v v),
        p.IsCycle ∧ Odd p.length ∧
          (k : ℕ∞) ≤
            (G.induce {x | x ∈ p.support}).chromaticNumber

theorem target : statement := sorry

end Statements.Erdos640OddCycleSpanChromatic
