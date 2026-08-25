import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex

namespace Statements.Erdos628TihanyConjecture

/-- The Erdős--Lovász Tihany conjecture: a non-complete `k`-chromatic
finite graph splits into induced subgraphs of chromatic numbers at least
`a` and `b` whenever `a+b=k+1`. -/
abbrev statement : Prop :=
  ∀ (V : Type) [Fintype V] (G : SimpleGraph V) (k : ℕ),
    G.chromaticNumber = (k : ℕ∞) → G.CliqueFree k →
      ∀ a b : ℕ, 2 ≤ a → 2 ≤ b → a + b = k + 1 →
        ∃ s : Set V,
          (a : ℕ∞) ≤ (G.induce s).chromaticNumber ∧
            (b : ℕ∞) ≤ (G.induce sᶜ).chromaticNumber

theorem target : statement := sorry

end Statements.Erdos628TihanyConjecture
