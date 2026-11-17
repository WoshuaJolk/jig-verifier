import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex

namespace Statements.Erdos628TihanyUpToFour

/-- The Erdős--Lovász Tihany conjecture for chromatic number `k ≤ 4`: the pairs
`(a,b) = (2,2)` at `k = 3` and `(2,3)`, `(3,2)` at `k = 4` (Brown and Jung, 1969). Same shape
as the root `Erdos628TihanyConjecture`, with the single extra hypothesis `k ≤ 4`. For `k ≤ 2`
no admissible `a, b` exist. -/
abbrev statement : Prop :=
  ∀ (V : Type) [Fintype V] (G : SimpleGraph V) (k : ℕ),
    k ≤ 4 →
    G.chromaticNumber = (k : ℕ∞) → G.CliqueFree k →
      ∀ a b : ℕ, 2 ≤ a → 2 ≤ b → a + b = k + 1 →
        ∃ s : Set V,
          (a : ℕ∞) ≤ (G.induce s).chromaticNumber ∧
            (b : ℕ∞) ≤ (G.induce sᶜ).chromaticNumber

theorem target : statement := sorry

end Statements.Erdos628TihanyUpToFour
