import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Sym.Sym2

namespace Statements.Erdos617TwoCliquePartitionedColors

/-- No `r`-colouring of the edges of `K_n` with `n ≥ r² + 1` has two distinct
colours `c₁ ≠ c₂` whose colour classes each admit a spanning partition of the
vertices into at most `r` monochromatic cliques. Consequently, in any
counterexample to Erdős problem 617 at most one colour class can be a union of
`r` spanning cliques, even though every colour class must have independence
number at most `r`. -/
abbrev statement : Prop :=
  ∀ (r : ℕ), 2 ≤ r →
    ∀ {V : Type} [Fintype V] [DecidableEq V],
      r ^ 2 + 1 ≤ Fintype.card V →
      ∀ coloring : Sym2 V → Fin r,
        ∀ c₁ c₂ : Fin r, c₁ ≠ c₂ →
          ¬ ((∃ P : V → Fin r,
                ∀ u v : V, u ≠ v → P u = P v → coloring s(u, v) = c₁) ∧
             (∃ P : V → Fin r,
                ∀ u v : V, u ≠ v → P u = P v → coloring s(u, v) = c₂))

theorem target : statement := sorry

end Statements.Erdos617TwoCliquePartitionedColors
