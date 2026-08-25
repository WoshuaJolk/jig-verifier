import Mathlib.Data.Fintype.Card
import Mathlib.Data.Sym.Sym2

namespace Statements.Erdos617BalancedColoring

/-- Erdős problem 617: no balanced `r`-colouring of `K_(r²+1)` exists for `r ≥ 3`. -/
abbrev statement : Prop :=
  ∀ (r : ℕ), r ≥ 3 →
    ∀ {V : Type} [Fintype V] [DecidableEq V],
      Fintype.card V = r ^ 2 + 1 →
      ∀ coloring : Sym2 V → Fin r,
        ∃ (S : Finset V) (k : Fin r),
          S.card = r + 1 ∧
          ∀ u ∈ S, ∀ v ∈ S, u ≠ v → coloring s(u, v) ≠ k

theorem target : statement := sorry

end Statements.Erdos617BalancedColoring
