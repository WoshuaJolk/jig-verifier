import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Card
import Mathlib.Data.Sym.Sym2

namespace Statements.Erdos617NoBalancedColoring

/-- Erdős Problem 617: every `r`-colouring of the edges of `K_(r²+1)`
has an `(r+1)`-vertex induced complete graph on which some colour is absent. -/
abbrev statement : Prop :=
  ∀ (r : ℕ), 3 ≤ r →
    ∀ (V : Type) [Fintype V] [DecidableEq V],
      Fintype.card V = r ^ 2 + 1 →
      ∀ coloring : Sym2 V → Fin r,
        ∃ (S : Finset V) (k : Fin r),
          S.card = r + 1 ∧
          ∀ u ∈ S, ∀ v ∈ S, u ≠ v → coloring s(u, v) ≠ k

theorem target : statement := sorry

end Statements.Erdos617NoBalancedColoring
