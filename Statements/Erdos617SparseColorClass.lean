import Mathlib.Data.Fintype.Card
import Mathlib.Data.Sym.Sym2
import Mathlib.Data.Finset.Filter
import Mathlib.Data.Sym.Card

namespace Statements.Erdos617SparseColorClass

/-- Sparse colour class forcing: if some colour class of an `r`-colouring of
`K_(r²+1)` has fewer than `r(r²-r+2)/2` edges, then the conclusion of Erdős 617
holds — there are `r+1` vertices whose induced complete graph omits a colour.
Consequently any counterexample colouring must use every colour on at least
`⌈r(r²-r+2)/2⌉` edges. -/
abbrev statement : Prop :=
  ∀ (r : ℕ), 3 ≤ r →
    ∀ {V : Type} [Fintype V] [DecidableEq V],
      Fintype.card V = r ^ 2 + 1 →
      ∀ coloring : Sym2 V → Fin r, ∀ c : Fin r,
        2 * (Finset.univ.filter
              fun e : Sym2 V => ¬ e.IsDiag ∧ coloring e = c).card
            < r * (r ^ 2 - r + 2) →
          ∃ (S : Finset V) (k : Fin r),
            S.card = r + 1 ∧
            ∀ u ∈ S, ∀ v ∈ S, u ≠ v → coloring s(u, v) ≠ k

theorem target : statement := sorry

end Statements.Erdos617SparseColorClass
