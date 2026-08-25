import Mathlib.Data.Finset.Card
import Mathlib.Data.Sym.Sym2

namespace Statements.Erdos617SingletonMissesColor

/-- Every colouring of the edges on a nonempty finite vertex type has a
one-vertex induced subgraph on which one of two colours is absent. -/
abbrev statement : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V], Nonempty V →
    ∀ coloring : Sym2 V → Fin 2,
      ∃ (S : Finset V) (k : Fin 2),
        S.card = 1 ∧
        ∀ u ∈ S, ∀ v ∈ S, u ≠ v → coloring s(u, v) ≠ k

theorem target : statement := sorry

end Statements.Erdos617SingletonMissesColor
