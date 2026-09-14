import Mathlib.Combinatorics.SimpleGraph.Paths

namespace Statements.J4P399PairSuppression

open SimpleGraph

abbrev statement : Prop :=
  ∀ (U V : Type) (K : SimpleGraph U) (G : SimpleGraph V)
    (vertex : U → V) (middle : K.Dart → V),
    Function.Injective vertex →
    (∀ d, G.Adj (vertex d.fst) (middle d)) →
    (∀ d, G.Adj (middle d) (vertex d.snd)) →
    (∀ d u, middle d ≠ vertex u) →
    (∀ d e, middle d = middle e → d.edge = e.edge) →
    ∀ (u : U) (c : K.Walk u u), c.IsCycle →
      ∃ d : G.Walk (vertex u) (vertex u), d.IsCycle ∧ d.length = 2 * c.length

end Statements.J4P399PairSuppression
