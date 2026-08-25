import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Data.Fin.Basic

namespace Statements.Erdos743OrderTwo

/-- The Gyárfás tree-packing conjecture at its first admissible order:
the unique two-vertex tree packs the unique edge of `K₂`. -/
abbrev statement : Prop :=
  ∀ T : (i : Fin (2 - 1)) → SimpleGraph (Fin (i.val + 2)),
    (∀ i, (T i).IsTree) →
    ∃ f : (i : Fin (2 - 1)) → Fin (i.val + 2) ↪ Fin 2,
      ∀ u v : Fin 2, u ≠ v →
        ∃! i : Fin (2 - 1),
          ∃ a b : Fin (i.val + 2), (T i).Adj a b ∧
            ((f i a = u ∧ f i b = v) ∨
             (f i a = v ∧ f i b = u))

theorem target : statement := sorry

end Statements.Erdos743OrderTwo
