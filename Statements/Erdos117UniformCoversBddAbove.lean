import Mathlib.Data.Finset.Card
import Mathlib.Order.Bounds.Basic
import Mathlib.Order.Lattice.Nat

namespace Statements.Erdos117UniformCoversBddAbove

/--
Minimum/supremum bridge used when assembling arXiv:2608.20507v1,
Theorem 2.2. The first conjunct turns any finite cover construction into an
upper bound for its least cardinality. The second turns uniform pointwise
bounds into the canonical root's explicit `BddAbove` guard.
-/
abbrev statement : Prop :=
  (∀ (α : Type) (coverOK : Finset α → Prop) (bound : ℕ),
      (∃ C : Finset α, coverOK C ∧ C.card ≤ bound) →
      sInf {k : ℕ | ∃ C : Finset α, C.card = k ∧ coverOK C} ≤ bound) ∧
  ∀ (ι : Type) (value : ι → ℕ) (admissible : ι → Prop) (bound : ℕ),
    (∀ i : ι, admissible i → value i ≤ bound) →
    BddAbove {k : ℕ | ∃ i : ι, admissible i ∧ value i = k}

theorem target : statement := by
  sorry

end Statements.Erdos117UniformCoversBddAbove
