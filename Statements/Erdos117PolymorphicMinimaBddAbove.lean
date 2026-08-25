import Mathlib.Data.Finset.Card
import Mathlib.Order.Bounds.Basic
import Mathlib.Order.Lattice.Nat

namespace Statements.Erdos117PolymorphicMinimaBddAbove

/--
Universe-polymorphic minimum/supremum bridge used when assembling
arXiv:2608.20507v1, Theorem 2.2. The `Type*` binders are required because the
canonical root's type of packaged groups lives one universe above its carriers.
-/
abbrev statement : Prop :=
  (∀ (α : Type*) (coverOK : Finset α → Prop) (bound : ℕ),
      (∃ C : Finset α, coverOK C ∧ C.card ≤ bound) →
      sInf {k : ℕ | ∃ C : Finset α, C.card = k ∧ coverOK C} ≤ bound) ∧
  ∀ (ι : Type*) (value : ι → ℕ) (admissible : ι → Prop) (bound : ℕ),
    (∀ i : ι, admissible i → value i ≤ bound) →
    BddAbove {k : ℕ | ∃ i : ι, admissible i ∧ value i = k}

theorem target : statement := by
  sorry

end Statements.Erdos117PolymorphicMinimaBddAbove
