import Mathlib.Data.Finset.Card
import Mathlib.Order.Bounds.Basic
import Mathlib.Order.Lattice.Nat

namespace Submissions.Erdos117PolymorphicMinimaBddAbove.Control

/-- Must-fail anti-restatement control with an intentional extra premise. -/
theorem proof :
    False →
      (∀ (α : Type*) (coverOK : Finset α → Prop) (bound : ℕ),
          (∃ C : Finset α, coverOK C ∧ C.card ≤ bound) →
          sInf {k : ℕ | ∃ C : Finset α, C.card = k ∧ coverOK C} ≤ bound) ∧
      ∀ (ι : Type*) (value : ι → ℕ) (admissible : ι → Prop) (bound : ℕ),
        (∀ i : ι, admissible i → value i ≤ bound) →
        BddAbove {k : ℕ | ∃ i : ι, admissible i ∧ value i = k} := by
  intro h
  exact h.elim

end Submissions.Erdos117PolymorphicMinimaBddAbove.Control
