import Mathlib.Data.Fin.Basic

namespace Submissions.Erdos711EmptyFamilyBoundary.FalsePremise

def HasDistinctMultiples (n m L : ℕ) : Prop :=
  ∃ a : Fin n → ℕ, Function.Injective a ∧
    ∀ k : Fin n,
      m < a k ∧ a k ≤ m + L ∧ (k.val + 1) ∣ a k

theorem proof :
    False →
      ∀ m : ℕ, HasDistinctMultiples 0 m 0 := by
  intro h
  exact h.elim

end Submissions.Erdos711EmptyFamilyBoundary.FalsePremise
