import Mathlib.Data.Fin.Basic

namespace Statements.Erdos711EmptyFamilyBoundary

def HasDistinctMultiples (n m L : ℕ) : Prop :=
  ∃ a : Fin n → ℕ, Function.Injective a ∧
    ∀ k : Fin n,
      m < a k ∧ a k ≤ m + L ∧ (k.val + 1) ∣ a k

abbrev statement : Prop :=
  ∀ m : ℕ, HasDistinctMultiples 0 m 0

theorem target : statement := sorry

end Statements.Erdos711EmptyFamilyBoundary
