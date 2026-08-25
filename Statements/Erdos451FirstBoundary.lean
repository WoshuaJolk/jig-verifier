import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.Prime.Basic

namespace Statements.Erdos451FirstBoundary

def GoodBlock (k n : ℕ) : Prop :=
  2 * k < n ∧
    ∀ p : ℕ, p.Prime → k < p → p < 2 * k →
      ¬p ∣ ∏ i ∈ Finset.range k, (n - (i + 1))

def LeastGoodBlock (k n : ℕ) : Prop :=
  GoodBlock k n ∧
    ∀ m : ℕ, GoodBlock k m → n ≤ m

abbrev statement : Prop := LeastGoodBlock 1 3

theorem target : statement := sorry

end Statements.Erdos451FirstBoundary
