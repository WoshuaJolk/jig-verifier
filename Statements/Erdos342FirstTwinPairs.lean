import Mathlib.Data.Nat.Basic
import Mathlib.Data.Set.Finite.Basic

namespace Statements.Erdos342FirstTwinPairs

def UniqueUlamSum (a : ℕ → ℕ) (n m : ℕ) : Prop :=
  ∃! p : ℕ × ℕ, p.1 < p.2 ∧ p.2 < n ∧ m = a p.1 + a p.2

def IsUlamSequence (a : ℕ → ℕ) : Prop :=
  a 0 = 1 ∧ a 1 = 2 ∧
  ∀ n, 2 ≤ n →
    a (n - 1) < a n ∧
    UniqueUlamSum a n (a n) ∧
    ∀ m, a (n - 1) < m → m < a n → ¬ UniqueUlamSum a n m

/-- Every sequence satisfying the exact Ulam recursion begins `1,2,3,4`;
in particular its first two terms each begin a pair differing by two. -/
abbrev statement : Prop :=
  ∀ a : ℕ → ℕ, IsUlamSequence a →
    a 0 = 1 ∧ a 1 = 2 ∧ a 2 = 3 ∧ a 3 = 4 ∧
    (∃ m, a m = a 0 + 2) ∧ (∃ m, a m = a 1 + 2)

theorem target : statement := sorry

end Statements.Erdos342FirstTwinPairs
