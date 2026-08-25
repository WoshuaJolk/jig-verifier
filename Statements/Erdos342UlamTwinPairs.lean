import Mathlib.Data.Nat.Basic
import Mathlib.Data.Set.Finite.Basic

namespace Statements.Erdos342UlamTwinPairs

def UniqueUlamSum (a : ℕ → ℕ) (n m : ℕ) : Prop :=
  ∃! p : ℕ × ℕ, p.1 < p.2 ∧ p.2 < n ∧ m = a p.1 + a p.2

def IsUlamSequence (a : ℕ → ℕ) : Prop :=
  a 0 = 1 ∧ a 1 = 2 ∧
  ∀ n, 2 ≤ n →
    a (n - 1) < a n ∧
    UniqueUlamSum a n (a n) ∧
    ∀ m, a (n - 1) < m → m < a n → ¬ UniqueUlamSum a n m

/-- Erdős problem 342(i): infinitely many pairs of Ulam numbers differ by
two. -/
abbrev statement : Prop :=
  ∀ a : ℕ → ℕ, IsUlamSequence a →
    Set.Infinite {n : ℕ | ∃ m, a m = a n + 2}

theorem target : statement := sorry

end Statements.Erdos342UlamTwinPairs
