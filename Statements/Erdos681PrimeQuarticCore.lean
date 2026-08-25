import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Order.Filter.AtTopBot.CountablyGenerated

open Filter

namespace Statements.Erdos681PrimeQuarticCore

def IsLeastPrimeFactor (p m : ℕ) : Prop :=
  p.Prime ∧ p ∣ m ∧ ∀ q : ℕ, q.Prime ∧ q ∣ m → p ≤ q

def IsComposite (m : ℕ) : Prop := 1 < m ∧ ¬m.Prime

def Witness (n k : ℕ) : Prop :=
  0 < k ∧ IsComposite (n + k) ∧
    ∀ p : ℕ, IsLeastPrimeFactor p (n + k) → k ^ 2 < p

/-- The full Erdős 681 conjecture is equivalent to its prime-successor
hard core, with every witness restricted to the necessary quartic window. -/
abbrev statement : Prop :=
  (∀ᶠ n : ℕ in atTop, ∃ k : ℕ, Witness n k) ↔
    ∀ᶠ n : ℕ in atTop, (n + 1).Prime →
      ∃ k : ℕ, Witness n k ∧ (k ^ 2) ^ 2 < n + k

theorem target : statement := sorry

end Statements.Erdos681PrimeQuarticCore
