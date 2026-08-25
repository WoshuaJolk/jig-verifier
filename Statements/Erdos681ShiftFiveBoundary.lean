import Mathlib.Data.Nat.Prime.Basic

namespace Statements.Erdos681ShiftFiveBoundary

def IsLeastPrimeFactor (p m : ℕ) : Prop :=
  p.Prime ∧ p ∣ m ∧ ∀ q : ℕ, q.Prime ∧ q ∣ m → p ≤ q

def IsComposite (m : ℕ) : Prop := 1 < m ∧ ¬m.Prime

/-- At `n = 5`, the shift `k = 1` gives the composite `6`, whose least
prime factor exceeds `k²`. -/
abbrev statement : Prop :=
  ∃ k : ℕ, 0 < k ∧ IsComposite (5 + k) ∧
    ∀ p : ℕ, IsLeastPrimeFactor p (5 + k) → k ^ 2 < p

theorem target : statement := sorry

end Statements.Erdos681ShiftFiveBoundary
