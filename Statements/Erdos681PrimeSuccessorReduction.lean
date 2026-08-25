import Mathlib.Data.Nat.Prime.Basic

namespace Statements.Erdos681PrimeSuccessorReduction

def IsLeastPrimeFactor (p m : ℕ) : Prop :=
  p.Prime ∧ p ∣ m ∧ ∀ q : ℕ, q.Prime ∧ q ∣ m → p ≤ q

def IsComposite (m : ℕ) : Prop := 1 < m ∧ ¬m.Prime

/-- Outside the prime-successor bases, shift one already supplies the rough
composite required by Erdős 681. -/
abbrev statement : Prop :=
  ∀ n : ℕ, 2 ≤ n →
    (n + 1).Prime ∨
      ∃ k : ℕ, 0 < k ∧ IsComposite (n + k) ∧
        ∀ p : ℕ, IsLeastPrimeFactor p (n + k) → k ^ 2 < p

theorem target : statement := sorry

end Statements.Erdos681PrimeSuccessorReduction
