import Mathlib.Data.Nat.Prime.Basic

namespace Statements.Erdos375GrimmConjecture

/-- Grimm's conjecture: every block of consecutive composite integers admits
distinct prime representatives, one dividing each member of the block. -/
abbrev statement : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ k : ℕ,
    (∀ i < k, ¬ (n + i + 1).Prime) →
      ∃ p : Fin k → ℕ, Function.Injective p ∧
        ∀ i, (p i).Prime ∧ p i ∣ n + i + 1

theorem target : statement := sorry

end Statements.Erdos375GrimmConjecture
