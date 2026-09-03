import Mathlib.Data.Nat.Prime.Basic

namespace Statements.Erdos375LeTwo

/-- Grimm's conjecture restricted to block length at most 2: this range is noted as
"trivial" on erdosproblems.com/375. -/
abbrev statement : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ k : ℕ, k ≤ 2 →
    (∀ i < k, ¬ (n + i + 1).Prime) →
      ∃ p : Fin k → ℕ, Function.Injective p ∧
        ∀ i, (p i).Prime ∧ p i ∣ n + i + 1

theorem target : statement := sorry

end Statements.Erdos375LeTwo
