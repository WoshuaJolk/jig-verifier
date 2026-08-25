import Mathlib.Data.Nat.Prime.Basic

namespace Statements.Erdos676ModFourHalf

/-- The two short residue classes modulo four are represented using the prime two. -/
abbrev statement : Prop :=
  ∀ n : ℕ, 4 ≤ n → n % 4 < 2 →
    ∃ p a b : ℕ,
      p.Prime ∧ 1 ≤ a ∧ b < p ∧ n = a * p ^ 2 + b

theorem target : statement := sorry

end Statements.Erdos676ModFourHalf
