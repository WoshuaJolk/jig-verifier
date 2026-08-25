import Mathlib.Data.Nat.Prime.Basic

namespace Statements.Erdos279DepthOneCover

/-- The elementary depth-one boundary case of Erdős Problem 279. -/
abbrev statement : Prop :=
  ∃ a : ℕ → ℕ, ∃ N : ℕ,
    (∀ p : ℕ, p.Prime → a p < p) ∧
    ∀ n ≥ N, ∃ p : ℕ, ∃ t ≥ 1,
      p.Prime ∧ n = a p + t * p

theorem target : statement := sorry

end Statements.Erdos279DepthOneCover
