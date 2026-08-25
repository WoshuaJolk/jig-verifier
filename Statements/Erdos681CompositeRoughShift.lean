import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Order.Filter.AtTopBot.CountablyGenerated

open Filter

namespace Statements.Erdos681CompositeRoughShift

/-- `p` is the least prime factor of `m`. -/
def IsLeastPrimeFactor (p m : ℕ) : Prop :=
  p.Prime ∧ p ∣ m ∧ ∀ q : ℕ, q.Prime ∧ q ∣ m → p ≤ q

/-- `m` is composite. -/
def IsComposite (m : ℕ) : Prop := 1 < m ∧ ¬m.Prime

/-- Erdős Problem 681: every sufficiently large `n` has a positive shift `k`
for which `n + k` is composite and its least prime factor exceeds `k²`. -/
abbrev statement : Prop :=
  ∀ᶠ n : ℕ in atTop, ∃ k : ℕ, 0 < k ∧ IsComposite (n + k) ∧
    ∀ p : ℕ, IsLeastPrimeFactor p (n + k) → k ^ 2 < p

theorem target : statement := sorry

end Statements.Erdos681CompositeRoughShift
