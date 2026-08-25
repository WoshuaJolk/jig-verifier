import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Set.Card

namespace Statements.Erdos849EveryBinomialMultiplicity

/-- Lower-half Pascal-triangle occurrences of `a`, counted as `(n,k)` solutions. -/
def occurrences (a : ℕ) : Set (ℕ × ℕ) :=
  {(n, k) | 1 ≤ k ∧ 2 * k ≤ n ∧ Nat.choose n k = a}

/-- Erdős Problem 849: every positive finite multiplicity occurs among the
nontrivial entries in the lower half of Pascal's triangle. -/
abbrev statement : Prop :=
  ∀ t : ℕ, 1 ≤ t → ∃ a : ℕ, (occurrences a).ncard = t

theorem target : statement := sorry

end Statements.Erdos849EveryBinomialMultiplicity
