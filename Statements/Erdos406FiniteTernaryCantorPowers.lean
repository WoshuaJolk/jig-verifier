import Mathlib.Data.Nat.Digits.Lemmas
import Mathlib.Data.Set.Finite.Basic

namespace Statements.Erdos406FiniteTernaryCantorPowers

/-- A natural number is a power of two and has no ternary digit `2`. -/
def good (n : ℕ) : Prop :=
  (∃ k : ℕ, n = 2 ^ k) ∧ Nat.digits 3 n ⊆ [0, 1]

/-- Erdős Problem 406: only finitely many powers of two have ternary expansions using solely the digits zero and one. -/
abbrev statement : Prop :=
  {n : ℕ | good n}.Finite

theorem target : statement := sorry

end Statements.Erdos406FiniteTernaryCantorPowers
