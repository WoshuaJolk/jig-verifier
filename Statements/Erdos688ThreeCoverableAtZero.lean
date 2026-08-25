import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Nat.Prime.Basic

namespace Statements.Erdos688ThreeCoverableAtZero

def Coverable (n : ℕ) (ε : ℝ) : Prop :=
  ∃ a : ℕ → ℕ, ∀ m : ℕ, 1 ≤ m → m ≤ n →
    ∃ p : ℕ, p.Prime ∧ (n : ℝ) ^ ε < p ∧ p ≤ n ∧ a p ≡ m [MOD p]

/-- The interval `[1,3]` can be covered by residue classes for primes above `3^0`. -/
abbrev statement : Prop :=
  Coverable 3 0

theorem target : statement := sorry

end Statements.Erdos688ThreeCoverableAtZero
