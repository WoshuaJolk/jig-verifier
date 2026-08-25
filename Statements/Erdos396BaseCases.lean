import Mathlib.Data.Nat.Choose.Central

/-!
# First two block lengths in Erdős problem 396

The conjecture holds for `k = 0,1`, witnessed respectively by `n = 1,2`.
-/

open Nat

namespace Statements.Erdos396BaseCases

abbrev statement : Prop :=
  ∀ k : ℕ, k ≤ 1 → ∃ n : ℕ, descFactorial n (k + 1) ∣ centralBinom n

theorem target : statement := sorry

end Statements.Erdos396BaseCases
