import Mathlib.Data.Nat.Choose.Central

/-!
# Erdős problem 396

For every block length, does some descending block of consecutive positive
integers divide the corresponding central binomial coefficient?
-/

open Nat

namespace Statements.Erdos396DescendingBlockCentralBinom

abbrev statement : Prop :=
  ∀ k : ℕ, ∃ n : ℕ, descFactorial n (k + 1) ∣ centralBinom n

theorem target : statement := sorry

end Statements.Erdos396DescendingBlockCentralBinom
