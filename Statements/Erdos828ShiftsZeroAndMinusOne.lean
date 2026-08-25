import Mathlib.Data.Nat.Totient
import Mathlib.Data.Nat.PrimeFin

/-!
# Two infinite shift families for Erdős problem 828

The conjecture holds for shifts zero and negative one.
-/

namespace Statements.Erdos828ShiftsZeroAndMinusOne

abbrev statement : Prop :=
  Set.Infinite {n : ℕ | (Nat.totient n : ℤ) ∣ (n : ℤ)} ∧
    Set.Infinite {n : ℕ | (Nat.totient n : ℤ) ∣ (n : ℤ) - 1}

theorem target : statement := sorry

end Statements.Erdos828ShiftsZeroAndMinusOne
