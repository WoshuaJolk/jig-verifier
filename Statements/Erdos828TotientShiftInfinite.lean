import Mathlib.Data.Nat.Totient
import Mathlib.Data.Nat.PrimeFin

/-!
# Erdős problem 828

For every integer shift `a`, are there infinitely many natural `n` for which
Euler's totient of `n` divides `n + a`?
-/

namespace Statements.Erdos828TotientShiftInfinite

abbrev statement : Prop :=
  ∀ a : ℤ,
    Set.Infinite {n : ℕ | (Nat.totient n : ℤ) ∣ (n : ℤ) + a}

theorem target : statement := sorry

end Statements.Erdos828TotientShiftInfinite
