import Mathlib.Data.Rat.Cast.Defs
import Mathlib.Data.Nat.Cast.Order.Field
import Mathlib.Data.Nat.Prime.Basic

/-!
# ErdosStrausMordellReduction — Erdős–Straus reduced to primes that are squares mod 840

## The claim

The Erdős–Straus conjecture is EQUIVALENT to its restriction to primes `p` satisfying all
three of

* `p ≡ 1 (mod 24)`,
* `p ≡ 1 or 4 (mod 5)` (a quadratic residue mod 5),
* `p ≡ 1, 2 or 4 (mod 7)` (a quadratic residue mod 7).

By CRT these conditions say exactly that `p mod 840` is the square of a unit, i.e.
`p ≡ 1, 121, 169, 289, 361, 529 (mod 840)` — the residue classes Mordell's congruence
identities leave open. The right-hand side of the equivalence is verbatim the proposition
of `Statements.ErdosStraus.statement`, so proving the restricted claim proves the
conjecture.

## What is NOT claimed

Neither side is asserted. This is a reduction, not a proof. The restricted set is nonempty:
`1009` is prime and `1009 ≡ 169 = 13² (mod 840)`. No claim is made about the divisor
conditions of the sharper reductions (`ErdosStrausSharpReduction`,
`ErdosStrausShiftReduction`), which cut along a different, non-congruence axis.
-/

namespace Statements.ErdosStrausMordellReduction

/-- The canonical proposition. -/
abbrev statement : Prop :=
  (∀ p : ℕ, p.Prime → p % 24 = 1 → (p % 5 = 1 ∨ p % 5 = 4) →
      (p % 7 = 1 ∨ p % 7 = 2 ∨ p % 7 = 4) →
      ∃ x y z : ℕ, 0 < x ∧ 0 < y ∧ 0 < z ∧
        (4 : ℚ) / (p : ℚ) = 1 / (x : ℚ) + 1 / (y : ℚ) + 1 / (z : ℚ)) ↔
    (∀ n : ℕ, 2 ≤ n → ∃ x y z : ℕ, 0 < x ∧ 0 < y ∧ 0 < z ∧
        (4 : ℚ) / (n : ℚ) = 1 / (x : ℚ) + 1 / (y : ℚ) + 1 / (z : ℚ))

theorem target : statement := sorry

end Statements.ErdosStrausMordellReduction
