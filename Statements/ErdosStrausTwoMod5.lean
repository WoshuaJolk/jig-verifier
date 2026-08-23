import Mathlib.Data.Rat.Cast.Defs
import Mathlib.Data.Nat.Cast.Order.Field

/-!
# ErdosStrausTwoMod5 — Erdős–Straus for n ≡ 2 (mod 5)

## The claim

For every integer `n ≥ 2` with `n % 5 = 2`, the fraction `4/n` is a sum of three unit
fractions `1/x + 1/y + 1/z` with `x, y, z` positive integers, not necessarily distinct.

Together with `ErdosStrausThreeMod5`, this completes the two quadratic-nonresidue classes
modulo 5: the classes 1 and 4 (mod 5) are exactly the squares of units, the residues left
open by Mordell's congruence identities. The class is not covered by the
`n ≢ 1 (mod 24)` reduction: `n = 97`, a prime `≡ 1 (mod 24)`, satisfies `97 % 5 = 2`.

## What is NOT claimed

Nothing about `n ≡ 0, 1, 3, 4 (mod 5)`. Nothing about distinctness or size of `x, y, z`.
-/

namespace Statements.ErdosStrausTwoMod5

/-- The canonical proposition. -/
abbrev statement : Prop :=
  ∀ n : ℕ, 2 ≤ n → n % 5 = 2 → ∃ x y z : ℕ, 0 < x ∧ 0 < y ∧ 0 < z ∧
    (4 : ℚ) / (n : ℚ) = 1 / (x : ℚ) + 1 / (y : ℚ) + 1 / (z : ℚ)

theorem target : statement := sorry

end Statements.ErdosStrausTwoMod5
