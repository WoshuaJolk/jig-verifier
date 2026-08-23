import Mathlib.Data.Rat.Cast.Defs
import Mathlib.Data.Nat.Cast.Order.Field

/-!
# ErdosStrausNonresidueMod7 — Erdős–Straus for n a quadratic nonresidue mod 7

## The claim

For every integer `n ≥ 2` with `n % 7 ∈ {3, 5, 6}` — the three quadratic nonresidues
modulo 7 — the fraction `4/n` is a sum of three unit fractions `1/x + 1/y + 1/z` with
`x, y, z` positive integers, not necessarily distinct.

These are the last classes of Mordell's covering set not yet on this board: with
`n ≢ 1 (mod 24)`, `n ≡ 2, 3 (mod 5)` and this statement, the only `n` not covered by a
congruence identity are those with `n mod 840` a square of a unit
(`1, 121, 169, 289, 361, 529`). None of the three classes here is covered by the earlier
reductions: `n = 73` (`≡ 3 mod 7`), `n = 313` (`≡ 5 mod 7`) and `n = 97` (`≡ 6 mod 7`)
are primes `≡ 1 (mod 24)`.

## What is NOT claimed

Nothing about `n ≡ 0, 1, 2, 4 (mod 7)`, the residues and zero. Nothing about distinctness
or size of `x, y, z`.
-/

namespace Statements.ErdosStrausNonresidueMod7

/-- The canonical proposition. -/
abbrev statement : Prop :=
  ∀ n : ℕ, 2 ≤ n → (n % 7 = 3 ∨ n % 7 = 5 ∨ n % 7 = 6) →
    ∃ x y z : ℕ, 0 < x ∧ 0 < y ∧ 0 < z ∧
      (4 : ℚ) / (n : ℚ) = 1 / (x : ℚ) + 1 / (y : ℚ) + 1 / (z : ℚ)

theorem target : statement := sorry

end Statements.ErdosStrausNonresidueMod7
