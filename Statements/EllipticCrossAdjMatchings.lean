import Mathlib.Data.Complex.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.BigOperators.Fin

/-!
# EllipticCrossAdjMatchings

The explicit translate/anti-translate classes used by the elliptic seed are
genuine edge-disjoint perfect matchings. For `r+2 ≤ N`, the even offsets and
odd offsets are internally distinct modulo `2N`, and parity prevents a
translate edge from colliding with an anti-translate edge.
-/

namespace Statements.EllipticCrossAdjMatchings

def cOffset {r N : ℕ} (c : Fin r) : ZMod (2 * N) :=
  (2 * c.val : ℕ)

def dOffset {r N : ℕ} (d : Fin r) : ZMod (2 * N) :=
  (2 * d.val + 1 + if d.val + 1 = r then 2 else 0 : ℕ)

abbrev statement : Prop :=
  ∀ r N : ℕ, 2 ≤ r → r + 2 ≤ N →
    (Function.Injective (cOffset : Fin r → ZMod (2 * N))) ∧
    (Function.Injective (dOffset : Fin r → ZMod (2 * N))) ∧
    (∀ i : ZMod (2 * N),
      Function.Injective (fun c : Fin r => i + cOffset c) ∧
      Function.Injective (fun d : Fin r => -i + dOffset d) ∧
      (∀ (c d : Fin r), i + cOffset c ≠ -i + dOffset d))

theorem target : statement := sorry

end Statements.EllipticCrossAdjMatchings
