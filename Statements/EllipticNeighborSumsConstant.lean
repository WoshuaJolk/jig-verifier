import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.BigOperators.Fin

/-!
# EllipticNeighborSumsConstant

The balanced translate/anti-translate incidence has constant Abel sums on
both sides. This is the group-law mechanism making every graph neighborhood a
hyperplane section of one elliptic normal curve linear system.
-/

namespace Statements.EllipticNeighborSumsConstant

open scoped BigOperators

def cOffset {r N : ℕ} (c : Fin r) : ZMod (2 * N) :=
  (2 * c.val : ℕ)

def dOffset {r N : ℕ} (d : Fin r) : ZMod (2 * N) :=
  (2 * d.val + 1 + if d.val + 1 = r then 2 else 0 : ℕ)

abbrev statement : Prop :=
  ∀ r N : ℕ,
    (∀ i : ZMod (2 * N),
      (∑ c : Fin r, (i + cOffset c)) +
          (∑ d : Fin r, (-i + dOffset d)) =
        (∑ c : Fin r, cOffset c) + (∑ d : Fin r, dOffset d)) ∧
    (∀ j : ZMod (2 * N),
      (∑ c : Fin r, (j - cOffset c)) +
          (∑ d : Fin r, (dOffset d - j)) =
        -(∑ c : Fin r, cOffset c) + (∑ d : Fin r, dOffset d))

theorem target : statement := sorry

end Statements.EllipticNeighborSumsConstant
