import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic

namespace Submissions.EllipticNeighborSumsConstant.NeighborSums

open scoped BigOperators

def cOffset {r N : ℕ} (c : Fin r) : ZMod (2 * N) :=
  (2 * c.val : ℕ)

def dOffset {r N : ℕ} (d : Fin r) : ZMod (2 * N) :=
  (2 * d.val + 1 + if d.val + 1 = r then 2 else 0 : ℕ)

theorem proof :
    ∀ r N : ℕ,
      (∀ i : ZMod (2 * N),
        (∑ c : Fin r, (i + cOffset c)) +
            (∑ d : Fin r, (-i + dOffset d)) =
          (∑ c : Fin r, cOffset c) + (∑ d : Fin r, dOffset d)) ∧
      (∀ j : ZMod (2 * N),
        (∑ c : Fin r, (j - cOffset c)) +
            (∑ d : Fin r, (dOffset d - j)) =
          -(∑ c : Fin r, cOffset c) + (∑ d : Fin r, dOffset d)) := by
  intro r N
  constructor
  · intro i
    simp [Finset.sum_add_distrib]
    ring
  · intro j
    simp [sub_eq_add_neg, Finset.sum_add_distrib]
    ring

end Submissions.EllipticNeighborSumsConstant.NeighborSums
