import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Order.Interval.Finset.Nat

/-!
# Erdős problem 1056

For every number of consecutive intervals, can all interval products be one
modulo a suitable prime?
-/

open scoped BigOperators
open Nat

namespace Statements.Erdos1056ConsecutiveProducts

def AllModProdEqualsOne (p : ℕ) {k : ℕ}
    (boundaries : Fin (k + 1) → ℕ) : Prop :=
  ∀ i : Fin k,
    (∏ n ∈ Finset.Ico (boundaries i.castSucc) (boundaries (i.castSucc + 1)), n) ≡ 1 [MOD p]

abbrev statement : Prop :=
  ∀ k : ℕ, k ≥ 2 →
    ∃ (p : ℕ), p.Prime ∧
      ∃ boundaries : Fin (k + 1) → ℕ,
        StrictMono boundaries ∧ AllModProdEqualsOne p boundaries

theorem target : statement := sorry

end Statements.Erdos1056ConsecutiveProducts
