import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Order.Interval.Finset.Nat

open scoped BigOperators
open Nat

/-!
# Erdős problem 1056: the cases k = 9 and k = 10
-/

namespace Statements.Erdos1056CasesNineAndTen

def AllModProdEqualsOne (p : ℕ) {k : ℕ}
    (boundaries : Fin (k + 1) → ℕ) : Prop :=
  ∀ i : Fin k,
    (∏ n ∈ Finset.Ico (boundaries i.castSucc) (boundaries (i.castSucc + 1)), n) ≡ 1 [MOD p]

def HasSolution (k : ℕ) : Prop :=
  ∃ (p : ℕ), p.Prime ∧
    ∃ boundaries : Fin (k + 1) → ℕ,
      StrictMono boundaries ∧ AllModProdEqualsOne p boundaries

abbrev statement : Prop := HasSolution 9 ∧ HasSolution 10

theorem target : statement := sorry

end Statements.Erdos1056CasesNineAndTen
