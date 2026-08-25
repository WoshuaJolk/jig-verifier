import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Order.Interval.Finset.Nat

open scoped BigOperators
open Nat

namespace Submissions.Erdos1056CasesNineAndTen.FalsePremise

def AllModProdEqualsOne (p : ℕ) {k : ℕ}
    (boundaries : Fin (k + 1) → ℕ) : Prop :=
  ∀ i : Fin k,
    (∏ n ∈ Finset.Ico (boundaries i.castSucc) (boundaries (i.castSucc + 1)), n) ≡ 1 [MOD p]

def HasSolution (k : ℕ) : Prop :=
  ∃ (p : ℕ), p.Prime ∧
    ∃ boundaries : Fin (k + 1) → ℕ,
      StrictMono boundaries ∧ AllModProdEqualsOne p boundaries

theorem proof : False → HasSolution 9 ∧ HasSolution 10 := by
  intro h
  exact h.elim

end Submissions.Erdos1056CasesNineAndTen.FalsePremise
