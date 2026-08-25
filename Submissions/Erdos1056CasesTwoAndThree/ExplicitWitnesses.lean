import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Order.Interval.Finset.Nat

open scoped BigOperators
open Nat

namespace Submissions.Erdos1056CasesTwoAndThree.ExplicitWitnesses

def AllModProdEqualsOne (p : ℕ) {k : ℕ}
    (boundaries : Fin (k + 1) → ℕ) : Prop :=
  ∀ i : Fin k,
    (∏ n ∈ Finset.Ico (boundaries i.castSucc) (boundaries (i.castSucc + 1)), n) ≡ 1 [MOD p]

def HasSolution (k : ℕ) : Prop :=
  ∃ (p : ℕ), p.Prime ∧
    ∃ boundaries : Fin (k + 1) → ℕ,
      StrictMono boundaries ∧ AllModProdEqualsOne p boundaries

theorem proof : HasSolution 2 ∧ HasSolution 3 := by
  constructor
  · refine ⟨11, by decide, ![3, 5, 8], by decide, ?_⟩
    unfold AllModProdEqualsOne
    decide
  · refine ⟨17, by decide, ![2, 6, 12, 16], by decide, ?_⟩
    unfold AllModProdEqualsOne
    decide

end Submissions.Erdos1056CasesTwoAndThree.ExplicitWitnesses
