import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Order.Interval.Finset.Nat

open scoped BigOperators
open Nat

namespace Submissions.Erdos1056CasesSevenAndEight.ExplicitWitnesses

def AllModProdEqualsOne (p : ℕ) {k : ℕ}
    (boundaries : Fin (k + 1) → ℕ) : Prop :=
  ∀ i : Fin k,
    (∏ n ∈ Finset.Ico (boundaries i.castSucc) (boundaries (i.castSucc + 1)), n) ≡ 1 [MOD p]

def HasSolution (k : ℕ) : Prop :=
  ∃ (p : ℕ), p.Prime ∧
    ∃ boundaries : Fin (k + 1) → ℕ,
      StrictMono boundaries ∧ AllModProdEqualsOne p boundaries

set_option maxRecDepth 10000 in
theorem proof : HasSolution 7 ∧ HasSolution 8 := by
  constructor
  · refine ⟨599, by decide, ![29, 51, 123, 184, 251, 290, 501, 540], by decide, ?_⟩
    unfold AllModProdEqualsOne
    decide
  · refine ⟨599, by decide, ![29, 51, 123, 184, 251, 290, 501, 540, 556], by decide, ?_⟩
    unfold AllModProdEqualsOne
    decide

end Submissions.Erdos1056CasesSevenAndEight.ExplicitWitnesses
