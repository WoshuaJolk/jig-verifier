import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Order.Interval.Finset.Nat

open scoped BigOperators
open Nat

namespace Submissions.Erdos1056CasesNineAndTen.ExplicitWitnesses

def AllModProdEqualsOne (p : ℕ) {k : ℕ}
    (boundaries : Fin (k + 1) → ℕ) : Prop :=
  ∀ i : Fin k,
    (∏ n ∈ Finset.Ico (boundaries i.castSucc) (boundaries (i.castSucc + 1)), n) ≡ 1 [MOD p]

def HasSolution (k : ℕ) : Prop :=
  ∃ (p : ℕ), p.Prime ∧
    ∃ boundaries : Fin (k + 1) → ℕ,
      StrictMono boundaries ∧ AllModProdEqualsOne p boundaries

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem proof : HasSolution 9 ∧ HasSolution 10 := by
  constructor
  · refine ⟨3011, by decide,
      ![1, 2, 612, 724, 750, 806, 2206, 2262, 2288, 2400],
      by decide, ?_⟩
    unfold AllModProdEqualsOne
    decide
  · refine ⟨3011, by decide,
      ![1, 2, 612, 724, 750, 806, 2206, 2262, 2288, 2400, 3010],
      by decide, ?_⟩
    unfold AllModProdEqualsOne
    decide

end Submissions.Erdos1056CasesNineAndTen.ExplicitWitnesses
