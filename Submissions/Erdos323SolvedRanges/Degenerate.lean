import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Set.Card
import Mathlib.Order.Filter.AtTopBot.Basic

open Filter
open scoped Asymptotics

namespace Submissions.Erdos323SolvedRanges.Degenerate

noncomputable def f (k m x : ℕ) : ℕ :=
  {n : ℕ | n ≤ x ∧ ∃ v : Fin m → ℕ, n = ∑ i, v i ^ k}.ncard

theorem proof : False →
    (∀ ε > (0 : ℝ),
      (fun x : ℕ => (x : ℝ) ^ (1 - ε)) =O[atTop]
        (fun x : ℕ => (f 1 1 x : ℝ))) ∧
    (∀ k ≥ 1, ∀ ε ≥ (1 : ℝ),
      (fun x : ℕ => (x : ℝ) ^ (1 - ε)) =O[atTop]
        (fun x : ℕ => (f k k x : ℝ))) :=
  False.elim

end Submissions.Erdos323SolvedRanges.Degenerate
