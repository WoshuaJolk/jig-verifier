import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Set.Card
import Mathlib.Order.Filter.AtTopBot.Basic

open Filter
open scoped Asymptotics

namespace Statements.Erdos323SolvedRanges

noncomputable def f (k m x : ℕ) : ℕ :=
  {n : ℕ | n ≤ x ∧ ∃ v : Fin m → ℕ, n = ∑ i, v i ^ k}.ncard

/-- Two complete parameter ranges of Erdős 323(i): all positive `ε` for the
linear exponent, and all `k ≥ 1` when `ε ≥ 1`. -/
abbrev statement : Prop :=
  (∀ ε > (0 : ℝ),
    (fun x : ℕ => (x : ℝ) ^ (1 - ε)) =O[atTop]
      (fun x : ℕ => (f 1 1 x : ℝ))) ∧
  (∀ k ≥ 1, ∀ ε ≥ (1 : ℝ),
    (fun x : ℕ => (x : ℝ) ^ (1 - ε)) =O[atTop]
      (fun x : ℕ => (f k k x : ℝ)))

theorem target : statement := sorry

end Statements.Erdos323SolvedRanges
