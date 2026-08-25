import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Set.Card
import Mathlib.Order.Filter.AtTopBot.Basic

open Filter
open scoped Asymptotics

namespace Statements.Erdos323WaringLowerBound

noncomputable def f (k m x : ℕ) : ℕ :=
  {n : ℕ | n ≤ x ∧ ∃ v : Fin m → ℕ, n = ∑ i, v i ^ k}.ncard

/-- Erdős Problem 323(i). -/
abbrev statement : Prop :=
  ∀ k ≥ 1, ∀ ε > (0 : ℝ),
    (fun x : ℕ => (x : ℝ) ^ (1 - ε)) =O[atTop]
      (fun x : ℕ => (f k k x : ℝ))

theorem target : statement := sorry

end Statements.Erdos323WaringLowerBound
