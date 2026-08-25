import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Set.Card
import Mathlib.Order.Filter.AtTopBot.CountablyGenerated

open Filter
open scoped Real

namespace Statements.Erdos340LargeEpsilon

/-- For any sequence containing one, the Erdős 340 estimate is automatic when `ε ≥ 1/2`. -/
abbrev statement : Prop :=
  ∀ f : ℕ → ℕ, f 0 = 1 →
    ∀ ε : ℝ, (1 : ℝ) / 2 ≤ ε →
      (fun n : ℕ ↦ √(n : ℝ) / (n : ℝ) ^ ε) =O[atTop]
        (fun n : ℕ ↦ ((Set.range f ∩ Set.Icc 1 n).ncard : ℝ))

theorem target : statement := sorry

end Statements.Erdos340LargeEpsilon
