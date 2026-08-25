import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Order.Filter.AtTopBot.CountablyGenerated

namespace Statements.Erdos451SubexponentialBlocks

def GoodBlock (k n : ℕ) : Prop :=
  2 * k < n ∧
    ∀ p : ℕ, p.Prime → k < p → p < 2 * k →
      ¬p ∣ ∏ i ∈ Finset.range k, (n - (i + 1))

def LeastGoodBlock (k n : ℕ) : Prop :=
  GoodBlock k n ∧
    ∀ m : ℕ, GoodBlock k m → n ≤ m

/-- The surviving open half of Erdős Problem 451: the least admissible
block endpoint n_k should be subexponential in k. -/
abbrev statement : Prop :=
  ∀ nk : ℕ → ℕ, (∀ k, LeastGoodBlock k (nk k)) →
    Filter.Tendsto
      (fun k : ℕ => Real.log (nk k : ℝ) / (k : ℝ))
      Filter.atTop (nhds 0)

theorem target : statement := sorry

end Statements.Erdos451SubexponentialBlocks
