import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Order.Filter.AtTopBot.CountablyGenerated
import Mathlib.Order.Lattice.Nat

open Filter Finset

namespace Statements.Erdos928ConsecutiveSmoothDensity

noncomputable def largestPrimeFactor (n : ℕ) : ℕ :=
  sSup {p : ℕ | p.Prime ∧ p ∣ n}

def smoothPair (α β : ℝ) (n : ℕ) : Prop :=
  (largestPrimeFactor n : ℝ) < (n : ℝ) ^ α ∧
    (largestPrimeFactor (n + 1) : ℝ) < ((n + 1 : ℕ) : ℝ) ^ β

noncomputable def smoothCount (α β : ℝ) (N : ℕ) : ℕ := by
  classical
  exact ((range N).filter (smoothPair α β)).card

/-- Erdős Problem 928: existence of the natural density. -/
abbrev statement : Prop :=
  ∀ α β : ℝ, 0 < α → α < 1 → 0 < β → β < 1 →
    ∃ d : ℝ,
      Tendsto
        (fun N : ℕ =>
          (smoothCount α β N : ℝ) / (N : ℝ))
        atTop (nhds d)

theorem target : statement := sorry

end Statements.Erdos928ConsecutiveSmoothDensity
