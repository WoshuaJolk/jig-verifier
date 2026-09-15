import Mathlib.Algebra.Order.Rearrangement
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

namespace Statements.J5P280DiscretePrefixEnergy

open Finset
noncomputable section

def cumulativeSum (f : ℕ → ℝ) (n : ℕ) : ℝ := ∑ i ∈ range n, f i

abbrev statement : Prop :=
  (∀ (f : ℕ → ℝ) (N : ℕ),
    (∑ j ∈ range N, (cumulativeSum f (j+1))^2 / (((j:ℝ)+1)*((j:ℝ)+2))) =
      2 * (∑ j ∈ range N, f j * (cumulativeSum f (j+1) / ((j:ℝ)+1))) -
      (∑ j ∈ range N, (f j)^2 / ((j:ℝ)+1)) -
      (cumulativeSum f N)^2 / ((N:ℝ)+1)) ∧
  (∀ (f : ℕ → ℝ) (N : ℕ),
    (∑ j ∈ range N, (cumulativeSum f (j+1) / ((j:ℝ)+1))^2) ≤
      16 * (∑ j ∈ range N, (f j)^2))

end
end Statements.J5P280DiscretePrefixEnergy
