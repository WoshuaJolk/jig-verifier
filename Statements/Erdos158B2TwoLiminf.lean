import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Set.Card
import Mathlib.Order.LiminfLimsup
import Mathlib.Topology.Instances.Nat

namespace Statements.Erdos158B2TwoLiminf

open Filter Real

/-- `A` is a `B₂[g]` set when every integer has at most `g`
unordered two-term representations from `A`. -/
def B2 (g : ℕ) (A : Set ℕ) : Prop :=
  ∀ n, {x : ℕ × ℕ |
    x.1 + x.2 = n ∧ x.1 ≤ x.2 ∧ x.1 ∈ A ∧ x.2 ∈ A}.encard ≤ g

/-- Erdős Problem 158: every infinite `B₂[2]` set has normalized
counting function with liminf zero. -/
abbrev statement : Prop :=
  ∀ A : Set ℕ, A.Infinite → B2 2 A →
    liminf
      (fun N : ℕ =>
        ((A ∩ Set.Iio N).ncard : ℝ) * (N : ℝ) ^ (-1 / 2 : ℝ))
      atTop = 0

theorem target : statement := sorry

end Statements.Erdos158B2TwoLiminf
