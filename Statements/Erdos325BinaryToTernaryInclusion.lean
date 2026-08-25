import Mathlib.Data.Set.Card
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Order.Interval.Set.Infinite

namespace Statements.Erdos325BinaryToTernaryInclusion

def IsSumTwoPower (k n : ℕ) : Prop :=
  ∃ a b, a ^ k + b ^ k = n

def IsSumThreePower (k n : ℕ) : Prop :=
  ∃ a b c, a ^ k + b ^ k + c ^ k = n

/-- Binary sums embed into ternary sums by adjoining the zero `k`th power,
so their bounded counting functions are ordered. -/
abbrev statement : Prop :=
  ∀ k x : ℕ, 0 < k →
    {n ∈ Set.Iic x | IsSumTwoPower k n}.ncard ≤
      {n ∈ Set.Iic x | IsSumThreePower k n}.ncard

theorem target : statement := sorry

end Statements.Erdos325BinaryToTernaryInclusion
