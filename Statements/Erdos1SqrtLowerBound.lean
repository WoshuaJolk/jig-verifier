import Mathlib.Data.Finset.Powerset
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.BigOperators.Group.Finset.Defs

namespace Statements.Erdos1SqrtLowerBound

abbrev IsSumDistinctSet (A : Finset ℕ) (N : ℕ) : Prop :=
  A ⊆ Finset.Icc 1 N ∧
    (fun (S : A.powerset) => S.1.sum id).Injective

/-- A fully explicit second-moment lower bound of order `2^|A| / √|A|`. -/
abbrev statement : Prop :=
  ∀ (N : ℕ) (A : Finset ℕ), IsSumDistinctSet A N → 2 ≤ A.card →
    2 ^ (A.card - 1) * (2 ^ (A.card - 2)) ^ 2 ≤
      2 ^ A.card * A.card * N ^ 2

theorem target : statement := sorry

end Statements.Erdos1SqrtLowerBound
