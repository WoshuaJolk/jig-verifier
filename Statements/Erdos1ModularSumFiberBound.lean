import Mathlib.Data.Finset.Powerset
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.BigOperators.Group.Finset.Defs

namespace Statements.Erdos1ModularSumFiberBound

abbrev IsSumDistinctSet (A : Finset ℕ) (N : ℕ) : Prop :=
  A ⊆ Finset.Icc 1 N ∧
    (fun (S : A.powerset) => S.1.sum id).Injective

/-- Every modular fiber of fixed-cardinality subset sums is small. -/
abbrev statement : Prop :=
  ∀ (N : ℕ) (A : Finset ℕ), IsSumDistinctSet A N →
    ∀ (q t k : ℕ),
      q * (((A.powersetCard k).filter fun S => S.sum id % q = t % q).card - 1) ≤
        k * N

theorem target : statement := sorry

end Statements.Erdos1ModularSumFiberBound
