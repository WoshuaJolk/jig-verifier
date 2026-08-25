import Mathlib.Data.Finset.Powerset
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.BigOperators.Group.Finset.Defs

namespace Statements.Erdos1ModularFiberBound

abbrev IsSumDistinctSet (A : Finset ℕ) (N : ℕ) : Prop :=
  A ⊆ Finset.Icc 1 N ∧
    (fun (S : A.powerset) => S.1.sum id).Injective

/-- Fixed-cardinality subsets of one residue fiber have sums spaced by the modulus. -/
abbrev statement : Prop :=
  ∀ (N : ℕ) (A : Finset ℕ), IsSumDistinctSet A N →
    ∀ (q r k : ℕ),
      q * (Nat.choose (A.filter fun a => a % q = r % q).card k - 1) ≤ k * N

theorem target : statement := sorry

end Statements.Erdos1ModularFiberBound
