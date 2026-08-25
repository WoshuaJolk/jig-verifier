import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Interval
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Order.Interval.Finset.Nat

open Nat Finset Set

namespace Statements.Erdos291CoprimeHarmonicNumerators

/-- Least common multiple of `1,...,n`. -/
def L (n : ℕ) : ℕ :=
  (Finset.Icc 1 n).lcm id

/-- Numerator when the `n`th harmonic number is put over denominator `L n`. -/
def a (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.Icc 1 n, L n / k

/-- The open half of Erdős Problem 291: infinitely many harmonic numbers
have numerator coprime to the common denominator `L n`. -/
abbrev statement : Prop :=
  {n : ℕ | Nat.gcd (a n) (L n) = 1}.Infinite

theorem target : statement := sorry

end Statements.Erdos291CoprimeHarmonicNumerators
