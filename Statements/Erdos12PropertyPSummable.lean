import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# Erdős problem 12(iii): reciprocal sums of Property P sets

## Source

Erdős and Sárközy, *On the divisibility properties of sequences of integers*,
Proc. London Math. Soc. (3) 21 (1970), pp. 97–101, p. 98:
"Probably, if A satisfies P then ∑ 1/aᵢ is convergent."

This is exactly the still-open third question on erdosproblems.com/12 and
`FormalConjectures/ErdosProblems/12.lean`.

## Reading

Property P says that no element `a` of `A` divides the sum of two distinct
larger elements `b,c` of `A`. Since `a < b` and `a < c` already make `a`
distinct from both, the conclusion `b = c` is exactly the exclusion of a
three-element counterexample.
-/

namespace Statements.Erdos12PropertyPSummable

/-- Every infinite set of natural numbers with Property P has a convergent
sum of reciprocals. -/
abbrev statement : Prop :=
  ∀ A : Set ℕ,
    (A.Infinite ∧
      ∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A,
        a ∣ b + c → a < b → a < c → b = c) →
    Summable (fun n : A => (1 : ℝ) / ((n : ℕ) : ℝ))

/-- The open target. -/
theorem target : statement := sorry

end Statements.Erdos12PropertyPSummable
