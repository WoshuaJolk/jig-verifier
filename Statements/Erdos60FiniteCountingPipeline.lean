import Mathlib.Combinatorics.SimpleGraph.CycleGraph
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Finite two-stage convexity pipeline for four-cycle counting

The three hypotheses are the degree sum, incidence/codegree sum, and
labelled-to-unlabelled `C₄` identities.  Two finite Cauchy inequalities then
give explicit constraints on the total codegree and unlabelled copy count.
-/

open scoped BigOperators

namespace Statements.Erdos60FiniteCountingPipeline

abbrev DistinctPairs (n : ℕ) :=
  {p : Fin n × Fin n // p.1 ≠ p.2}

abbrev statement : Prop :=
  ∀ (n m C : ℕ)
    (degree : Fin n → ℕ) (codegree : DistinctPairs n → ℕ),
    (∑ v, degree v) = 2 * m →
    (∑ v, degree v * (degree v - 1)) =
      2 * ∑ p, codegree p →
    (∑ p, codegree p * (codegree p - 1)) = 8 * C →
    ((2 * m) ^ 2 ≤
      n * (2 * (∑ p, codegree p) + 2 * m)) ∧
    ((∑ p, codegree p) ^ 2 ≤
      (n * (n - 1)) * (8 * C + ∑ p, codegree p))

theorem target : statement := sorry

end Statements.Erdos60FiniteCountingPipeline
