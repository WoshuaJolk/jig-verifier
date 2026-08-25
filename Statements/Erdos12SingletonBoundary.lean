import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
Smoke-test boundary for Erdős problem 12: the singleton `{3}` contains no
forbidden triple.  This exercises the exact Property P implication used by the
root without pretending to advance the open reciprocal-summability question.
-/

namespace Statements.Erdos12SingletonBoundary

abbrev statement : Prop :=
  ∀ a ∈ ({3} : Set ℕ), ∀ b ∈ ({3} : Set ℕ), ∀ c ∈ ({3} : Set ℕ),
    a ∣ b + c → a < b → a < c → b = c

theorem target : statement := sorry

end Statements.Erdos12SingletonBoundary
