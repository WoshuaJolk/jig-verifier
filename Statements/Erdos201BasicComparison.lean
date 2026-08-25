import Mathlib

open Finset

namespace Statements.Erdos201BasicComparison

def IsThreeAPFree (A : Finset ℤ) : Prop :=
  ∀ ⦃a⦄, a ∈ A → ∀ ⦃b⦄, b ∈ A → ∀ ⦃c⦄, c ∈ A →
    a + c = 2 * b → a = b ∨ b = c

noncomputable def maxThreeAPFreeCard (A : Finset ℤ) : ℕ := by
  classical
  exact (A.powerset.filter IsThreeAPFree).sup card

noncomputable def intervalExtremum (N : ℕ) : ℕ :=
  maxThreeAPFreeCard (Finset.Icc 1 (N : ℤ))

noncomputable def arbitraryExtremum (N : ℕ) : ℕ :=
  sInf {m : ℕ | ∃ A : Finset ℤ,
    A.card = N ∧ maxThreeAPFreeCard A = m}

/-- The interval is one admissible ambient set, so the worst guaranteed
three-AP-free cardinality cannot exceed the interval extremum. -/
abbrev statement : Prop :=
  ∀ N : ℕ, arbitraryExtremum N ≤ intervalExtremum N

theorem target : statement := sorry

end Statements.Erdos201BasicComparison
