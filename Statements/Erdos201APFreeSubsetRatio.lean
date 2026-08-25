import Mathlib

open Filter Finset

namespace Statements.Erdos201APFreeSubsetRatio

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

/-- Erdős Problem 201: intervals are asymptotically extremal for
guaranteed three-term-progression-free subsets. -/
abbrev statement : Prop :=
  Tendsto
    (fun N : ℕ =>
      (intervalExtremum N : ℝ) / (arbitraryExtremum N : ℝ))
    atTop (nhds 1)

theorem target : statement := sorry

end Statements.Erdos201APFreeSubsetRatio
