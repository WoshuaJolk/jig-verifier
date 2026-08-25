import Mathlib

open Finset

namespace Submissions.Erdos201BasicComparison.Worker09Control

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

theorem proof
    (claim : ∀ N : ℕ, arbitraryExtremum N ≤ intervalExtremum N) :
    ∀ N : ℕ, arbitraryExtremum N ≤ intervalExtremum N :=
  claim

end Submissions.Erdos201BasicComparison.Worker09Control
