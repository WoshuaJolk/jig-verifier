import Mathlib

namespace Submissions.Erdos201DefinitionBoundary.Worker09VacuousControl

def IsThreeAPFree (A : Finset ℤ) : Prop :=
  ∀ ⦃a⦄, a ∈ A → ∀ ⦃b⦄, b ∈ A → ∀ ⦃c⦄, c ∈ A →
    a + c = 2 * b → a = b ∨ b = c

theorem proof (h : False) :
    IsThreeAPFree ({1} : Finset ℤ) ∧
    Finset.Icc (1 : ℤ) 1 = {1} ∧
    ∀ N : ℕ, ∃ A : Finset ℤ, A.card = N := h.elim

end Submissions.Erdos201DefinitionBoundary.Worker09VacuousControl
