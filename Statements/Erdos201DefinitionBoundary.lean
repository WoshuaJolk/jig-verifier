import Mathlib

namespace Statements.Erdos201DefinitionBoundary

def IsThreeAPFree (A : Finset ℤ) : Prop :=
  ∀ ⦃a⦄, a ∈ A → ∀ ⦃b⦄, b ∈ A → ∀ ⦃c⦄, c ∈ A →
    a + c = 2 * b → a = b ∨ b = c

abbrev statement : Prop :=
  IsThreeAPFree ({1} : Finset ℤ) ∧
  Finset.Icc (1 : ℤ) 1 = {1} ∧
  ∀ N : ℕ, ∃ A : Finset ℤ, A.card = N

theorem target : statement := sorry

end Statements.Erdos201DefinitionBoundary
