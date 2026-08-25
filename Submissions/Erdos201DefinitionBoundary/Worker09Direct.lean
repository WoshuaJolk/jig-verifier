import Mathlib

namespace Submissions.Erdos201DefinitionBoundary.Worker09Direct

def IsThreeAPFree (A : Finset ℤ) : Prop :=
  ∀ ⦃a⦄, a ∈ A → ∀ ⦃b⦄, b ∈ A → ∀ ⦃c⦄, c ∈ A →
    a + c = 2 * b → a = b ∨ b = c

theorem proof :
    IsThreeAPFree ({1} : Finset ℤ) ∧
    Finset.Icc (1 : ℤ) 1 = {1} ∧
    ∀ N : ℕ, ∃ A : Finset ℤ, A.card = N := by
  constructor
  · simp [IsThreeAPFree]
  constructor
  · decide
  · intro N
    let e : ℕ ↪ ℤ := ⟨Int.ofNat, Int.ofNat_injective⟩
    exact ⟨(Finset.range N).map e, by simp⟩

end Submissions.Erdos201DefinitionBoundary.Worker09Direct
