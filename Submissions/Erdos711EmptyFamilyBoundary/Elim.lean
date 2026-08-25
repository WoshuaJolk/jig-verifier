import Mathlib.Data.Fin.Basic

namespace Submissions.Erdos711EmptyFamilyBoundary.Elim

def HasDistinctMultiples (n m L : ℕ) : Prop :=
  ∃ a : Fin n → ℕ, Function.Injective a ∧
    ∀ k : Fin n,
      m < a k ∧ a k ≤ m + L ∧ (k.val + 1) ∣ a k

theorem proof :
    ∀ m : ℕ, HasDistinctMultiples 0 m 0 := by
  intro m
  refine ⟨fun k => Fin.elim0 k, ?_, ?_⟩
  · intro i
    exact Fin.elim0 i
  · intro i
    exact Fin.elim0 i

end Submissions.Erdos711EmptyFamilyBoundary.Elim
