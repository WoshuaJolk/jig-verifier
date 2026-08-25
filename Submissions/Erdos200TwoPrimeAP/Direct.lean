import Mathlib.Algebra.Module.NatInt
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Set.Card
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic

namespace Submissions.Erdos200TwoPrimeAP.Direct

def IsAPOfLengthWith {α : Type*} [AddCommMonoid α]
    (s : Set α) (l : ℕ∞) (a d : α) : Prop :=
  ENat.card s = l ∧ s = {a + n • d | (n : ℕ) (_ : n < l)}

def IsAPOfLength {α : Type*} [AddCommMonoid α]
    (s : Set α) (l : ℕ∞) : Prop :=
  ∃ a d : α, IsAPOfLengthWith s l a d

theorem proof :
    IsAPOfLength ({2, 3} : Set ℕ) 2 ∧
      ∀ p ∈ ({2, 3} : Set ℕ), p.Prime := by
  constructor
  · refine ⟨2, 1, ?_⟩
    simp [IsAPOfLengthWith]
    ext x
    constructor
    · intro hx
      rcases hx with rfl | rfl
      · exact ⟨0, by norm_num, by norm_num⟩
      · exact ⟨1, by norm_num, by norm_num⟩
    · rintro ⟨i, hi, rfl⟩
      interval_cases i <;> simp
  · norm_num

end Submissions.Erdos200TwoPrimeAP.Direct
