import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic

namespace Submissions.Erdos307CoprimeVariant.EmptySets

/-- Degenerate control: the size and equation demands dropped, so empty sets are a witness.
Must not be accepted. -/
theorem proof :
    ∃ P Q : Finset ℕ, (∀ p ∈ P, 0 < p) ∧ (∀ q ∈ Q, 0 < q) ∧
      (P : Set ℕ).Pairwise Nat.Coprime ∧ (Q : Set ℕ).Pairwise Nat.Coprime :=
  ⟨∅, ∅, by simp, by simp, by simp, by simp⟩

end Submissions.Erdos307CoprimeVariant.EmptySets
