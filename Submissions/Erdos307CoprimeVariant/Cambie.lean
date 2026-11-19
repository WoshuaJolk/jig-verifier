import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic

namespace Submissions.Erdos307CoprimeVariant.Cambie

theorem proof :
    ∃ P Q : Finset ℕ, (∀ p ∈ P, 0 < p) ∧ (∀ q ∈ Q, 0 < q) ∧ 1 < P.card ∧ 1 < Q.card ∧
      (P : Set ℕ).Pairwise Nat.Coprime ∧ (Q : Set ℕ).Pairwise Nat.Coprime ∧
      (∑ p ∈ P, (p : ℚ)⁻¹) * (∑ q ∈ Q, (q : ℚ)⁻¹) = 1 := by
  refine ⟨{1, 5}, {2, 3}, by decide, by decide, by decide, by decide, ?_, ?_, ?_⟩
  · intro a ha b hb hab
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> first | exact absurd rfl hab | decide
  · intro a ha b hb hab
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> first | exact absurd rfl hab | decide
  · rw [Finset.sum_pair (by decide), Finset.sum_pair (by decide)]
    norm_num

end Submissions.Erdos307CoprimeVariant.Cambie
