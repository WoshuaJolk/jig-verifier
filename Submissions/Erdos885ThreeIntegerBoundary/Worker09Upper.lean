import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Dist
import Mathlib.Data.Set.Card
import Mathlib.Tactic

open Set

namespace Submissions.Erdos885ThreeIntegerBoundary.Worker09Upper

def factorDifferenceSet (n : ℕ) : Set ℕ :=
  {d | ∃ a b : ℕ, n = a * b ∧ d = Nat.dist a b}

theorem factorDifferenceSet_finite {n : ℕ} (hn : 0 < n) :
    (factorDifferenceSet n).Finite := by
  refine Set.finite_Iic n |>.subset ?_
  intro d hd
  rcases hd with ⟨a, b, hab, rfl⟩
  have ha0 : 0 < a := by
    by_contra h
    simp at h
    simp [h] at hab
    omega
  have hb0 : 0 < b := by
    by_contra h
    simp at h
    simp [h] at hab
    omega
  have ha : a ≤ n := by
    rw [hab]
    exact Nat.le_mul_of_pos_right a hb0
  have hb : b ≤ n := by
    rw [hab]
    exact Nat.le_mul_of_pos_left b ha0
  rw [Nat.dist_eq_max_sub_min]
  exact (Nat.sub_le (max a b) (min a b)).trans (max_le ha hb)

theorem proof :
    ∃ Ns : Finset ℕ,
      Ns.card = 3 ∧ (∀ n ∈ Ns, 1 ≤ n) ∧
        (⋂ n ∈ Ns, factorDifferenceSet n).ncard ≥ 3 := by
  refine ⟨{112, 952, 3240}, by norm_num, by norm_num, ?_⟩
  have hsub : ({6, 54, 111} : Set ℕ) ⊆
      factorDifferenceSet 112 ∩ (factorDifferenceSet 952 ∩
        factorDifferenceSet 3240) := by
    intro d hd
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hd
    rcases hd with rfl | rfl | rfl
    · exact ⟨⟨8, 14, by norm_num, by norm_num [Nat.dist]⟩,
        ⟨⟨28, 34, by norm_num, by norm_num [Nat.dist]⟩,
          ⟨54, 60, by norm_num, by norm_num [Nat.dist]⟩⟩⟩
    · exact ⟨⟨2, 56, by norm_num, by norm_num [Nat.dist]⟩,
        ⟨⟨14, 68, by norm_num, by norm_num [Nat.dist]⟩,
          ⟨36, 90, by norm_num, by norm_num [Nat.dist]⟩⟩⟩
    · exact ⟨⟨1, 112, by norm_num, by norm_num [Nat.dist]⟩,
        ⟨⟨8, 119, by norm_num, by norm_num [Nat.dist]⟩,
          ⟨24, 135, by norm_num, by norm_num [Nat.dist]⟩⟩⟩
  have hfinite :
      (factorDifferenceSet 112 ∩ (factorDifferenceSet 952 ∩
        factorDifferenceSet 3240)).Finite :=
    (factorDifferenceSet_finite (by norm_num : 0 < 112)).inter_of_left _
  have hcard := Set.ncard_le_ncard hsub hfinite
  norm_num at hcard ⊢
  simpa using hcard

end Submissions.Erdos885ThreeIntegerBoundary.Worker09Upper
