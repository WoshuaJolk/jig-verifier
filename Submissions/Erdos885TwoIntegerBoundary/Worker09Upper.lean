import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Dist
import Mathlib.Data.Set.Card
import Mathlib.Tactic

open Set

namespace Submissions.Erdos885TwoIntegerBoundary.Worker09Upper

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
      Ns.card = 2 ∧ (∀ n ∈ Ns, 1 ≤ n) ∧
        (⋂ n ∈ Ns, factorDifferenceSet n).ncard ≥ 2 := by
  refine ⟨{8, 120}, by norm_num, by norm_num, ?_⟩
  have hsub : ({2, 7} : Set ℕ) ⊆
      factorDifferenceSet 8 ∩ factorDifferenceSet 120 := by
    intro d hd
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hd
    rcases hd with rfl | rfl
    · constructor
      · exact ⟨2, 4, by norm_num, by norm_num [Nat.dist]⟩
      · exact ⟨10, 12, by norm_num, by norm_num [Nat.dist]⟩
    · constructor
      · exact ⟨1, 8, by norm_num, by norm_num [Nat.dist]⟩
      · exact ⟨8, 15, by norm_num, by norm_num [Nat.dist]⟩
  have hfinite : (factorDifferenceSet 8 ∩ factorDifferenceSet 120).Finite :=
    (factorDifferenceSet_finite (by norm_num : 0 < 8)).inter_of_left _
  have hcard := Set.ncard_le_ncard hsub hfinite
  norm_num at hcard ⊢
  simpa using hcard

end Submissions.Erdos885TwoIntegerBoundary.Worker09Upper
