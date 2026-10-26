/-
Copyright 2026 The Formal Conjectures Authors.
Licensed under the Apache License, Version 2.0.
https://www.apache.org/licenses/LICENSE-2.0

Adapted from FormalConjectures/ErdosProblems/885.lean at
f778b1709d8787f6793e5bb3a4f0a1208bf702a7 (k_eq_4).
The finite-set lemma is adapted from Jig artifact
16d351e9-7cf6-4082-a3a2-212a04f5fe56 by woshuajolk.
This verifies the known k=4 result of Bremner (2019); no novelty claimed.
-/
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Dist
import Mathlib.Data.Set.Card
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.NormNum

open Set
namespace Submissions.Erdos885FourIntegerBoundary.KnownWitness

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
      Ns.card = 4 ∧ (∀ n ∈ Ns, 1 ≤ n) ∧
        (⋂ n ∈ Ns, factorDifferenceSet n).ncard ≥ 4 := by
  refine ⟨{65984625, 508032000, 1578963456, 2505664000}, by norm_num, by norm_num, ?_⟩
  have hsub : (↑({5040, 27720, 68880, 164976} : Finset ℕ) : Set ℕ) ⊆
      ⋂ n ∈ ({65984625, 508032000, 1578963456, 2505664000} : Finset ℕ), factorDifferenceSet n := by
    intro d hd
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hd
    simp only [Set.mem_iInter, Finset.mem_insert, Finset.mem_singleton]
    rintro n (rfl | rfl | rfl | rfl) <;> rcases hd with rfl | rfl | rfl | rfl
    · exact ⟨5985, 11025, by norm_num, by norm_num [Nat.dist]⟩
    · exact ⟨2205, 29925, by norm_num, by norm_num [Nat.dist]⟩
    · exact ⟨945, 69825, by norm_num, by norm_num [Nat.dist]⟩
    · exact ⟨399, 165375, by norm_num, by norm_num [Nat.dist]⟩
    · exact ⟨20160, 25200, by norm_num, by norm_num [Nat.dist]⟩
    · exact ⟨12600, 40320, by norm_num, by norm_num [Nat.dist]⟩
    · exact ⟨6720, 75600, by norm_num, by norm_num [Nat.dist]⟩
    · exact ⟨3024, 168000, by norm_num, by norm_num [Nat.dist]⟩
    · exact ⟨37296, 42336, by norm_num, by norm_num [Nat.dist]⟩
    · exact ⟨28224, 55944, by norm_num, by norm_num [Nat.dist]⟩
    · exact ⟨18144, 87024, by norm_num, by norm_num [Nat.dist]⟩
    · exact ⟨9072, 174048, by norm_num, by norm_num [Nat.dist]⟩
    · exact ⟨47600, 52640, by norm_num, by norm_num [Nat.dist]⟩
    · exact ⟨38080, 65800, by norm_num, by norm_num [Nat.dist]⟩
    · exact ⟨26320, 95200, by norm_num, by norm_num [Nat.dist]⟩
    · exact ⟨14000, 178976, by norm_num, by norm_num [Nat.dist]⟩
  have hfin : (⋂ n ∈ ({65984625, 508032000, 1578963456, 2505664000} : Finset ℕ), factorDifferenceSet n).Finite :=
    (factorDifferenceSet_finite (by norm_num : 0 < 65984625)).subset
      (Set.iInter₂_subset 65984625 (by simp))
  calc 4 = (↑({5040, 27720, 68880, 164976} : Finset ℕ) : Set ℕ).ncard := by
        rw [Set.ncard_coe_finset]; decide
    _ ≤ _ := Set.ncard_le_ncard hsub hfin

end Submissions.Erdos885FourIntegerBoundary.KnownWitness
