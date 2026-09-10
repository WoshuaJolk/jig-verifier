import Mathlib.Combinatorics.Additive.Dissociation
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Nat.Log
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring

namespace Submissions.Erdos963TernaryBound.Savcab
open Finset

noncomputable def signedSpan (B : Finset ℝ) : Finset ℝ := by
  classical
  exact (univ : Finset (B → Fin 3)).image
    (fun e => ∑ b : B, ((e b).val : ℝ) * b.val - ∑ b : B, b.val)

lemma card_signedSpan (B : Finset ℝ) : (signedSpan B).card ≤ 3 ^ B.card := by
  classical
  calc
    (signedSpan B).card ≤ Fintype.card (B → Fin 3) := card_image_le
    _ = 3 ^ B.card := by simp

lemma sub_sum_mem_signedSpan {B T U : Finset ℝ} (hT : T ⊆ B) (hU : U ⊆ B) :
    (∑ t ∈ T, t) - ∑ u ∈ U, u ∈ signedSpan B := by
  classical
  let e : B → Fin 3 := fun b =>
    if b.val ∈ T then (if b.val ∈ U then 1 else 2) else
      (if b.val ∈ U then 0 else 1)
  refine mem_image.mpr ⟨e, mem_univ _, ?_⟩
  rw [← sum_sub_distrib]
  have he : ∀ b : B, ((e b).val : ℝ) * b.val - b.val =
      (if b.val ∈ T then b.val else 0) - (if b.val ∈ U then b.val else 0) := by
    intro b
    by_cases ht : b.val ∈ T <;> by_cases hu : b.val ∈ U <;> simp [e, ht, hu] <;> ring
  simp_rw [he]
  rw [sum_sub_distrib]
  congr 1
  · rw [Finset.sum_coe_sort B (fun x : ℝ => if x ∈ T then x else 0)]
    simp only [Finset.sum_ite_mem, Finset.inter_eq_right.mpr hT]
  · rw [Finset.sum_coe_sort B (fun x : ℝ => if x ∈ U then x else 0)]
    simp only [Finset.sum_ite_mem, Finset.inter_eq_right.mpr hU]

lemma subset_signedSpan (B : Finset ℝ) : B ⊆ signedSpan B := by
  classical
  intro a ha
  simpa using sub_sum_mem_signedSpan (singleton_subset_iff.mpr ha) (empty_subset B)

lemma maximal_spans {A B : Finset ℝ} (hB : AddDissociated (B : Set ℝ))
    (hmax : ∀ a ∈ A, a ∉ B → ¬ AddDissociated (insert a B : Set ℝ)) :
    A ⊆ signedSpan B := by
  classical
  intro a ha
  by_cases hab : a ∈ B
  · exact subset_signedSpan B hab
  obtain ⟨T, U, hT, hU, hdisj, hne, heq⟩ :=
    not_addDissociated_iff_exists_disjoint.mp (hmax a ha hab)
  have hT : T ⊆ insert a B := by
    intro x hx
    exact mem_insert.mpr (hT hx)
  have hU : U ⊆ insert a B := by
    intro x hx
    exact mem_insert.mpr (hU hx)
  by_cases hat : a ∈ T
  · have haU : a ∉ U := fun hau => Finset.disjoint_left.mp hdisj hat hau
    have hUB : U ⊆ B := (subset_insert_iff_of_notMem haU).mp hU
    have hTB : T.erase a ⊆ B := subset_insert_iff.mp hT
    have hrepr : a = (∑ u ∈ U, u) - ∑ t ∈ T.erase a, t := by
      rw [sum_erase_eq_sub hat, heq]
      abel
    rw [hrepr]
    exact sub_sum_mem_signedSpan hUB hTB
  have hTB : T ⊆ B := (subset_insert_iff_of_notMem hat).mp hT
  by_cases hau : a ∈ U
  · have hUB : U.erase a ⊆ B := subset_insert_iff.mp hU
    have hrepr : a = (∑ t ∈ T, t) - ∑ u ∈ U.erase a, u := by
      rw [sum_erase_eq_sub hau, ← heq]
      abel
    rw [hrepr]
    exact sub_sum_mem_signedSpan hTB hUB
  have hUB : U ⊆ B := (subset_insert_iff_of_notMem hau).mp hU
  exact (hne (hB hTB hUB heq)).elim

def Dissociated (B : Finset ℝ) : Prop :=
  ∀ S T : Finset ℝ, S ⊆ B → T ⊆ B →
    (∑ x ∈ S, x) = ∑ x ∈ T, x → S = T

theorem proof : ∀ A : Finset ℝ, ∃ B : Finset ℝ,
    B ⊆ A ∧ Dissociated B ∧ A.card ≤ 3 ^ B.card := by
  classical
  intro A
  obtain ⟨B, hB⟩ :=
    (A.powerset.filter fun B : Finset ℝ => AddDissociated (B : Set ℝ)).exists_maximal
      ⟨∅, mem_filter.mpr ⟨empty_mem_powerset _, by simp⟩⟩
  simp only [mem_filter, mem_powerset] at hB
  refine ⟨B, hB.1.1, ?_, ?_⟩
  · intro S T hS hT heq
    exact hB.1.2 hS hT heq
  · have hspan : A ⊆ signedSpan B := maximal_spans hB.1.2 (by
      intro a ha hab h
      exact hB.not_gt ⟨insert_subset_iff.mpr ⟨ha, hB.1.1⟩, by simpa only [coe_insert] using h⟩ (ssubset_insert hab))
    exact (card_le_card hspan).trans (card_signedSpan B)

end Submissions.Erdos963TernaryBound.Savcab
