import Mathlib.Algebra.Group.Pointwise.Set.Card
import Mathlib.Analysis.Real.Cardinality
import Mathlib.SetTheory.Cardinal.Continuum
import Mathlib.Tactic

namespace Submissions.Erdos949SmallForbiddenSetCase.Worker01

open Cardinal
open scoped Pointwise

theorem proof :
    ∀ S : Set ℝ, #S < 𝔠 →
      ∃ A ⊆ Sᶜ, #A = 𝔠 ∧ A + A ⊆ Sᶜ := by
  intro S hS𝔠
  obtain ⟨A, ⟨hAS, hAAS⟩, hAmax⟩ := by
    refine zorn_subset {A ⊆ Sᶜ | ∀ x ∈ A, ∀ y ∈ A, x + y ∉ S} ?_
    simp only [Set.ofPred_and, Set.subset_inter_iff, Set.mem_inter_iff,
      Set.mem_ofPred_eq, and_imp, and_assoc]
    refine fun C hCS hSC hC ↦ ⟨_, Set.iUnion₂_subset hCS, ?_, Set.subset_iUnion₂⟩
    simp only [Set.mem_iUnion, exists_prop, forall_exists_index, and_imp]
    rintro x B hB hx y D hD hy
    obtain ⟨E, hE, hBE, hDE⟩ := hC.directedOn _ hB _ hD
    exact hSC hE _ (hBE hx) _ (hDE hy)
  have hAAS' : A + A ⊆ Sᶜ := by
    rintro _ ⟨x, hx, y, hy, rfl⟩
    exact hAAS x hx y hy
  refine ⟨A, hAS, ?_, hAAS'⟩
  replace hAmax : Sᶜ ∩ ((· / 2) '' S)ᶜ ⊆ A ∪ ⋃ a ∈ A, (· - a) '' S := by
    simp only [Set.subset_def, Set.mem_inter_iff, Set.mem_compl_iff,
      Set.mem_image, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      div_eq_iff_mul_eq, mul_two, exists_eq_right', Set.mem_union,
      Set.mem_iUnion, sub_eq_iff_eq_add, exists_eq_right, exists_prop,
      or_iff_not_imp_left, and_imp]
    rintro x hxS hxxS hxA
    by_contra! hxAS
    refine hxA <| hAmax ?_ (Set.subset_insert ..) (Set.mem_insert ..)
    simpa [Set.insert_subset_iff, forall_and, add_comm _ x, *] using
      ⟨hxAS, hAAS⟩
  have hlarge : #↑(Sᶜ ∩ ((· / 2) '' S)ᶜ) = 𝔠 := by
    rw [← Set.compl_union, mk_compl_of_infinite, mk_real]
    grw [mk_union_le, Cardinal.mk_real]
    refine add_lt_of_lt aleph0_le_continuum hS𝔠 ?_
    grw [mk_image_le]
    exact hS𝔠
  refine (mk_real ▸ mk_set_le _).eq_of_not_lt fun hA𝔠 ↦ lt_irrefl 𝔠 ?_
  calc
    𝔠 = #↑(Sᶜ ∩ ((· / 2) '' S)ᶜ) := by rw [hlarge]
    _ ≤ #↑(A ∪ ⋃ a ∈ A, (· - a) '' S) := mk_subtype_mono hAmax
    _ ≤ #A + #A * #S := by
      obtain rfl | hA := A.eq_empty_or_nonempty
      · simp
      have : Nonempty A := hA.coe_sort
      grw [mk_union_le, mk_biUnion_le, ciSup_le fun _ ↦ mk_image_le]
    _ < 𝔠 := add_lt_of_lt aleph0_le_continuum hA𝔠 <|
      mul_lt_of_lt aleph0_le_continuum hA𝔠 hS𝔠

end Submissions.Erdos949SmallForbiddenSetCase.Worker01
