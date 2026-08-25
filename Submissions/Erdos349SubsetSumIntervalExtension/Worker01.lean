import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

namespace Submissions.Erdos349SubsetSumIntervalExtension.Worker01

open Finset

theorem proof :
    ∀ (values : Finset ℕ) (a L : ℕ), a ∉ values →
      (∀ n ≤ L, ∃ chosen : Finset ℕ, chosen ⊆ values ∧ ∑ x ∈ chosen, x = n) →
      a ≤ L + 1 →
      ∀ n ≤ L + a, ∃ chosen : Finset ℕ,
        chosen ⊆ insert a values ∧ ∑ x ∈ chosen, x = n := by
  intro values a L hafresh hcover ha n hn
  by_cases hnL : n ≤ L
  · obtain ⟨chosen, hchosen, hsum⟩ := hcover n hnL
    exact ⟨chosen, hchosen.trans (subset_insert a values), hsum⟩
  · have hLa : L + 1 ≥ a := ha
    have han : a ≤ n := by omega
    have hrem : n - a ≤ L := by omega
    obtain ⟨chosen, hchosen, hsum⟩ := hcover (n - a) hrem
    have hnotmem : a ∉ chosen := fun haChosen ↦ hafresh (hchosen haChosen)
    refine ⟨insert a chosen, ?_, ?_⟩
    · exact insert_subset_insert a hchosen
    · rw [sum_insert hnotmem, hsum]
      omega

end Submissions.Erdos349SubsetSumIntervalExtension.Worker01
