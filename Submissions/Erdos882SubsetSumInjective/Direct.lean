import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic

namespace Submissions.Erdos882SubsetSumInjective.Direct

open Finset

def nonemptySubsetSums (A : Finset ℕ) : Finset ℕ :=
  (A.powerset.erase ∅).image fun B => B.sum id

def DivisibilityAntichain (S : Finset ℕ) : Prop :=
  ∀ x ∈ S, ∀ y ∈ S, x ∣ y → x = y

theorem proof :
    ∀ n : ℕ, ∀ A : Finset ℕ,
      A ⊆ Icc 1 n →
      DivisibilityAntichain (nonemptySubsetSums A) →
      ∀ B ⊆ A, ∀ C ⊆ A,
        B.sum id = C.sum id → B = C := by
  intro n A hA hanti B hB C hC hsum
  let D := B \ C
  let E := C \ B
  have hDsub : D ⊆ A := fun x hx => hB (Finset.mem_sdiff.mp hx).1
  have hEsub : E ⊆ A := fun x hx => hC (Finset.mem_sdiff.mp hx).1
  have hsumdiff : D.sum id = E.sum id := by
    have h₁ : (B ∩ C).sum id + D.sum id = B.sum id := by
      simpa [D] using B.sum_inter_add_sum_sdiff C id
    have h₂ : (B ∩ C).sum id + E.sum id = C.sum id := by
      simpa [E, Finset.inter_comm] using C.sum_inter_add_sum_sdiff B id
    omega
  by_contra hne
  have hDne : D.Nonempty := by
    by_contra hD
    have hD0 : D = ∅ := Finset.not_nonempty_iff_eq_empty.mp hD
    have hEzero : E.sum id = 0 := by simpa [hD0] using hsumdiff.symm
    have hE0 : E = ∅ := by
      by_contra hE'
      obtain ⟨e, he⟩ := Finset.nonempty_iff_ne_empty.mpr hE'
      have hepos : 1 ≤ e := (Finset.mem_Icc.mp (hA (hEsub he))).1
      have hele : e ≤ E.sum id := by
        apply Finset.single_le_sum (f := id)
        · intro i hi
          omega
        · exact he
      omega
    apply hne
    apply Finset.Subset.antisymm
    · exact Finset.sdiff_eq_empty_iff_subset.mp (by simpa [D] using hD0)
    · exact Finset.sdiff_eq_empty_iff_subset.mp (by simpa [E] using hE0)
  have hEne : E.Nonempty := by
    by_contra hE
    have hE0 : E = ∅ := Finset.not_nonempty_iff_eq_empty.mp hE
    have : D.sum id = 0 := by simpa [hE0] using hsumdiff
    obtain ⟨d, hd⟩ := hDne
    have hdpos : 1 ≤ d := (Finset.mem_Icc.mp (hA (hDsub hd))).1
    have hdle : d ≤ D.sum id := by
      apply Finset.single_le_sum (f := id)
      · intro i hi
        omega
      · exact hd
    omega
  let x := D.sum id
  have hxpos : 0 < x := by
    obtain ⟨d, hd⟩ := hDne
    have hdpos : 1 ≤ d := (Finset.mem_Icc.mp (hA (hDsub hd))).1
    have hdle : d ≤ D.sum id := by
      apply Finset.single_le_sum (f := id)
      · intro i hi
        omega
      · exact hd
    dsimp [x]
    omega
  have hxmem : x ∈ nonemptySubsetSums A := by
    rw [nonemptySubsetSums, Finset.mem_image]
    refine ⟨D, ?_, rfl⟩
    simp only [Finset.mem_erase, Finset.mem_powerset]
    exact ⟨Finset.nonempty_iff_ne_empty.mp hDne, hDsub⟩
  have hDE : Disjoint D E := by
    apply Finset.disjoint_left.mpr
    intro a ha hb
    exact (Finset.mem_sdiff.mp ha).2 (Finset.mem_sdiff.mp hb).1
  let U := D ∪ E
  have hUsub : U ⊆ A := Finset.union_subset hDsub hEsub
  have hUne : U.Nonempty := hDne.mono Finset.subset_union_left
  have hsumU : U.sum id = x + x := by
    dsimp [U, x]
    rw [Finset.sum_union hDE, hsumdiff]
  have hUmem : x + x ∈ nonemptySubsetSums A := by
    rw [nonemptySubsetSums, Finset.mem_image]
    refine ⟨U, ?_, hsumU⟩
    simp only [Finset.mem_erase, Finset.mem_powerset]
    exact ⟨Finset.nonempty_iff_ne_empty.mp hUne, hUsub⟩
  have hxdiv : x ∣ x + x := ⟨2, by omega⟩
  have := hanti x hxmem (x + x) hUmem hxdiv
  omega

end Submissions.Erdos882SubsetSumInjective.Direct
