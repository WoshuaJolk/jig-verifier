import Mathlib.Data.Finset.Interval
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic

namespace Submissions.Erdos44ForbiddenDifferenceDeletion.Direct

open Set Finset

def IsSidon {α : Type*} [AddCommMonoid α] (A : Set α) : Prop :=
  ∀ᵉ (i₁ ∈ A) (j₁ ∈ A) (i₂ ∈ A) (j₂ ∈ A),
    i₁ + i₂ = j₁ + j₂ →
      (i₁ = j₁ ∧ i₂ = j₂) ∨ (i₁ = j₂ ∧ i₂ = j₁)

def AvoidsDifferences (C F : Finset ℕ) : Prop :=
  ∀ x ∈ C, ∀ d ∈ F, x + d ∉ C

theorem proof :
    ∀ (C F : Finset ℕ), IsSidon (C : Set ℕ) →
      (∀ d ∈ F, 0 < d) →
        ∃ C' ⊆ C, IsSidon (C' : Set ℕ) ∧
          AvoidsDifferences C' F ∧ C.card ≤ C'.card + F.card := by
  classical
  intro C F hC hFpos
  let badFor : ℕ → Finset ℕ := fun d => C.filter fun x => x + d ∈ C
  have hbadFor (d : ℕ) (hd : d ∈ F) : (badFor d).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro x hx y hy
    have hxb := Finset.mem_filter.mp hx
    have hyb := Finset.mem_filter.mp hy
    have heq : x + (y + d) = y + (x + d) := by omega
    rcases hC x hxb.1 y hyb.1 (y + d) hyb.2 (x + d) hxb.2 heq with h | h
    · exact h.1
    · have hdpos := hFpos d hd
      omega
  let bad := F.biUnion badFor
  let C' := C \ bad
  have hsub : C' ⊆ C := Finset.sdiff_subset
  have hsidon : IsSidon (C' : Set ℕ) := by
    intro i₁ hi₁ j₁ hj₁ i₂ hi₂ j₂ hj₂ hsum
    exact hC i₁ (hsub hi₁) j₁ (hsub hj₁) i₂ (hsub hi₂) j₂ (hsub hj₂) hsum
  have havoids : AvoidsDifferences C' F := by
    intro x hx d hd hxd
    have hxbc := Finset.mem_sdiff.mp hx
    have hxdc : x + d ∈ C := hsub hxd
    have hxbadFor : x ∈ badFor d := Finset.mem_filter.mpr ⟨hxbc.1, hxdc⟩
    have hxbad : x ∈ bad := Finset.mem_biUnion.mpr ⟨d, hd, hxbadFor⟩
    exact hxbc.2 hxbad
  have hbadCard : bad.card ≤ F.card := by
    calc
      bad.card ≤ ∑ d ∈ F, (badFor d).card := Finset.card_biUnion_le
      _ ≤ ∑ _d ∈ F, 1 := Finset.sum_le_sum fun d hd => hbadFor d hd
      _ = F.card := by simp
  have hloss : C.card ≤ C'.card + F.card := by
    have hbase : C.card ≤ (C \ bad).card + bad.card :=
      Finset.card_le_card_sdiff_add_card
    dsimp only [C']
    omega
  exact ⟨C', hsub, hsidon, havoids, hloss⟩

end Submissions.Erdos44ForbiddenDifferenceDeletion.Direct
