import Mathlib.Data.Finset.BooleanAlgebra
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

namespace Submissions.Erdos1183ChainPigeonhole.Direct

def IsChain {α : Type} [DecidableEq α]
    (family : Finset (Finset α)) : Prop :=
  ∀ A ∈ family, ∀ B ∈ family, A ⊆ B ∨ B ⊆ A

def Monochromatic {α : Type} [DecidableEq α]
    (color : Finset α → Bool) (family : Finset (Finset α)) : Prop :=
  ∃ b : Bool, ∀ A ∈ family, color A = b

def UnionClosed {α : Type} [DecidableEq α]
    (family : Finset (Finset α)) : Prop :=
  ∀ A ∈ family, ∀ B ∈ family, A ∪ B ∈ family

theorem chain_subfamily_unionClosed
    {α : Type} [DecidableEq α]
    {family mono : Finset (Finset α)}
    (hchain : IsChain family) (hsub : mono ⊆ family) :
    UnionClosed mono := by
  intro A hA B hB
  rcases hchain A (hsub hA) B (hsub hB) with hAB | hBA
  · rw [Finset.union_eq_right.mpr hAB]
    exact hB
  · rw [Finset.union_eq_left.mpr hBA]
    exact hA

theorem proof :
    ∀ (α : Type) [DecidableEq α],
      ∀ family : Finset (Finset α),
        ∀ color : Finset α → Bool,
          IsChain family →
            ∃ mono : Finset (Finset α),
              mono ⊆ family ∧ Monochromatic color mono ∧
                UnionClosed mono ∧ family.card ≤ 2 * mono.card := by
  intro α inst family color hchain
  let red := family.filter fun A => color A = true
  let blue := family.filter fun A => color A ≠ true
  have hsum : red.card + blue.card = family.card := by
    simpa [red, blue] using
      (Finset.card_filter_add_card_filter_not
        (s := family) (fun A => color A = true))
  by_cases hle : red.card ≤ blue.card
  · refine ⟨blue, ?_, ?_, ?_, ?_⟩
    · exact Finset.filter_subset _ _
    · refine ⟨false, ?_⟩
      intro A hA
      have hnot : color A ≠ true := (Finset.mem_filter.mp hA).2
      exact Bool.eq_false_of_not_eq_true hnot
    · exact chain_subfamily_unionClosed hchain (Finset.filter_subset _ _)
    · omega
  · refine ⟨red, ?_, ?_, ?_, ?_⟩
    · exact Finset.filter_subset _ _
    · refine ⟨true, ?_⟩
      intro A hA
      exact (Finset.mem_filter.mp hA).2
    · exact chain_subfamily_unionClosed hchain (Finset.filter_subset _ _)
    · omega

end Submissions.Erdos1183ChainPigeonhole.Direct
