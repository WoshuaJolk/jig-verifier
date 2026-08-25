import Mathlib.Data.Set.Card
import Mathlib.Order.Lattice.Nat
import Mathlib.Tactic

namespace Submissions.Erdos20UniformityOneExact.Direct

def IsSunflower {α : Type} (family : Set (Set α)) : Prop :=
  ∃ kernel : Set α, family.Pairwise fun left right => left ∩ right = kernel

noncomputable def sunflowerThreshold (uniformity petals : ℕ) : ℕ :=
  sInf {bound : ℕ | ∀ {α : Type} (family : Set (Set α)),
    ((∀ member ∈ family, member.ncard = uniformity) ∧ bound ≤ family.ncard) →
      ∃ subfamily ⊆ family,
        subfamily.ncard = petals ∧ IsSunflower subfamily}

theorem proof : ∀ petals : ℕ, sunflowerThreshold 1 petals = petals := by
  intro petals
  let forcing : Set ℕ := {bound : ℕ | ∀ {α : Type} (family : Set (Set α)),
    ((∀ member ∈ family, member.ncard = 1) ∧ bound ≤ family.ncard) →
      ∃ subfamily ⊆ family,
        subfamily.ncard = petals ∧ IsSunflower subfamily}
  have hpetals : petals ∈ forcing := by
    intro α family hfamily
    by_cases hp : petals = 0
    · subst petals
      refine ⟨∅, Set.empty_subset family, by simp, ?_⟩
      exact ⟨∅, by simp⟩
    · have hfamily_ne : family.ncard ≠ 0 := by omega
      have hfinite : family.Finite := Set.finite_of_ncard_ne_zero hfamily_ne
      let familyFinset := hfinite.toFinset
      have hcard : petals ≤ familyFinset.card := by
        rw [← Set.ncard_eq_toFinset_card family hfinite]
        exact hfamily.2
      obtain ⟨subfamily, hsub, hsubcard⟩ :=
        Finset.exists_subset_card_eq hcard
      refine ⟨(subfamily : Set (Set α)), ?_, by simpa using hsubcard, ?_⟩
      · intro member hmember
        have : member ∈ familyFinset := hsub hmember
        simpa [familyFinset] using this
      · refine ⟨∅, ?_⟩
        intro left hleft right hright hne
        have hleft_family : left ∈ family := by
          have : left ∈ familyFinset := hsub hleft
          simpa [familyFinset] using this
        have hright_family : right ∈ family := by
          have : right ∈ familyFinset := hsub hright
          simpa [familyFinset] using this
        obtain ⟨a, rfl⟩ := Set.ncard_eq_one.mp
          (hfamily.1 left hleft_family)
        obtain ⟨b, rfl⟩ := Set.ncard_eq_one.mp
          (hfamily.1 right hright_family)
        simp_all
  have hlower : petals ≤ sInf forcing := by
    apply le_csInf (s := forcing) ⟨petals, hpetals⟩
    intro bound hbound
    by_contra hnot
    have hlt : bound < petals := Nat.lt_of_not_ge hnot
    let family : Set (Set (Fin bound)) :=
      Set.range fun i : Fin bound => ({i} : Set (Fin bound))
    have hinjective :
        Function.Injective (fun i : Fin bound => ({i} : Set (Fin bound))) := by
      intro i j hij
      simpa using hij
    have hfamily_finite : family.Finite := Set.finite_range _
    have hfamily_card : family.ncard = bound := by
      rw [Set.ncard_range_of_injective hinjective]
      simp
    have hfamily_uniform : ∀ member ∈ family, member.ncard = 1 := by
      intro member hmember
      obtain ⟨i, rfl⟩ := hmember
      simp
    obtain ⟨subfamily, hsub, hsubcard, _⟩ :=
      hbound family ⟨hfamily_uniform, by simp [hfamily_card]⟩
    have hsub_le : subfamily.ncard ≤ family.ncard :=
      Set.ncard_le_ncard hsub hfamily_finite
    omega
  have hupper : sInf forcing ≤ petals := Nat.sInf_le hpetals
  change sInf forcing = petals
  exact Nat.le_antisymm hupper hlower

end Submissions.Erdos20UniformityOneExact.Direct
