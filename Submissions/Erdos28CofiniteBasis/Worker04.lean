import Mathlib.Data.Finset.NatAntidiagonal
import Mathlib.Data.Set.Finite.Lattice

open Set

namespace Submissions.Erdos28CofiniteBasis.Worker04

noncomputable def representationCount (A : Set ℕ) (n : ℕ) : ℕ := by
  classical
  exact ((Finset.antidiagonal n).filter fun (p : ℕ × ℕ) => p.1 ∈ A ∧ p.2 ∈ A).card

theorem proof :
    ∀ (A : Set ℕ), Aᶜ.Finite →
      ∀ k : ℕ, ∃ n : ℕ, k ≤ representationCount A n := by
  intro A hA k
  classical
  obtain ⟨N, hN⟩ := hA.bddAbove
  let f : ℕ → ℕ × ℕ := fun i => (N + 1 + i, N + 1 + k - i)
  let candidates := (Finset.range (k + 1)).image f
  refine ⟨2 * (N + 1) + k, ?_⟩
  have hf : Function.Injective f := by
    intro i j hij
    have hfirst := congrArg Prod.fst hij
    simp only [f] at hfirst
    omega
  have hcandidates : candidates.card = k + 1 := by
    simp only [candidates, Finset.card_image_of_injective _ hf, Finset.card_range]
  have hsubset :
      candidates ⊆
        (Finset.antidiagonal (2 * (N + 1) + k)).filter
          (fun (p : ℕ × ℕ) => p.1 ∈ A ∧ p.2 ∈ A) := by
    intro p hp
    simp only [candidates, Finset.mem_image, Finset.mem_range] at hp
    rcases hp with ⟨i, hi, rfl⟩
    apply Finset.mem_filter.mpr
    constructor
    · apply Finset.mem_antidiagonal.mpr
      simp only [f]
      omega
    · constructor
      · by_contra hnot
        have hcomp : N + 1 + i ∈ Aᶜ := hnot
        have := hN hcomp
        omega
      · by_contra hnot
        have hcomp : N + 1 + k - i ∈ Aᶜ := hnot
        have := hN hcomp
        omega
  rw [representationCount]
  have hcard := Finset.card_le_card hsubset
  omega

end Submissions.Erdos28CofiniteBasis.Worker04
