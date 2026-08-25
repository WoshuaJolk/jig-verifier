import Mathlib.Algebra.Group.Pointwise.Set.Finite
import Mathlib.Data.Finset.NatAntidiagonal

open Set
open scoped Pointwise

namespace Submissions.Erdos28RepresentationPositive.Worker04

noncomputable def representationCount (A : Set ℕ) (n : ℕ) : ℕ := by
  classical
  exact ((Finset.antidiagonal n).filter fun (p : ℕ × ℕ) => p.1 ∈ A ∧ p.2 ∈ A).card

theorem proof :
    ∀ (A : Set ℕ) (n : ℕ), 0 < representationCount A n ↔ n ∈ A + A := by
  intro A n
  classical
  rw [Set.mem_add]
  constructor
  · intro h
    have hne := Finset.card_pos.mp h
    rcases hne with ⟨⟨a, b⟩, hp⟩
    simp only [Finset.mem_filter, Finset.mem_antidiagonal] at hp
    exact ⟨a, hp.2.1, b, hp.2.2, hp.1⟩
  · rintro ⟨a, ha, b, hb, hab⟩
    apply Finset.card_pos.mpr
    exact ⟨(a, b), Finset.mem_filter.mpr ⟨Finset.mem_antidiagonal.mpr hab, ha, hb⟩⟩

end Submissions.Erdos28RepresentationPositive.Worker04
