import Mathlib.Data.Finset.Prod
import Mathlib.Tactic

namespace Submissions.Erdos44SidonCollisionFibers.Direct

open Set Finset

def IsSidon {α : Type*} [AddCommMonoid α] (A : Set α) : Prop :=
  ∀ᵉ (i₁ ∈ A) (j₁ ∈ A) (i₂ ∈ A) (j₂ ∈ A),
    i₁ + i₂ = j₁ + j₂ →
      (i₁ = j₁ ∧ i₂ = j₂) ∨ (i₁ = j₂ ∧ i₂ = j₁)

abbrev Triple := (ℕ × ℕ) × ℕ

def IsCollision (C : Finset ℕ) (d : ℕ) (p : Triple) : Prop :=
  p.1.1 ∈ C ∧ p.1.2 ∈ C ∧ p.2 ∈ C ∧
    p.1.1 + p.1.2 = d + p.2

theorem proof :
    ∀ (C : Finset ℕ), IsSidon (C : Set ℕ) →
      ∀ d ∉ C,
        (∀ p q : Triple, IsCollision C d p → IsCollision C d q →
          p.1.1 = q.1.1 → p = q) ∧
        (∀ p q : Triple, IsCollision C d p → IsCollision C d q →
          p.1.2 = q.1.2 → p = q) ∧
        (∀ p q : Triple, IsCollision C d p → IsCollision C d q →
          p.2 = q.2 →
            (p.1.1 = q.1.1 ∧ p.1.2 = q.1.2) ∨
            (p.1.1 = q.1.2 ∧ p.1.2 = q.1.1)) := by
  intro C hC d hd
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨⟨x, y⟩, z⟩ ⟨⟨u, v⟩, w⟩ hp hq hxu
    unfold IsCollision at hp hq
    dsimp at hp hq
    rcases hp with ⟨hx, hy, hz, hpe⟩
    rcases hq with ⟨hu, hv, hw, hqe⟩
    change x = u at hxu
    subst u
    have hsum : y + w = v + z := by omega
    rcases hC y hy v hv w hw z hz hsum with h | h
    · rcases h with ⟨rfl, rfl⟩
      rfl
    · rcases h with ⟨hyz, hwv⟩
      have hxd : x = d := by omega
      exfalso
      apply hd
      simpa [hxd] using hx
  · rintro ⟨⟨x, y⟩, z⟩ ⟨⟨u, v⟩, w⟩ hp hq hyv
    unfold IsCollision at hp hq
    dsimp at hp hq
    rcases hp with ⟨hx, hy, hz, hpe⟩
    rcases hq with ⟨hu, hv, hw, hqe⟩
    change y = v at hyv
    subst v
    have hsum : x + w = u + z := by omega
    rcases hC x hx u hu w hw z hz hsum with h | h
    · rcases h with ⟨rfl, rfl⟩
      rfl
    · rcases h with ⟨hxz, hwu⟩
      have hyd : y = d := by omega
      exfalso
      apply hd
      simpa [hyd] using hy
  · rintro ⟨⟨x, y⟩, z⟩ ⟨⟨u, v⟩, w⟩ hp hq hzw
    unfold IsCollision at hp hq
    dsimp at hp hq
    rcases hp with ⟨hx, hy, hz, hpe⟩
    rcases hq with ⟨hu, hv, hw, hqe⟩
    change z = w at hzw
    subst w
    have hsum : x + y = u + v := by omega
    exact hC x hx u hu y hy v hv hsum

end Submissions.Erdos44SidonCollisionFibers.Direct
