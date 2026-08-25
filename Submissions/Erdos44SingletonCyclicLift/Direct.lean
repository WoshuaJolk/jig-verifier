import Mathlib.Data.Finset.Interval
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic

namespace Submissions.Erdos44SingletonCyclicLift.Direct

open Set Finset

def IsSidon {α : Type*} [AddCommMonoid α] (A : Set α) : Prop :=
  ∀ᵉ (i₁ ∈ A) (j₁ ∈ A) (i₂ ∈ A) (j₂ ∈ A),
    i₁ + i₂ = j₁ + j₂ →
      (i₁ = j₁ ∧ i₂ = j₂) ∨ (i₁ = j₂ ∧ i₂ = j₁)

def rot (n r x : ℕ) : ℕ := (x + n - r) % n

def RotSidon (n r : ℕ) (D : Finset ℕ) : Prop :=
  ∀ x ∈ D, ∀ y ∈ D, ∀ u ∈ D, ∀ v ∈ D,
    (rot n r x + rot n r y) % n = (rot n r u + rot n r v) % n →
      (x = u ∧ y = v) ∨ (x = v ∧ y = u)

def RotInjective (n r : ℕ) (D : Finset ℕ) : Prop :=
  ∀ x ∈ D, ∀ y ∈ D, rot n r x = rot n r y → x = y

theorem proof :
    ∀ (N a n r : ℕ) (D : Finset ℕ), 1 ≤ a → a ≤ N → 0 < n → r < n →
      r ∈ D → RotInjective n r D → RotSidon n r D →
      (∀ x ∈ D, x ≠ r → N < a + rot n r x) →
      N < a + n - 1 →
      ∀ ε : ℝ, 0 < ε →
        (1 - ε) * Real.sqrt ((a + n - 1 : ℕ) : ℝ) ≤ D.card →
          ∃ M > N, ∃ B ⊆ Finset.Icc (N + 1) M,
            IsSidon (({a} ∪ B : Finset ℕ) : Set ℕ) ∧
              (1 - ε) * Real.sqrt M ≤ ({a} ∪ B : Finset ℕ).card := by
  classical
  intro N a n r D ha hNa hn hrn hr hinj hsidon hgap hMN ε hε hdensity
  let f : ℕ → ℕ := fun x => a + rot n r x
  let L := D.image f
  let M := a + n - 1
  let B := L.erase a
  have hrr : rot n r r = 0 := by
    dsimp [rot]
    rw [Nat.add_sub_cancel_left, Nat.mod_self]
  have haL : a ∈ L := by
    apply Finset.mem_image.mpr
    refine ⟨r, hr, ?_⟩
    simp [f, hrr]
  have hf_inj : Set.InjOn f D := by
    intro x hx y hy hxy
    dsimp [f] at hxy
    apply hinj x hx y hy
    omega
  have hcardL : L.card = D.card := by
    exact Finset.card_image_iff.mpr hf_inj
  have hLsidon : IsSidon (L : Set ℕ) := by
    intro i₁ hi₁ j₁ hj₁ i₂ hi₂ j₂ hj₂ hsum
    rcases Finset.mem_image.mp hi₁ with ⟨x, hx, rfl⟩
    rcases Finset.mem_image.mp hj₁ with ⟨u, hu, rfl⟩
    rcases Finset.mem_image.mp hi₂ with ⟨y, hy, rfl⟩
    rcases Finset.mem_image.mp hj₂ with ⟨v, hv, rfl⟩
    have hrot : rot n r x + rot n r y = rot n r u + rot n r v := by
      dsimp [f] at hsum
      omega
    have hmod :
        (rot n r x + rot n r y) % n =
          (rot n r u + rot n r v) % n := by rw [hrot]
    rcases hsidon x hx y hy u hu v hv hmod with h | h
    · left
      exact ⟨by simp [h.1], by simp [h.2]⟩
    · right
      exact ⟨by simp [h.1], by simp [h.2]⟩
  have hBsub : B ⊆ Finset.Icc (N + 1) M := by
    intro b hb
    have hb' := Finset.mem_erase.mp hb
    rcases Finset.mem_image.mp hb'.2 with ⟨x, hx, rfl⟩
    have hxr : x ≠ r := by
      intro h
      subst x
      apply hb'.1
      simp [f, hrr]
    have hlower := hgap x hx hxr
    have hrotlt : rot n r x < n := Nat.mod_lt _ hn
    apply Finset.mem_Icc.mpr
    change N + 1 ≤ a + rot n r x ∧ a + rot n r x ≤ a + n - 1
    constructor <;> omega
  have hunion : ({a} ∪ B : Finset ℕ) = L := by
    apply Finset.ext
    intro x
    simp only [Finset.mem_union, Finset.mem_singleton, B, Finset.mem_erase]
    constructor
    · rintro (rfl | ⟨-, hx⟩)
      · exact haL
      · exact hx
    · intro hx
      by_cases hxa : x = a
      · exact Or.inl hxa
      · exact Or.inr ⟨hxa, hx⟩
  refine ⟨M, hMN, B, hBsub, ?_, ?_⟩
  · rw [hunion]
    exact hLsidon
  · rw [hunion, hcardL]
    simpa only [M] using hdensity

end Submissions.Erdos44SingletonCyclicLift.Direct
