import Mathlib.Data.Finset.Interval
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic

namespace Submissions.Erdos44ConditionalExtension.Direct

open Set Finset

def IsSidon {α : Type*} [AddCommMonoid α] (A : Set α) : Prop :=
  ∀ᵉ (i₁ ∈ A) (j₁ ∈ A) (i₂ ∈ A) (j₂ ∈ A),
    i₁ + i₂ = j₁ + j₂ →
      (i₁ = j₁ ∧ i₂ = j₂) ∨ (i₁ = j₂ ∧ i₂ = j₁)

private theorem onePoint
    (N : ℕ) (A : Finset ℕ) (hsub : A ⊆ Finset.Icc 1 N)
    (hsidon : IsSidon (A : Set ℕ)) (x : ℕ) (hx : 2 * N ≤ x) :
    IsSidon ((A : Set ℕ) ∪ {x}) := by
  have upper : ∀ ⦃a : ℕ⦄, a ∈ A → a ≤ N := by
    intro a ha
    exact (Finset.mem_Icc.mp (hsub ha)).2
  have lower : ∀ ⦃a : ℕ⦄, a ∈ A → 1 ≤ a := by
    intro a ha
    exact (Finset.mem_Icc.mp (hsub ha)).1
  intro i₁ hi₁ j₁ hj₁ i₂ hi₂ j₂ hj₂ hsum
  simp only [Set.mem_union, Set.mem_singleton_iff] at hi₁ hj₁ hi₂ hj₂
  rcases hi₁ with hi₁ | rfl <;>
    rcases hj₁ with hj₁ | rfl <;>
      rcases hi₂ with hi₂ | rfl <;>
        rcases hj₂ with hj₂ | rfl
  all_goals
    try have hi₁N := upper hi₁
    try have hj₁N := upper hj₁
    try have hi₂N := upper hi₂
    try have hj₂N := upper hj₂
    try have hi₁pos := lower hi₁
    try have hj₁pos := lower hj₁
    try have hi₂pos := lower hi₂
    try have hj₂pos := lower hj₂
    first
    | exact hsidon i₁ hi₁ j₁ hj₁ i₂ hi₂ j₂ hj₂ hsum
    | (left; constructor <;> omega)
    | (right; constructor <;> omega)
    | omega

theorem proof :
    ∀ᵉ (N ≥ (1 : ℕ)) (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) →
      ∀ᵉ (ε > (0 : ℝ)),
        (1 - ε) * Real.sqrt ((2 * N : ℕ) : ℝ) ≤ A.card + 1 →
          ∃ᵉ (M > N) (B ⊆ Finset.Icc (N + 1) M),
            IsSidon (A ∪ B : Set ℕ) ∧
              (1 - ε) * Real.sqrt M ≤ (A ∪ B).card := by
  intro N hN A hsub hsidon ε hε hdensity
  let x := 2 * N
  have hx : 2 * N ≤ x := by omega
  have hxN : N < x := by omega
  have hxnot : x ∉ A := by
    intro hmem
    have hupper := (Finset.mem_Icc.mp (hsub hmem)).2
    omega
  refine ⟨x, hxN, {x}, ?_, ?_, ?_⟩
  · intro y hy
    simp only [Finset.mem_singleton] at hy
    subst y
    exact Finset.mem_Icc.mpr ⟨by omega, le_rfl⟩
  · simpa only [Finset.coe_union, Finset.coe_singleton] using
      onePoint N A hsub hsidon x hx
  · rw [Finset.card_union_of_disjoint]
    · simp only [Finset.card_singleton, Nat.cast_add, Nat.cast_one]
      simpa only [x] using hdensity
    · exact Finset.disjoint_singleton_right.mpr hxnot

end Submissions.Erdos44ConditionalExtension.Direct
