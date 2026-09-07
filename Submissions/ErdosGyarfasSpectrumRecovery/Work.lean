import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

namespace Submissions.ErdosGyarfasSpectrumRecovery.Work

def responds (S : Finset ℕ) (q : ℕ) : Prop :=
  ∃ x ∈ S, ∃ k : ℕ, 2 ≤ k ∧ q + x = 2 ^ k

lemma isolate (M k x y j : ℕ) (hQ : 2 * M < 2 ^ k)
    (hx : 1 ≤ x ∧ x ≤ M) (hy : 1 ≤ y ∧ y ≤ M)
    (heq : 2 ^ k - x + y = 2 ^ j) : y = x := by
  have hsub : 2 ^ k - x + x = 2 ^ k := Nat.sub_add_cancel (by omega)
  have hj : j = k := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hp := Nat.pow_le_pow_right (by decide : 0 < 2) (show j + 1 ≤ k by omega)
      rw [pow_succ] at hp
      omega
    · have hp := Nat.pow_le_pow_right (by decide : 0 < 2) (show k + 1 ≤ j by omega)
      rw [pow_succ] at hp
      omega
  subst j
  omega

theorem proof : ∀ (M : ℕ) (S T : Finset ℕ),
    (∀ x ∈ S, 1 ≤ x ∧ x ≤ M) →
    (∀ x ∈ T, 1 ≤ x ∧ x ≤ M) →
    ((∀ q : ℕ, 2 ≤ q → responds S q → responds T q) ↔ S ⊆ T) := by
  intro M S T hS hT
  constructor
  · intro h x hx
    have hb := hS x hx
    have hg : M + 1 < 2 ^ (M + 1) := Nat.lt_two_pow_self
    have hQ : 2 * M < 2 ^ (M + 2) := by
      rw [show M + 2 = (M + 1) + 1 by omega, pow_succ]
      omega
    have hq : 2 ≤ 2 ^ (M + 2) - x := by
      rw [show M + 2 = (M + 1) + 1 by omega, pow_succ]
      omega
    have hr : responds S (2 ^ (M + 2) - x) :=
      ⟨x, hx, M + 2, by omega, Nat.sub_add_cancel (by omega)⟩
    obtain ⟨y, hy, j, _, heq⟩ := h _ hq hr
    have he := isolate M (M + 2) x y j hQ hb (hT y hy) heq
    simpa [he] using hy
  · intro h q _ hr
    obtain ⟨x, hx, k, hk, heq⟩ := hr
    exact ⟨x, h hx, k, hk, heq⟩

end Submissions.ErdosGyarfasSpectrumRecovery.Work
