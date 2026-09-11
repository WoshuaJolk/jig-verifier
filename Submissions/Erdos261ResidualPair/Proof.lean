import Mathlib.Data.Set.Basic
import Mathlib.Tactic.Order

namespace Submissions.Erdos261ResidualPair.Proof

theorem proof :
    ∀ (a : ℕ) (S : Set ℕ),
      ((∀ r ∈ S, r < a + 1) ∧
        (∀ r ∈ S, ∀ s ∈ S, r = s ∨ r + s = a + 1)) →
      0 ∉ {t | ∃ r ∈ S, t < a + 2 ∧
        (t = 2 * r ∨ (a ≤ 2 * r ∧ t = 2 * r - a))} →
      ((∀ t ∈ {t | ∃ r ∈ S, t < a + 2 ∧
          (t = 2 * r ∨ (a ≤ 2 * r ∧ t = 2 * r - a))},
          t < (a + 1) + 1) ∧
        (∀ t ∈ {t | ∃ r ∈ S, t < a + 2 ∧
            (t = 2 * r ∨ (a ≤ 2 * r ∧ t = 2 * r - a))},
          ∀ u ∈ {u | ∃ s ∈ S, u < a + 2 ∧
            (u = 2 * s ∨ (a ≤ 2 * s ∧ u = 2 * s - a))},
          t = u ∨ t + u = (a + 1) + 1)) := by
  intro a S hS h0
  have hnzero : ∀ r ∈ S, 2 * r ≠ a := by
    intro r hr hra
    apply h0
    refine ⟨r, hr, by omega, Or.inr ⟨by omega, ?_⟩⟩
    omega
  constructor
  · intro t ht
    rcases ht with ⟨r, hr, ht, htr⟩
    omega
  · intro t ht u hu
    rcases ht with ⟨r, hr, ht, htr⟩
    rcases hu with ⟨s, hs, hu, hus⟩
    rcases hS.2 r hr s hs with hrs | hrs
    · subst s
      have hnr := hnzero r hr
      rcases htr with htr | htr <;> rcases hus with hus | hus
      all_goals omega
    · rcases htr with htr | htr <;> rcases hus with hus | hus
      all_goals have hnr := hnzero r hr
      all_goals have hns := hnzero s hs
      all_goals omega

end Submissions.Erdos261ResidualPair.Proof
