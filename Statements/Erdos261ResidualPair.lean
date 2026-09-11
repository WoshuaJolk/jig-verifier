import Mathlib.Data.Set.Basic
import Mathlib.Tactic.Order

namespace Statements.Erdos261ResidualPair

def children (a : ℕ) (S : Set ℕ) : Set ℕ :=
  {t | ∃ r ∈ S, t < a + 2 ∧
    (t = 2 * r ∨ (a ≤ 2 * r ∧ t = 2 * r - a))}

def PairShaped (a : ℕ) (S : Set ℕ) : Prop :=
  (∀ r ∈ S, r < a + 1) ∧
  (∀ r ∈ S, ∀ s ∈ S, r = s ∨ r + s = a + 1)

/-- Admissible residuals remain a singleton or a complementary pair until
one branch reaches zero. -/
abbrev statement : Prop :=
  ∀ (a : ℕ) (S : Set ℕ),
    PairShaped a S → 0 ∉ children a S → PairShaped (a + 1) (children a S)

theorem target : statement := by
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

end Statements.Erdos261ResidualPair
