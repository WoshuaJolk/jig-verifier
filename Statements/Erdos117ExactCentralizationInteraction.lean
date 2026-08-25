import Mathlib.GroupTheory.Commutator.Basic

namespace Statements.Erdos117ExactCentralizationInteraction

open scoped commutatorElement

/-- The exact-centralization noncancellation step used in Lemma 5.7 of
arXiv:2608.20507v1. An earlier commutator outside a normal filtration term
cannot be cancelled by a later commutator inside that term. -/
abbrev statement : Prop :=
  ∀ (G : Type) [Group G] (K : Subgroup G) [K.Normal]
    (a₁ a₂ b₁ b₂ : G),
      Commute b₁ a₂ →
      Commute b₂ a₁ →
      ⁅b₁, b₂⁆ ∈ K →
      ⁅a₁, a₂⁆ ∉ K →
      ¬Commute (a₁ * b₁) (a₂ * b₂)

theorem target : statement := sorry

end Statements.Erdos117ExactCentralizationInteraction
