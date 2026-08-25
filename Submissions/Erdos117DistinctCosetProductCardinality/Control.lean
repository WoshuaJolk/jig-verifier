import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Algebra.Group.Subgroup.Basic

namespace Submissions.Erdos117DistinctCosetProductCardinality.Control

/-- Must-fail control: the canonical theorem is hidden behind an extra false
hypothesis, so this compiles but is not a proof of the published statement. -/
theorem proof :
    False →
      ∀ (G : Type) [Group G] [DecidableEq G]
        (A : Subgroup G) (T D : Finset G),
          (∀ d ∈ D, d ∈ A) →
          (∀ a ∈ T, ∀ a' ∈ T, a ≠ a' → a⁻¹ * a' ∉ A) →
          ((T.product D).image (fun q : G × G ↦ q.1 * q.2)).card =
            T.card * D.card := by
  intro h
  exact h.elim

end Submissions.Erdos117DistinctCosetProductCardinality.Control
