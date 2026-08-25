import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Algebra.Group.Subgroup.Basic

namespace Statements.Erdos117DistinctCosetProductCardinality

/-- The product-cardinality step from arXiv:2608.20507v1, Lemma 5.7,
TeX source line 481. If `D` lies in `A` and `T` consists of representatives
of distinct left `A`-cosets, multiplication maps `T × D` injectively to `G`. -/
abbrev statement : Prop :=
  ∀ (G : Type) [Group G] [DecidableEq G]
    (A : Subgroup G) (T D : Finset G),
      (∀ d ∈ D, d ∈ A) →
      (∀ a ∈ T, ∀ a' ∈ T, a ≠ a' → a⁻¹ * a' ∉ A) →
      ((T.product D).image (fun q : G × G ↦ q.1 * q.2)).card =
        T.card * D.card

theorem target : statement := sorry

end Statements.Erdos117DistinctCosetProductCardinality
