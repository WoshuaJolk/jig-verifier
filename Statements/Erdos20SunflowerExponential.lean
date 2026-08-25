import Mathlib.Data.Set.Card
import Mathlib.Order.Lattice.Nat

namespace Statements.Erdos20SunflowerExponential

/-- A set family is a sunflower when every pair of distinct members has the
same intersection. -/
def IsSunflower {α : Type} (family : Set (Set α)) : Prop :=
  ∃ kernel : Set α, family.Pairwise fun left right => left ∩ right = kernel

/-- The least size forcing a `petals`-member sunflower in every family of
`uniformity`-element sets. -/
noncomputable def sunflowerThreshold (uniformity petals : ℕ) : ℕ :=
  sInf {bound : ℕ | ∀ {α : Type} (family : Set (Set α)),
    ((∀ member ∈ family, member.ncard = uniformity) ∧ bound ≤ family.ncard) →
      ∃ subfamily ⊆ family,
        subfamily.ncard = petals ∧ IsSunflower subfamily}

/-- Erdős problem 20, the sunflower conjecture. -/
abbrev statement : Prop :=
  ∃ constants : ℕ → ℕ, ∀ uniformity petals : ℕ, uniformity > 0 →
    sunflowerThreshold uniformity petals < (constants petals) ^ uniformity

theorem target : statement := sorry

end Statements.Erdos20SunflowerExponential
