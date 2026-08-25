import Mathlib.Data.Set.Card
import Mathlib.Order.Lattice.Nat

namespace Statements.Erdos20UniformityOneExact

def IsSunflower {α : Type} (family : Set (Set α)) : Prop :=
  ∃ kernel : Set α, family.Pairwise fun left right => left ∩ right = kernel

noncomputable def sunflowerThreshold (uniformity petals : ℕ) : ℕ :=
  sInf {bound : ℕ | ∀ {α : Type} (family : Set (Set α)),
    ((∀ member ∈ family, member.ncard = uniformity) ∧ bound ≤ family.ncard) →
      ∃ subfamily ⊆ family,
        subfamily.ncard = petals ∧ IsSunflower subfamily}

/-- For one-element sets, the exact threshold is the requested number of petals. -/
abbrev statement : Prop :=
  ∀ petals : ℕ, sunflowerThreshold 1 petals = petals

theorem target : statement := sorry

end Statements.Erdos20UniformityOneExact
