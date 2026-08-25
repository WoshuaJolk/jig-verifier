import Mathlib.Data.Set.Card
import Mathlib.Order.Lattice.Nat

namespace Statements.Erdos20FactorialUpper

def IsSunflower {α : Type} (family : Set (Set α)) : Prop :=
  ∃ kernel : Set α, family.Pairwise fun left right => left ∩ right = kernel

noncomputable def sunflowerThreshold (uniformity petals : ℕ) : ℕ :=
  sInf {bound : ℕ | ∀ {α : Type} (family : Set (Set α)),
    ((∀ member ∈ family, member.ncard = uniformity) ∧ bound ≤ family.ncard) →
      ∃ subfamily ⊆ family,
        subfamily.ncard = petals ∧ IsSunflower subfamily}

/-- The classical Erdős–Rado factorial upper bound for sunflower thresholds. -/
abbrev statement : Prop :=
  ∀ uniformity petals : ℕ, uniformity > 0 → 2 ≤ petals →
    sunflowerThreshold uniformity petals ≤
      (petals - 1) ^ uniformity * uniformity.factorial + 1

theorem target : statement := sorry

end Statements.Erdos20FactorialUpper
