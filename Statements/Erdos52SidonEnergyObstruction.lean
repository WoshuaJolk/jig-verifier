import Mathlib.Combinatorics.Additive.Energy
import Mathlib.Data.Finset.Prod

open scoped Pointwise

namespace Statements.Erdos52SidonEnergyObstruction

/--
A quantitative obstruction profile below the `|A|⁴ / K` threshold:
all Sidon subsets are small, while both additive and multiplicative energies
are greater than `K`.
-/
abbrev statement : Prop :=
  ∀ (A : Finset ℤ) (K : ℕ),
    K * max (A + A).card (A * A).card < A.card ^ 4 →
      (∀ B : Finset ℤ, B ⊆ A →
        (∀ a ∈ B, ∀ b ∈ B, a ≤ b →
          ∀ c ∈ B, ∀ d ∈ B, c ≤ d →
            a + b = c + d → a = c ∧ b = d) →
        K * (B.card * (B.card + 1)) < 2 * A.card ^ 4) ∧
      K < Finset.addEnergy A A ∧
      K < Finset.mulEnergy A A

theorem target : statement := sorry

end Statements.Erdos52SidonEnergyObstruction
