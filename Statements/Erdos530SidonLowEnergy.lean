import Mathlib.Combinatorics.Additive.Energy
import Mathlib.Analysis.Real.Sqrt

namespace Statements.Erdos530SidonLowEnergy

def IsSidon (S : Finset ℝ) : Prop :=
  ∀ ⦃a b c d : ℝ⦄, a ∈ S → b ∈ S → c ∈ S → d ∈ S →
    a + b = c + d → (a = c ∧ b = d) ∨ (a = d ∧ b = c)

abbrev statement : Prop :=
  ∀ A : Finset ℝ, 256 ≤ A.card →
    (Finset.addEnergy A A : ℝ) ≤ (A.card : ℝ) ^ 2 * Real.sqrt A.card / 4 →
    ∃ S : Finset ℝ, S ⊆ A ∧ IsSidon S ∧ Real.sqrt A.card ≤ (S.card : ℝ)

theorem target : statement := sorry

end Statements.Erdos530SidonLowEnergy
