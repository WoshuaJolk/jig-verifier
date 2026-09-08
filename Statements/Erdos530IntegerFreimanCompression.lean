import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Set.Function

namespace Statements.Erdos530IntegerFreimanCompression

abbrev statement : Prop :=
  ∀ (A : Finset ℤ) (m : ℕ), 0 < m →
  ∃ C : Finset ℤ, C ⊆ A ∧ ∃ f : ℤ → ZMod m, Set.InjOn f C ∧
    (∀ a ∈ C, ∀ b ∈ C, ∀ c ∈ C, ∀ d ∈ C,
      a + b = c + d → f a + f b = f c + f d) ∧
    4 * (m : ℤ) * A.card - (A.card : ℤ) * ((A.card : ℤ) - 1) ≤
      8 * (m : ℤ) * C.card

theorem target : statement := sorry

end Statements.Erdos530IntegerFreimanCompression
