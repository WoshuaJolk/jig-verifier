import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Card

namespace Statements.Erdos530IntegerFreimanModel

abbrev statement : Prop :=
  ∀ A : Finset ℝ, ∃ f : ℝ → ℤ, Set.InjOn f A ∧
    ∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, ∀ d ∈ A,
      f a + f b = f c + f d ↔ a + b = c + d

theorem target : statement := sorry

end Statements.Erdos530IntegerFreimanModel
