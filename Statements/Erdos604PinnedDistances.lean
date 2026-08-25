import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Finset.Card

open EuclideanSpace

namespace Statements.Erdos604PinnedDistances

/-- Erdős Problem 604, with `n^(1-o(1))` expanded as every exponent `1-ε`. -/
abbrev statement : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ,
      ∀ A : Finset (EuclideanSpace ℝ (Fin 2)), N ≤ A.card →
        ∃ x ∈ A,
          c * (A.card : ℝ) ^ (1 - ε) ≤
            ((A.image fun y => dist x y).card : ℝ)

theorem target : statement := sorry

end Statements.Erdos604PinnedDistances
