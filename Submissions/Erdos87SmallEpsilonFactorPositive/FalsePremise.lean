import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace Submissions.Erdos87SmallEpsilonFactorPositive.FalsePremise

theorem proof :
    False →
      ∀ ε : ℝ, 0 < ε → ε < 1 →
        ∀ k : ℕ, 0 < (1 - ε) ^ k := by
  intro h
  exact h.elim

end Submissions.Erdos87SmallEpsilonFactorPositive.FalsePremise
