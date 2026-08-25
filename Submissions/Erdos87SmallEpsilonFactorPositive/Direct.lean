import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace Submissions.Erdos87SmallEpsilonFactorPositive.Direct

theorem proof :
    ∀ ε : ℝ, 0 < ε → ε < 1 →
      ∀ k : ℕ, 0 < (1 - ε) ^ k := by
  intro ε _ hε k
  exact pow_pos (sub_pos.mpr hε) k

end Submissions.Erdos87SmallEpsilonFactorPositive.Direct
