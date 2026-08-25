import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Base

open Filter Asymptotics

namespace Statements.Erdos117LogBoundsAsymptoticAssembly

noncomputable def errorScale (n : ℕ) : ℝ :=
  Real.sqrt (n : ℝ) * Real.log ((n : ℝ) + 2) ^ (3 : ℕ)

/--
Final analytic assembly in arXiv:2608.20507v1, Theorem 2.2. The first
eventual inequality is the extraspecial-group lower output
`log₂ h(n) ≥ n/2 - O(1)`. The second is the uniform group-theoretic upper
output `log₂ h(n) ≤ n/2 + O(√n log³(n+2))`.
-/
abbrev statement : Prop :=
  ∀ (h : ℕ → ℕ) (lowerConstant upperConstant : ℝ),
    0 ≤ lowerConstant →
    0 ≤ upperConstant →
    (∀ᶠ n : ℕ in atTop,
      (n : ℝ) / 2 - lowerConstant ≤ Real.logb 2 (h n : ℝ)) →
    (∀ᶠ n : ℕ in atTop,
      Real.logb 2 (h n : ℝ) ≤
        (n : ℝ) / 2 + upperConstant * errorScale n) →
    (fun n : ℕ => Real.logb 2 (h n : ℝ) - (n : ℝ) / 2) =O[atTop]
      errorScale

theorem target : statement := by
  sorry

end Statements.Erdos117LogBoundsAsymptoticAssembly
