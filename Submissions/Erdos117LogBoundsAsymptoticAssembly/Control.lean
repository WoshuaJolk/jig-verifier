import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Base

open Filter Asymptotics

namespace Submissions.Erdos117LogBoundsAsymptoticAssembly.Control

noncomputable def errorScale (n : ℕ) : ℝ :=
  Real.sqrt (n : ℝ) * Real.log ((n : ℝ) + 2) ^ (3 : ℕ)

/-- Must-fail anti-restatement control with an intentional extra premise. -/
theorem proof :
    False →
      ∀ (h : ℕ → ℕ) (lowerConstant upperConstant : ℝ),
        0 ≤ lowerConstant →
        0 ≤ upperConstant →
        (∀ᶠ n : ℕ in atTop,
          (n : ℝ) / 2 - lowerConstant ≤ Real.logb 2 (h n : ℝ)) →
        (∀ᶠ n : ℕ in atTop,
          Real.logb 2 (h n : ℝ) ≤
            (n : ℝ) / 2 + upperConstant * errorScale n) →
        (fun n : ℕ => Real.logb 2 (h n : ℝ) - (n : ℝ) / 2) =O[atTop]
          errorScale := by
  intro h
  exact h.elim

end Submissions.Erdos117LogBoundsAsymptoticAssembly.Control
