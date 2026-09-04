import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

namespace Submissions.Erdos1039SingleRootLemniscate.Direct

def MonicValue (root : ℂ) (z : ℂ) : ℂ :=
  z - root

theorem proof :
    ∀ root : ℂ, ‖root‖ ≤ 1 →
      ∀ z : ℂ, dist z root < 1 → ‖MonicValue root z‖ < 1 := by
  intro root _ z hz
  simp only [MonicValue, Complex.dist_eq] at hz
  exact hz

end Submissions.Erdos1039SingleRootLemniscate.Direct
