import Commons.ColeskiE811Sig20260909_K6RealCertificate
import Commons.ColeskiE811Sig20260909_WeightedIndicator

/- BEGIN bundled local module K6SeparatorForm -/

namespace ColeskiK6SeparatorForm
open ColeskiK6RealCertificate ColeskiK6Check ColeskiOrbitChecks
open ColeskiPatternCode ColeskiOrbitCoefficient ColeskiWeightedIndicator

theorem checked_separator
    (checks : ∀ r : Fin 551, ∀ k : Fin 7200, orbitCheck r.val k.val = true)
    (r a : Nat) (ws : Array Nat) (h : checkPositive r a ws = true) :
    0 < ∑ z : Fin 6, ∑ m : Fin 5, ∑ c : Fin 6,
      coefficientFor (fromCode (deletionCode r a z.val)) (m,c) *
        ((if colorFin r a (skip z.val m.val) z.val = c then (6 : ℝ) else 0) - 1) := by
  simp_rw [sum_indicator]
  exact checked_positive checks r a ws h
end ColeskiK6SeparatorForm
#print axioms ColeskiK6SeparatorForm.checked_separator

/- END bundled local module K6SeparatorForm -/
