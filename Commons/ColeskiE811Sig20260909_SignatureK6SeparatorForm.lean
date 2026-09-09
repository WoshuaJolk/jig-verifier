import Commons.ColeskiE811Sig20260909_SignatureK6RealCertificate
import Commons.ColeskiE811Sig20260909_WeightedIndicator

/- BEGIN bundled local module SignatureK6SeparatorForm -/


namespace ColeskiSignatureK6SeparatorForm

open ColeskiK6RealCertificate ColeskiK6Check ColeskiPatternCode
open ColeskiSignatureK6RealCertificate ColeskiSignatureWeights
open ColeskiSignatureRows ColeskiWeightedIndicator

theorem checked_separator
    (rows : ∀ r : Fin 551, rowMatches r)
    (r a : Nat) (ws : Array Nat) (h : checkPositive r a ws = true) :
    0 < ∑ z : Fin 6, ∑ m : Fin 5, ∑ c : Fin 6,
      coefficientFor (fromCode (deletionCode r a z.val)) (m, c) *
        ((if colorFin r a (skip z.val m.val) z.val = c then (6 : ℝ) else 0) - 1) := by
  simp_rw [sum_indicator]
  exact checked_positive rows r a ws h

end ColeskiSignatureK6SeparatorForm

#print axioms ColeskiSignatureK6SeparatorForm.checked_separator

/- END bundled local module SignatureK6SeparatorForm -/
