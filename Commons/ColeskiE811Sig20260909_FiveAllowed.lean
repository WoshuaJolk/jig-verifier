import Commons.ColeskiE811Sig20260909_FiveExtension
import Commons.ColeskiE811Sig20260909_PatternValidity

/- BEGIN bundled local module FiveAllowed -/

namespace ColeskiFiveAllowed
open ColeskiK4Coverage ColeskiK5Coverage ColeskiPatternAction ColeskiFiveExtension ColeskiArmCode ColeskiPatternValidity

theorem normalized_allowed (x : Pattern (Fin 5) (Fin 6)) (r : Nat)
    (h : Valid x)
    (hb : ∀ u v : Fin 4, x u.castSucc v.castSucc = ColeskiPatternFour.fromCode r u v) :
    allowedExtension r (encodeArm (arms x)) = true := by
  have h0 : good ((x 0 4).getD 0) ((x 1 4).getD 0) (digit r 0) = true := by
    have ht := h.2.2.2 4 0 1 (by decide) (by decide) (by decide)
    have hbase : x 0 1 = ColeskiPatternFour.fromCode r 0 1 := by simpa using hb 0 1
    rw [h.1 4 0,h.1 4 1,hbase] at ht
    simpa [ColeskiPatternFour.fromCode,ColeskiPatternFour.edgeIndex] using ht
  have h1 : good ((x 0 4).getD 0) ((x 2 4).getD 0) (digit r 1) = true := by
    have ht := h.2.2.2 4 0 2 (by decide) (by decide) (by decide)
    have hbase : x 0 2 = ColeskiPatternFour.fromCode r 0 2 := by simpa using hb 0 2
    rw [h.1 4 0,h.1 4 2,hbase] at ht
    simpa [ColeskiPatternFour.fromCode,ColeskiPatternFour.edgeIndex] using ht
  have h2 : good ((x 0 4).getD 0) ((x 3 4).getD 0) (digit r 2) = true := by
    have ht := h.2.2.2 4 0 3 (by decide) (by decide) (by decide)
    have hbase : x 0 3 = ColeskiPatternFour.fromCode r 0 3 := by simpa using hb 0 3
    rw [h.1 4 0,h.1 4 3,hbase] at ht
    simpa [ColeskiPatternFour.fromCode,ColeskiPatternFour.edgeIndex] using ht
  have h3 : good ((x 1 4).getD 0) ((x 2 4).getD 0) (digit r 3) = true := by
    have ht := h.2.2.2 4 1 2 (by decide) (by decide) (by decide)
    have hbase : x 1 2 = ColeskiPatternFour.fromCode r 1 2 := by simpa using hb 1 2
    rw [h.1 4 1,h.1 4 2,hbase] at ht
    simpa [ColeskiPatternFour.fromCode,ColeskiPatternFour.edgeIndex] using ht
  have h4 : good ((x 1 4).getD 0) ((x 3 4).getD 0) (digit r 4) = true := by
    have ht := h.2.2.2 4 1 3 (by decide) (by decide) (by decide)
    have hbase : x 1 3 = ColeskiPatternFour.fromCode r 1 3 := by simpa using hb 1 3
    rw [h.1 4 1,h.1 4 3,hbase] at ht
    simpa [ColeskiPatternFour.fromCode,ColeskiPatternFour.edgeIndex] using ht
  have h5 : good ((x 2 4).getD 0) ((x 3 4).getD 0) (digit r 5) = true := by
    have ht := h.2.2.2 4 2 3 (by decide) (by decide) (by decide)
    have hbase : x 2 3 = ColeskiPatternFour.fromCode r 2 3 := by simpa using hb 2 3
    rw [h.1 4 2,h.1 4 3,hbase] at ht
    simpa [ColeskiPatternFour.fromCode,ColeskiPatternFour.edgeIndex] using ht
  simp [allowedExtension,digit_encodeArm_nat,arms,h0,h1,h2,h3,h4,h5]
end ColeskiFiveAllowed
#print axioms ColeskiFiveAllowed.normalized_allowed

/- END bundled local module FiveAllowed -/
