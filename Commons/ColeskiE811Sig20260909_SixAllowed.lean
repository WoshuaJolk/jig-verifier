import Commons.ColeskiE811Sig20260909_SixExtension

/- BEGIN bundled local module SixAllowed -/

namespace ColeskiSixAllowed
open ColeskiK4Coverage ColeskiPatternAction ColeskiPatternCode ColeskiSixExtension ColeskiArmFive ColeskiPatternValidity

def allowedExtension6 (r a : Nat) : Bool :=
  good (digit a 0) (digit a 1) (digit r 0) &&
  good (digit a 0) (digit a 2) (digit r 1) &&
  good (digit a 0) (digit a 3) (digit r 2) &&
  good (digit a 0) (digit a 4) (digit r 3) &&
  good (digit a 1) (digit a 2) (digit r 4) &&
  good (digit a 1) (digit a 3) (digit r 5) &&
  good (digit a 1) (digit a 4) (digit r 6) &&
  good (digit a 2) (digit a 3) (digit r 7) &&
  good (digit a 2) (digit a 4) (digit r 8) &&
  good (digit a 3) (digit a 4) (digit r 9)

theorem normalized_allowed (x : Pattern (Fin 6) (Fin 6)) (r : Nat)
    (h : Valid x)
    (hb : ∀ u v : Fin 5, x u.castSucc v.castSucc = fromCode r u v) :
    allowedExtension6 r (encodeArm (arms x)) = true := by
  have h0 : good ((x 0 5).getD 0) ((x 1 5).getD 0) (digit r 0) = true := by
    have ht := h.2.2.2 5 0 1 (by decide) (by decide) (by decide)
    have hbase : x 0 1 = fromCode r 0 1 := by simpa using hb 0 1
    rw [h.1 5 0,h.1 5 1,hbase] at ht
    simpa [fromCode,edgeIndex] using ht
  have h1 : good ((x 0 5).getD 0) ((x 2 5).getD 0) (digit r 1) = true := by
    have ht := h.2.2.2 5 0 2 (by decide) (by decide) (by decide)
    have hbase : x 0 2 = fromCode r 0 2 := by simpa using hb 0 2
    rw [h.1 5 0,h.1 5 2,hbase] at ht
    simpa [fromCode,edgeIndex] using ht
  have h2 : good ((x 0 5).getD 0) ((x 3 5).getD 0) (digit r 2) = true := by
    have ht := h.2.2.2 5 0 3 (by decide) (by decide) (by decide)
    have hbase : x 0 3 = fromCode r 0 3 := by simpa using hb 0 3
    rw [h.1 5 0,h.1 5 3,hbase] at ht
    simpa [fromCode,edgeIndex] using ht
  have h3 : good ((x 0 5).getD 0) ((x 4 5).getD 0) (digit r 3) = true := by
    have ht := h.2.2.2 5 0 4 (by decide) (by decide) (by decide)
    have hbase : x 0 4 = fromCode r 0 4 := by simpa using hb 0 4
    rw [h.1 5 0,h.1 5 4,hbase] at ht
    simpa [fromCode,edgeIndex] using ht
  have h4 : good ((x 1 5).getD 0) ((x 2 5).getD 0) (digit r 4) = true := by
    have ht := h.2.2.2 5 1 2 (by decide) (by decide) (by decide)
    have hbase : x 1 2 = fromCode r 1 2 := by simpa using hb 1 2
    rw [h.1 5 1,h.1 5 2,hbase] at ht
    simpa [fromCode,edgeIndex] using ht
  have h5 : good ((x 1 5).getD 0) ((x 3 5).getD 0) (digit r 5) = true := by
    have ht := h.2.2.2 5 1 3 (by decide) (by decide) (by decide)
    have hbase : x 1 3 = fromCode r 1 3 := by simpa using hb 1 3
    rw [h.1 5 1,h.1 5 3,hbase] at ht
    simpa [fromCode,edgeIndex] using ht
  have h6 : good ((x 1 5).getD 0) ((x 4 5).getD 0) (digit r 6) = true := by
    have ht := h.2.2.2 5 1 4 (by decide) (by decide) (by decide)
    have hbase : x 1 4 = fromCode r 1 4 := by simpa using hb 1 4
    rw [h.1 5 1,h.1 5 4,hbase] at ht
    simpa [fromCode,edgeIndex] using ht
  have h7 : good ((x 2 5).getD 0) ((x 3 5).getD 0) (digit r 7) = true := by
    have ht := h.2.2.2 5 2 3 (by decide) (by decide) (by decide)
    have hbase : x 2 3 = fromCode r 2 3 := by simpa using hb 2 3
    rw [h.1 5 2,h.1 5 3,hbase] at ht
    simpa [fromCode,edgeIndex] using ht
  have h8 : good ((x 2 5).getD 0) ((x 4 5).getD 0) (digit r 8) = true := by
    have ht := h.2.2.2 5 2 4 (by decide) (by decide) (by decide)
    have hbase : x 2 4 = fromCode r 2 4 := by simpa using hb 2 4
    rw [h.1 5 2,h.1 5 4,hbase] at ht
    simpa [fromCode,edgeIndex] using ht
  have h9 : good ((x 3 5).getD 0) ((x 4 5).getD 0) (digit r 9) = true := by
    have ht := h.2.2.2 5 3 4 (by decide) (by decide) (by decide)
    have hbase : x 3 4 = fromCode r 3 4 := by simpa using hb 3 4
    rw [h.1 5 3,h.1 5 4,hbase] at ht
    simpa [fromCode,edgeIndex] using ht
  simp [allowedExtension6,digit_encodeArm_nat,arms,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]
end ColeskiSixAllowed
#print axioms ColeskiSixAllowed.normalized_allowed

/- END bundled local module SixAllowed -/
