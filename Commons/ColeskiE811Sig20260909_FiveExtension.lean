import Commons.ColeskiE811Sig20260909_PatternCode
import Commons.ColeskiE811Sig20260909_PatternFour
import Commons.ColeskiE811Sig20260909_ArmCode

/- BEGIN bundled local module FiveExtension -/

namespace ColeskiFiveExtension
open ColeskiK4Coverage ColeskiK5Coverage ColeskiPatternAction ColeskiPatternCode ColeskiArmCode

def arms (x : Pattern (Fin 5) (Fin 6)) : Fin 4 → Fin 6 := fun i => (x i.castSucc 4).getD 0

private theorem some_getD {o : Option (Fin 6)} (h : o ≠ none) : some (o.getD 0) = o := by
  cases o <;> simp_all

theorem reconstruct_extended (x : Pattern (Fin 5) (Fin 6)) (r : Nat)
    (hs : ∀ u v, x u v = x v u) (hd : ∀ u, x u u = none)
    (hf : ∀ u v, u ≠ v → x u v ≠ none)
    (hb : ∀ u v : Fin 4, x u.castSucc v.castSucc = ColeskiPatternFour.fromCode r u v) :
    fromCode (extendCode r (encodeArm (arms x))) = x := by
  have hforward (u v : Fin 5) (h : u ≠ v) : some ((x u v).getD 0) = x u v := some_getD (hf u v h)
  have hreverse (u v : Fin 5) (h : u ≠ v) : some ((x u v).getD 0) = x v u :=
    (hforward u v h).trans (hs u v)
  funext u v
  fin_cases u <;> fin_cases v
  · simpa [fromCode] using (hd 0).symm
  · simpa [fromCode, edgeIndex, extension_digits_nat, extensionDigit, ColeskiPatternFour.fromCode, ColeskiPatternFour.edgeIndex, arms, digit_encodeArm_nat] using (hb 0 1).symm
  · simpa [fromCode, edgeIndex, extension_digits_nat, extensionDigit, ColeskiPatternFour.fromCode, ColeskiPatternFour.edgeIndex, arms, digit_encodeArm_nat] using (hb 0 2).symm
  · simpa [fromCode, edgeIndex, extension_digits_nat, extensionDigit, ColeskiPatternFour.fromCode, ColeskiPatternFour.edgeIndex, arms, digit_encodeArm_nat] using (hb 0 3).symm
  · simpa [fromCode, edgeIndex, extension_digits_nat, extensionDigit, ColeskiPatternFour.fromCode, ColeskiPatternFour.edgeIndex, arms, digit_encodeArm_nat] using hforward 0 4 (by decide)
  · simpa [fromCode, edgeIndex, extension_digits_nat, extensionDigit, ColeskiPatternFour.fromCode, ColeskiPatternFour.edgeIndex, arms, digit_encodeArm_nat] using (hb 1 0).symm
  · simpa [fromCode] using (hd 1).symm
  · simpa [fromCode, edgeIndex, extension_digits_nat, extensionDigit, ColeskiPatternFour.fromCode, ColeskiPatternFour.edgeIndex, arms, digit_encodeArm_nat] using (hb 1 2).symm
  · simpa [fromCode, edgeIndex, extension_digits_nat, extensionDigit, ColeskiPatternFour.fromCode, ColeskiPatternFour.edgeIndex, arms, digit_encodeArm_nat] using (hb 1 3).symm
  · simpa [fromCode, edgeIndex, extension_digits_nat, extensionDigit, ColeskiPatternFour.fromCode, ColeskiPatternFour.edgeIndex, arms, digit_encodeArm_nat] using hforward 1 4 (by decide)
  · simpa [fromCode, edgeIndex, extension_digits_nat, extensionDigit, ColeskiPatternFour.fromCode, ColeskiPatternFour.edgeIndex, arms, digit_encodeArm_nat] using (hb 2 0).symm
  · simpa [fromCode, edgeIndex, extension_digits_nat, extensionDigit, ColeskiPatternFour.fromCode, ColeskiPatternFour.edgeIndex, arms, digit_encodeArm_nat] using (hb 2 1).symm
  · simpa [fromCode] using (hd 2).symm
  · simpa [fromCode, edgeIndex, extension_digits_nat, extensionDigit, ColeskiPatternFour.fromCode, ColeskiPatternFour.edgeIndex, arms, digit_encodeArm_nat] using (hb 2 3).symm
  · simpa [fromCode, edgeIndex, extension_digits_nat, extensionDigit, ColeskiPatternFour.fromCode, ColeskiPatternFour.edgeIndex, arms, digit_encodeArm_nat] using hforward 2 4 (by decide)
  · simpa [fromCode, edgeIndex, extension_digits_nat, extensionDigit, ColeskiPatternFour.fromCode, ColeskiPatternFour.edgeIndex, arms, digit_encodeArm_nat] using (hb 3 0).symm
  · simpa [fromCode, edgeIndex, extension_digits_nat, extensionDigit, ColeskiPatternFour.fromCode, ColeskiPatternFour.edgeIndex, arms, digit_encodeArm_nat] using (hb 3 1).symm
  · simpa [fromCode, edgeIndex, extension_digits_nat, extensionDigit, ColeskiPatternFour.fromCode, ColeskiPatternFour.edgeIndex, arms, digit_encodeArm_nat] using (hb 3 2).symm
  · simpa [fromCode] using (hd 3).symm
  · simpa [fromCode, edgeIndex, extension_digits_nat, extensionDigit, ColeskiPatternFour.fromCode, ColeskiPatternFour.edgeIndex, arms, digit_encodeArm_nat] using hforward 3 4 (by decide)
  · simpa [fromCode, edgeIndex, extension_digits_nat, extensionDigit, ColeskiPatternFour.fromCode, ColeskiPatternFour.edgeIndex, arms, digit_encodeArm_nat] using hreverse 0 4 (by decide)
  · simpa [fromCode, edgeIndex, extension_digits_nat, extensionDigit, ColeskiPatternFour.fromCode, ColeskiPatternFour.edgeIndex, arms, digit_encodeArm_nat] using hreverse 1 4 (by decide)
  · simpa [fromCode, edgeIndex, extension_digits_nat, extensionDigit, ColeskiPatternFour.fromCode, ColeskiPatternFour.edgeIndex, arms, digit_encodeArm_nat] using hreverse 2 4 (by decide)
  · simpa [fromCode, edgeIndex, extension_digits_nat, extensionDigit, ColeskiPatternFour.fromCode, ColeskiPatternFour.edgeIndex, arms, digit_encodeArm_nat] using hreverse 3 4 (by decide)
  · simpa [fromCode] using (hd 4).symm
end ColeskiFiveExtension
#print axioms ColeskiFiveExtension.reconstruct_extended

/- END bundled local module FiveExtension -/
