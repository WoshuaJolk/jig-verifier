import Commons.ColeskiE811Sig20260909_ArmFive
import Commons.ColeskiE811Sig20260909_K6RealCertificate
import Commons.ColeskiE811Sig20260909_PatternValidity

/- BEGIN bundled local module SixExtension -/

namespace ColeskiSixExtension
open ColeskiPatternAction ColeskiPatternCode ColeskiK6Check ColeskiK6RealCertificate ColeskiArmFive

def sixPattern (r a : Nat) : Pattern (Fin 6) (Fin 6) :=
  fun u v => if u = v then none else some (colorFin r a u.val v.val)
def arms (x : Pattern (Fin 6) (Fin 6)) : Fin 5 → Fin 6 := fun i => (x i.castSucc 5).getD 0

private theorem some_getD {o : Option (Fin 6)} (h : o ≠ none) : some (o.getD 0) = o := by
  cases o <;> simp_all

theorem reconstruct_extended (x : Pattern (Fin 6) (Fin 6)) (r : Nat)
    (hs : ∀ u v, x u v = x v u) (hd : ∀ u, x u u = none)
    (hf : ∀ u v, u ≠ v → x u v ≠ none)
    (hb : ∀ u v : Fin 5, x u.castSucc v.castSucc = fromCode r u v) :
    sixPattern r (encodeArm (arms x)) = x := by
  have hforward (u v : Fin 6) (h : u ≠ v) : some ((x u v).getD 0) = x u v := some_getD (hf u v h)
  have hreverse (u v : Fin 6) (h : u ≠ v) : some ((x u v).getD 0) = x v u :=
    (hforward u v h).trans (hs u v)
  funext u v
  fin_cases u <;> fin_cases v
  · simpa [sixPattern] using (hd 0).symm
  · simpa [sixPattern,colorFin,edgeColor,fromCode,edgeIndex,arms,digit_encodeArm_nat] using (hb 0 1).symm
  · simpa [sixPattern,colorFin,edgeColor,fromCode,edgeIndex,arms,digit_encodeArm_nat] using (hb 0 2).symm
  · simpa [sixPattern,colorFin,edgeColor,fromCode,edgeIndex,arms,digit_encodeArm_nat] using (hb 0 3).symm
  · simpa [sixPattern,colorFin,edgeColor,fromCode,edgeIndex,arms,digit_encodeArm_nat] using (hb 0 4).symm
  · simpa [sixPattern,colorFin,edgeColor,fromCode,edgeIndex,arms,digit_encodeArm_nat] using hforward 0 5 (by decide)
  · simpa [sixPattern,colorFin,edgeColor,fromCode,edgeIndex,arms,digit_encodeArm_nat] using (hb 1 0).symm
  · simpa [sixPattern] using (hd 1).symm
  · simpa [sixPattern,colorFin,edgeColor,fromCode,edgeIndex,arms,digit_encodeArm_nat] using (hb 1 2).symm
  · simpa [sixPattern,colorFin,edgeColor,fromCode,edgeIndex,arms,digit_encodeArm_nat] using (hb 1 3).symm
  · simpa [sixPattern,colorFin,edgeColor,fromCode,edgeIndex,arms,digit_encodeArm_nat] using (hb 1 4).symm
  · simpa [sixPattern,colorFin,edgeColor,fromCode,edgeIndex,arms,digit_encodeArm_nat] using hforward 1 5 (by decide)
  · simpa [sixPattern,colorFin,edgeColor,fromCode,edgeIndex,arms,digit_encodeArm_nat] using (hb 2 0).symm
  · simpa [sixPattern,colorFin,edgeColor,fromCode,edgeIndex,arms,digit_encodeArm_nat] using (hb 2 1).symm
  · simpa [sixPattern] using (hd 2).symm
  · simpa [sixPattern,colorFin,edgeColor,fromCode,edgeIndex,arms,digit_encodeArm_nat] using (hb 2 3).symm
  · simpa [sixPattern,colorFin,edgeColor,fromCode,edgeIndex,arms,digit_encodeArm_nat] using (hb 2 4).symm
  · simpa [sixPattern,colorFin,edgeColor,fromCode,edgeIndex,arms,digit_encodeArm_nat] using hforward 2 5 (by decide)
  · simpa [sixPattern,colorFin,edgeColor,fromCode,edgeIndex,arms,digit_encodeArm_nat] using (hb 3 0).symm
  · simpa [sixPattern,colorFin,edgeColor,fromCode,edgeIndex,arms,digit_encodeArm_nat] using (hb 3 1).symm
  · simpa [sixPattern,colorFin,edgeColor,fromCode,edgeIndex,arms,digit_encodeArm_nat] using (hb 3 2).symm
  · simpa [sixPattern] using (hd 3).symm
  · simpa [sixPattern,colorFin,edgeColor,fromCode,edgeIndex,arms,digit_encodeArm_nat] using (hb 3 4).symm
  · simpa [sixPattern,colorFin,edgeColor,fromCode,edgeIndex,arms,digit_encodeArm_nat] using hforward 3 5 (by decide)
  · simpa [sixPattern,colorFin,edgeColor,fromCode,edgeIndex,arms,digit_encodeArm_nat] using (hb 4 0).symm
  · simpa [sixPattern,colorFin,edgeColor,fromCode,edgeIndex,arms,digit_encodeArm_nat] using (hb 4 1).symm
  · simpa [sixPattern,colorFin,edgeColor,fromCode,edgeIndex,arms,digit_encodeArm_nat] using (hb 4 2).symm
  · simpa [sixPattern,colorFin,edgeColor,fromCode,edgeIndex,arms,digit_encodeArm_nat] using (hb 4 3).symm
  · simpa [sixPattern] using (hd 4).symm
  · simpa [sixPattern,colorFin,edgeColor,fromCode,edgeIndex,arms,digit_encodeArm_nat] using hforward 4 5 (by decide)
  · simpa [sixPattern,colorFin,edgeColor,fromCode,edgeIndex,arms,digit_encodeArm_nat] using hreverse 0 5 (by decide)
  · simpa [sixPattern,colorFin,edgeColor,fromCode,edgeIndex,arms,digit_encodeArm_nat] using hreverse 1 5 (by decide)
  · simpa [sixPattern,colorFin,edgeColor,fromCode,edgeIndex,arms,digit_encodeArm_nat] using hreverse 2 5 (by decide)
  · simpa [sixPattern,colorFin,edgeColor,fromCode,edgeIndex,arms,digit_encodeArm_nat] using hreverse 3 5 (by decide)
  · simpa [sixPattern,colorFin,edgeColor,fromCode,edgeIndex,arms,digit_encodeArm_nat] using hreverse 4 5 (by decide)
  · simpa [sixPattern] using (hd 5).symm
end ColeskiSixExtension
#print axioms ColeskiSixExtension.reconstruct_extended

/- END bundled local module SixExtension -/
