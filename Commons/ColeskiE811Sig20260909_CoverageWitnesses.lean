import Commons.ColeskiE811Sig20260909_K4CoverageExtra
import Commons.ColeskiE811Sig20260909_K5CoverageExtra
import Commons.ColeskiE811Sig20260909_K4SemanticsOnly
import Commons.ColeskiE811Sig20260909_K5SemanticsOnly

/- BEGIN bundled local module CoverageWitnesses -/

namespace ColeskiCoverageWitnesses
open ColeskiK4Coverage ColeskiK5Coverage

/-- Every allowed labeled four-vertex code has a bounded explicit
representative/permutation witness. -/
theorem witness4_exists (k : Fin 46656) (h : allowed k = true) :
    ∃ w : Fin 36000, transformed (w.val+1) = k.val := by
  have hc := coverage k k.isLt
  have hw : witness k ≠ 0 ∧ witness k ≤ 36000 ∧ transformed (witness k) = k := by
    simpa [check, h, and_assoc] using hc
  refine ⟨⟨witness k-1, by omega⟩, ?_⟩
  have heq : witness k-1+1 = witness k := by omega
  simpa only [heq] using hw.2.2

/-- Every permitted one-vertex extension of a listed K4 representative has
an explicit K5 representative/permutation witness, with no search assumption. -/
theorem witness5_exists (r : Fin 25) (a : Fin 1296)
    (h : allowedExtension representatives[r.val]! a = true) :
    ∃ w : Fin 3967200,
      transformed5 (w.val+1) = extendCode representatives[r.val]! a := by
  let k := r.val*1296+a.val
  have hk : k < 32400 := by dsimp [k]; omega
  have hd : k/1296 = r.val := by dsimp [k]; omega
  have hm : k%1296 = a.val := by dsimp [k]; omega
  have hc := coverage5 k hk
  have hw : witness5 k ≠ 0 ∧ witness5 k ≤ 3967200 ∧
      transformed5 (witness5 k) = extendCode representatives[r.val]! a := by
    simpa [check5, hd, hm, h, and_assoc] using hc
  refine ⟨⟨witness5 k-1, by omega⟩, ?_⟩
  have heq : witness5 k-1+1 = witness5 k := by omega
  simpa only [heq] using hw.2.2
end ColeskiCoverageWitnesses
#print axioms ColeskiCoverageWitnesses.witness4_exists
#print axioms ColeskiCoverageWitnesses.witness5_exists

/- END bundled local module CoverageWitnesses -/
