import Commons.ColeskiE811Sig20260909_ColoringPattern
import Commons.ColeskiE811Sig20260909_SignatureSeparatorInvariance

/- BEGIN bundled local module SignatureBalanceCoefficient -/


namespace ColeskiSignatureBalanceCoefficient

open ColeskiPatternAction ColeskiColoringPattern ColeskiDeletionPermutation
open ColeskiSignatureDeletionAction ColeskiSignatureSeparatorInvariance
open ColeskiSignatureWeights ColeskiFlagSignature

abbrev Positions (z : Fin 6) := {i : Fin 6 // i ≠ z}

noncomputable def restPattern (z : Fin 6)
    (d : Positions z → Positions z → Fin 6) : FivePattern :=
  coloredPattern (fun i j => d (deletionEquiv z i) (deletionEquiv z j))

noncomputable def weight (z : Fin 6) (v : Positions z)
    (d : Positions z → Positions z → Fin 6) (a : Fin 6) : ℝ :=
  coefficientFor (restPattern z d) ((deletionEquiv z).symm v, a)

theorem restPattern_from_coloring (d : Fin 6 → Fin 6 → Fin 6) (z : Fin 6) :
    restPattern z (fun i j => d i.val j.val) = deletePattern (coloredPattern d) z := by
  funext i j
  change (if i = j then none else some (d (z.succAbove i) (z.succAbove j))) =
    (if z.succAbove i = z.succAbove j then none else some (d (z.succAbove i) (z.succAbove j)))
  have he : z.succAbove i = z.succAbove j ↔ i = j := (Fin.succAboveEmb z).injective.eq_iff
  simp only [he]

theorem weight_sum (d : Fin 6 → Fin 6 → Fin 6) :
    (∑ z : Fin 6, ∑ v : Positions z, ∑ a : Fin 6,
      weight z v (fun i j => d i.val j.val) a *
        ((if d v.val z = a then (6 : ℝ) else 0) - 1)) =
      separator (coloredPattern d) := by
  unfold separator
  apply Finset.sum_congr rfl
  intro z hz
  rw [← Equiv.sum_comp (deletionEquiv z)
    (fun v => ∑ a : Fin 6, weight z v (fun i j => d i.val j.val) a *
      ((if d v.val z = a then (6 : ℝ) else 0) - 1))]
  apply Finset.sum_congr rfl
  intro m hm
  apply Finset.sum_congr rfl
  intro a ha
  unfold weight term
  rw [restPattern_from_coloring]
  simp only [Equiv.symm_apply_apply, deletionEquiv_apply, coloredPattern,
    if_neg (Fin.succAbove_ne z m), Option.getD_some]

end ColeskiSignatureBalanceCoefficient

#print axioms ColeskiSignatureBalanceCoefficient.weight_sum

/- END bundled local module SignatureBalanceCoefficient -/
