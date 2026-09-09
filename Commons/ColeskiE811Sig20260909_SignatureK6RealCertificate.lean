import Commons.ColeskiE811Sig20260909_K6RealCertificate
import Commons.ColeskiE811Sig20260909_SignatureWitnessCoefficient

/- BEGIN bundled local module SignatureK6RealCertificate -/


namespace ColeskiSignatureK6RealCertificate

open ColeskiK4Coverage ColeskiK5Coverage ColeskiPatternCode ColeskiK6Check
open ColeskiK6RealCertificate ColeskiSignatureWitnessCoefficient
open ColeskiSignatureWeights ColeskiSignatureRows

set_option maxRecDepth 100000
set_option maxHeartbeats 0

noncomputable def realTotal (r a : Nat) : ℝ :=
  ∑ z : Fin 6, ∑ m : Fin 5,
    (6 * coefficientFor (fromCode (deletionCode r a z.val))
      (m, colorFin r a (skip z.val m.val) z.val) -
    ∑ c : Fin 6, coefficientFor (fromCode (deletionCode r a z.val)) (m, c))

theorem coefficient_at_deletion
    (rows : ∀ r : Fin 551, rowMatches r)
    (r a : Nat) (ws : Array Nat) (h : checkPositive r a ws = true)
    (z : Fin 6) (flag : Fin 5 × Fin 6) :
    coefficientFor (fromCode (deletionCode r a z.val)) flag =
      (flagWeight ws[z.val]! flag.1.val flag.2.val : ℝ) := by
  have hd := List.all_eq_true.mp (Bool.and_eq_true_iff.mp h).1
    z.val (List.mem_range.mpr z.isLt)
  have ht : 0 < ws[z.val]! ∧ ws[z.val]! ≤ 3967200 ∧
      transformed5 ws[z.val]! = deletionCode r a z.val := by
    simpa [deletionCheck, and_assoc] using hd
  let w : Fin 3967200 := ⟨ws[z.val]! - 1, by omega⟩
  have he : w.val + 1 = ws[z.val]! := by dsimp [w]; omega
  have hw : transformed5 (w.val + 1) = deletionCode r a z.val := by
    rw [he]
    exact ht.2.2
  simpa only [he] using coefficient_witness rows w (deletionCode r a z.val) hw flag

theorem realTotal_eq
    (rows : ∀ r : Fin 551, rowMatches r)
    (r a : Nat) (ws : Array Nat) (h : checkPositive r a ws = true) :
    realTotal r a = (total r a ws : ℝ) := by
  unfold realTotal total
  rw [cast_sum6]
  apply Finset.sum_congr rfl
  intro z hz
  rw [cast_sum5]
  apply Finset.sum_congr rfl
  intro m hm
  simp_rw [coefficient_at_deletion rows r a ws h z]
  simp only [contribution, Int.cast_sub, Int.cast_mul, Int.cast_ofNat, cast_sum6, colorFin]

theorem checked_positive
    (rows : ∀ r : Fin 551, rowMatches r)
    (r a : Nat) (ws : Array Nat) (h : checkPositive r a ws = true) :
    0 < realTotal r a := by
  have hp : 0 < total r a ws := of_decide_eq_true (Bool.and_eq_true_iff.mp h).2
  rw [realTotal_eq rows r a ws h]
  exact_mod_cast hp

end ColeskiSignatureK6RealCertificate

#print axioms ColeskiSignatureK6RealCertificate.checked_positive

/- END bundled local module SignatureK6RealCertificate -/
