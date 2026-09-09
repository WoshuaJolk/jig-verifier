import Commons.ColeskiE811Sig20260909_SixNormalization
import Commons.ColeskiE811Sig20260909_DeletionCode
import Commons.ColeskiE811Sig20260909_SignatureSeparatorInvariance
import Commons.ColeskiE811Sig20260909_SignatureK6SeparatorForm

/- BEGIN bundled local module SignatureGeneralSeparator -/


namespace ColeskiSignatureGeneralSeparator

open ColeskiPatternAction ColeskiPatternValidity ColeskiPaletteAction ColeskiK5Coverage
open ColeskiPatternCode
open ColeskiSixExtension ColeskiSixAllowed ColeskiK6Check ColeskiDeletionCode
open ColeskiSignatureDeletionAction ColeskiSignatureSeparatorInvariance
open ColeskiSignatureK6SeparatorForm ColeskiSignatureRows

theorem signature_deletePattern_eq_fromCode (r a : Nat) (z : Fin 6) :
    deletePattern (sixPattern r a) z = fromCode (deletionCode r a z.val) := by
  exact ColeskiDeletionCode.deletePattern_eq_fromCode r a z

theorem checked_normalized
    (rows : ∀ r : Fin 551, rowMatches r)
    (r a : Nat) (ws : Array Nat) (h : checkPositive r a ws = true) :
    0 < separator (sixPattern r a) := by
  unfold separator term
  simp_rw [signature_deletePattern_eq_fromCode, incident_color]
  exact checked_separator rows r a ws h

theorem positive_of_checks
    (rows : ∀ r : Fin 551, rowMatches r)
    (positive : ∀ r : Fin 551, ∀ a : Fin 7776,
      allowedExtension6 representatives5[r.val]! a.val = true →
      ∃ ws : Array Nat, checkPositive representatives5[r.val]! a.val ws = true)
    (x : Pattern (Fin 6) (Fin 6)) (hx : Valid x) : 0 < separator x := by
  obtain ⟨r, a, g, ha, hg⟩ := ColeskiSixNormalization.normalize x hx
  have hn : Valid (sixPattern representatives5[r.val]! a.val) := by
    have hh := valid_transport g⁻¹ x hx
    rw [← hg, inv_smul_smul] at hh
    exact hh
  obtain ⟨ws, hws⟩ := positive r a ha
  rw [← hg, separator_transport g _ hn]
  exact checked_normalized rows _ _ ws hws

end ColeskiSignatureGeneralSeparator

#print axioms ColeskiSignatureGeneralSeparator.positive_of_checks

/- END bundled local module SignatureGeneralSeparator -/
