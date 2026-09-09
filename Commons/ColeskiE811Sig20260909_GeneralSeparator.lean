import Commons.ColeskiE811Sig20260909_SixNormalization
import Commons.ColeskiE811Sig20260909_DeletionCode
import Commons.ColeskiE811Sig20260909_SeparatorInvariance
import Commons.ColeskiE811Sig20260909_K6SeparatorForm

/- BEGIN bundled local module GeneralSeparator -/

namespace ColeskiGeneralSeparator
open ColeskiPatternAction ColeskiPatternValidity ColeskiPaletteAction ColeskiK5Coverage
open ColeskiSixExtension ColeskiSixAllowed ColeskiK6Check ColeskiOrbitChecks
open ColeskiSeparatorInvariance ColeskiDeletionCode ColeskiK6SeparatorForm

theorem checked_normalized
    (checks : ∀ r : Fin 551, ∀ k : Fin 7200, orbitCheck r.val k.val = true)
    (r a : Nat) (ws : Array Nat) (h : checkPositive r a ws = true) :
    0 < separator (sixPattern r a) := by
  unfold separator term
  simp_rw [deletePattern_eq_fromCode,incident_color]
  exact checked_separator checks r a ws h

theorem positive_of_checks
    (checks : ∀ r : Fin 551, ∀ k : Fin 7200, orbitCheck r.val k.val = true)
    (positive : ∀ r : Fin 551, ∀ a : Fin 7776,
      allowedExtension6 representatives5[r.val]! a.val = true →
      ∃ ws : Array Nat, checkPositive representatives5[r.val]! a.val ws = true)
    (x : Pattern (Fin 6) (Fin 6)) (hx : Valid x) : 0 < separator x := by
  obtain ⟨r,a,g,ha,hg⟩ := ColeskiSixNormalization.normalize x hx
  have hn : Valid (sixPattern representatives5[r.val]! a.val) := by
    have hh := valid_transport g⁻¹ x hx
    rw [← hg,inv_smul_smul] at hh
    exact hh
  obtain ⟨ws,hws⟩ := positive r a ha
  rw [← hg,separator_transport checks g _ hn]
  exact checked_normalized checks _ _ ws hws
end ColeskiGeneralSeparator
#print axioms ColeskiGeneralSeparator.positive_of_checks

/- END bundled local module GeneralSeparator -/
