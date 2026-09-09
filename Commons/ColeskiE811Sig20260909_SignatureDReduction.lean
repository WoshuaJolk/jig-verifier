import Statements.E811DNoBalancedBase
import Commons.ColeskiE811Sig20260909_CertificateReduction
import Commons.ColeskiE811Sig20260909_SignatureBalanceCoefficient
import Commons.ColeskiE811Sig20260909_SignatureGeneralSeparator

/- BEGIN bundled local module SignatureDReduction -/


namespace ColeskiSignatureDReduction

open Statements.E811DNoBalancedBase
open ColeskiK5Coverage ColeskiSixAllowed ColeskiK6Check ColeskiSignatureRows

set_option maxRecDepth 8000
set_option maxHeartbeats 0

theorem good_swap : ∀ a b c : Fin 6,
    ColeskiK4Coverage.good a c b = ColeskiK4Coverage.good a b c := by decide

theorem palette_good (a b c : Fin 6)
    (h : a = b ∨ b = c ∨ a = c ∨ ({a, b, c} : Finset (Fin 6)) ∈ palettes) :
    ColeskiK4Coverage.good a c b = true := by
  exact (good_swap a b c).trans ((ColeskiK4Coverage.good_iff a b c).mpr h)

theorem certificate_from_checks
    (rows : ∀ r : Fin 551, rowMatches r)
    (positive : ∀ r : Fin 551, ∀ a : Fin 7776,
      allowedExtension6 representatives5[r.val]! a.val = true →
      ∃ ws : Array Nat, checkPositive representatives5[r.val]! a.val ws = true)
    (d : Fin 6 → Fin 6 → Fin 6) (hs : ∀ u v, d u v = d v u)
    (hg : ∀ u v w, d u v = d v w ∨ d v w = d u w ∨ d u v = d u w ∨
      ({d u v, d v w, d u w} : Finset (Fin 6)) ∈ palettes) :
    0 < ∑ z : Fin 6, ∑ v : ColeskiSignatureBalanceCoefficient.Positions z,
      ∑ a : Fin 6,
      ColeskiSignatureBalanceCoefficient.weight z v (fun i j => d i.val j.val) a *
        ((if d v.val z = a then (6 : ℝ) else 0) - 1) := by
  rw [ColeskiSignatureBalanceCoefficient.weight_sum]
  apply ColeskiSignatureGeneralSeparator.positive_of_checks rows positive
  apply ColeskiColoringPattern.valid_colored d hs
  intro u v w _ _ _
  exact palette_good _ _ _ (hg u v w)

theorem target_from_checks
    (rows : ∀ r : Fin 551, rowMatches r)
    (positive : ∀ r : Fin 551, ∀ a : Fin 7776,
      allowedExtension6 representatives5[r.val]! a.val = true →
      ∃ ws : Array Nat, checkPositive representatives5[r.val]! a.val ws = true) :
    Statements.E811DNoBalancedBase.statement := by
  intro t ht c hs hd hp
  letI : Nontrivial (Fin (6 * t + 1)) := ⟨⟨⟨0, by omega⟩, ⟨1, by omega⟩, by
    intro he
    have hv := congrArg (fun i : Fin (6 * t + 1) => i.val) he
    change (0 : Nat) = 1 at hv
    omega⟩⟩
  exact ColeskiCertificateReduction.excludes_balanced_graph
    (fun a b c => ({a, b, c} : Finset (Fin 6)) ∈ palettes)
    ColeskiSignatureBalanceCoefficient.weight
    (certificate_from_checks rows positive)
    t (by simp) c hs hd hp 0

end ColeskiSignatureDReduction

#print axioms ColeskiSignatureDReduction.target_from_checks

/- END bundled local module SignatureDReduction -/
