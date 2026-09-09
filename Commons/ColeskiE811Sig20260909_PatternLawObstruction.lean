import Commons.ColeskiE811Sig20260909_FiniteLawSeparator
import Commons.ColeskiE811Sig20260909_GeneralSeparator

/- BEGIN bundled local module PatternLawObstruction -/


namespace ColeskiPatternLawObstruction
open ColeskiPatternAction ColeskiPatternValidity ColeskiDeletionAction
open ColeskiOrbitCoefficient ColeskiOrbitChecks ColeskiK5Coverage ColeskiSixAllowed
open ColeskiK6Check ColeskiSeparatorInvariance

theorem impossible {X : Type*} [Fintype X]
    (checks : ∀ r : Fin 551, ∀ k : Fin 7200, orbitCheck r.val k.val = true)
    (positive : ∀ r : Fin 551, ∀ a : Fin 7776,
      allowedExtension6 representatives5[r.val]! a.val = true →
      ∃ ws : Array Nat, checkPositive representatives5[r.val]! a.val ws = true)
    (mass : X → ℝ) (pattern : X → Pattern (Fin 6) (Fin 6))
    (nonnegative : ∀ x, 0 ≤ mass x)
    (normalized : ∑ x, mass x = 1)
    (supported : ∀ x, 0 < mass x → Valid (pattern x))
    (balanced : ∀ (z : Fin 6) (m : Fin 5) (c : Fin 6)
      (p : Pattern (Fin 5) (Fin 6)),
      (∑ x, if deletePattern (pattern x) z = p then
        mass x * ((if ((pattern x) (z.succAbove m) z).getD 0 = c then (6 : ℝ) else 0) - 1)
        else 0) = 0) : False := by
  classical
  let tag : (Fin 6 × Fin 5 × Fin 6) → X → Pattern (Fin 5) (Fin 6) :=
    fun i x => deletePattern (pattern x) i.1
  let weight : (Fin 6 × Fin 5 × Fin 6) → Pattern (Fin 5) (Fin 6) → ℝ :=
    fun i p => coefficientFor p (i.2.1,i.2.2)
  let moment : (Fin 6 × Fin 5 × Fin 6) → X → ℝ := fun i x =>
    (if ((pattern x) (i.1.succAbove i.2.1) i.1).getD 0 = i.2.2 then 6 else 0) - 1
  apply ColeskiFiniteLawSeparator.impossible mass tag weight moment nonnegative normalized
  · intro i p
    exact balanced i.1 i.2.1 i.2.2 p
  · intro x hx
    have hp := ColeskiGeneralSeparator.positive_of_checks checks positive (pattern x) (supported x hx)
    simpa only [Fintype.sum_prod_type, tag, weight, moment, separator, term] using hp

end ColeskiPatternLawObstruction
#print axioms ColeskiPatternLawObstruction.impossible

/- END bundled local module PatternLawObstruction -/
