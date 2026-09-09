import Commons.ColeskiE811Sig20260909_FiveNormalization
import Commons.ColeskiE811Sig20260909_OrbitCoefficient

/- BEGIN bundled local module ValidCoefficient -/

namespace ColeskiValidCoefficient
open ColeskiPatternAction ColeskiPatternValidity ColeskiPaletteAction
open ColeskiOrbitChecks ColeskiOrbitCoefficient

theorem transport_valid
    (checks : ∀ r : Fin 551, ∀ k : Fin 7200, orbitCheck r.val k.val = true)
    (x : Pattern (Fin 5) (Fin 6)) (hx : Valid x) (s : G) (f : Fin 5 × Fin 6) :
    coefficientFor (s • x) (s • f) = coefficientFor x f := by
  obtain ⟨i,g,hg⟩ := ColeskiFiveNormalization.normalize x hx
  exact coefficientFor_transport checks i g s x f hg
end ColeskiValidCoefficient
#print axioms ColeskiValidCoefficient.transport_valid

/- END bundled local module ValidCoefficient -/
