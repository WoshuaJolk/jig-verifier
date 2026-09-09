import Commons.ColeskiE811Sig20260909_OrbitStabilizers
import Commons.ColeskiE811Sig20260909_OrbitWeights

/- BEGIN bundled local module OrbitCoefficient -/

namespace ColeskiOrbitCoefficient
open ColeskiPatternAction ColeskiPaletteAction ColeskiOrbitChecks
open ColeskiOrbitSeparation ColeskiOrbitStabilizers ColeskiOrbitWeights

noncomputable def coefficientFor (x : Pattern (Fin 5) (Fin 6)) (f : Fin 5 × Fin 6) : ℝ :=
  value (G := G) representative coefficient x f

theorem coefficientFor_eq
    (checks : ∀ r : Fin 551, ∀ k : Fin 7200, orbitCheck r.val k.val = true)
    (i : Fin 551) (g : G) (x : Pattern (Fin 5) (Fin 6)) (f : Fin 5 × Fin 6)
    (h : g • representative i = x) : coefficientFor x f = coefficient i (g⁻¹ • f) := by
  exact value_eq representative coefficient (separated_from_checks checks)
    (stabilizers_from_checks checks) i g x f h

theorem coefficientFor_transport
    (checks : ∀ r : Fin 551, ∀ k : Fin 7200, orbitCheck r.val k.val = true)
    (i : Fin 551) (g s : G) (x : Pattern (Fin 5) (Fin 6)) (f : Fin 5 × Fin 6)
    (h : g • representative i = x) :
    coefficientFor (s • x) (s • f) = coefficientFor x f := by
  exact value_transport representative coefficient (separated_from_checks checks)
    (stabilizers_from_checks checks) i g s x f h
end ColeskiOrbitCoefficient
#print axioms ColeskiOrbitCoefficient.coefficientFor_eq
#print axioms ColeskiOrbitCoefficient.coefficientFor_transport

/- END bundled local module OrbitCoefficient -/
