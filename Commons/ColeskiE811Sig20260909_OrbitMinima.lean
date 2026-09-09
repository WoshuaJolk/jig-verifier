import Commons.ColeskiE811Sig20260909_OrbitWeights

/- BEGIN bundled local module OrbitMinima -/

namespace ColeskiOrbitMinima

variable {G X I : Type*} [Group G] [MulAction G X]

/-- Distinct attained minima of an orbit-invariant search space certify that
representatives cannot lie in the same orbit. -/
theorem separate_of_minima (rep : I → X) (code : X → Nat)
    (minimum : I → Nat) (attainer : I → G)
    (attained : ∀ i, code (attainer i • rep i) = minimum i)
    (lower : ∀ i (g : G), minimum i ≤ code (g • rep i))
    (distinct : Function.Injective minimum) :
    ∀ i j (g : G), g • rep i = rep j → i = j := by
  intro i j g h
  apply distinct
  apply Nat.le_antisymm
  · have hi := lower i (attainer j*g)
    simpa only [mul_smul, h, attained] using hi
  · have hj := lower j (attainer i*g⁻¹)
    have hback : g⁻¹ • rep j = rep i := by rw [← h, inv_smul_smul]
    simpa only [mul_smul, hback, attained] using hj
end ColeskiOrbitMinima
#print axioms ColeskiOrbitMinima.separate_of_minima

/- END bundled local module OrbitMinima -/
