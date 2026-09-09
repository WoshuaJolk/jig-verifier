import Mathlib

/- BEGIN bundled local module OrbitWeights -/

namespace ColeskiOrbitWeights

variable {G X F I : Type*} [Group G] [MulAction G X] [MulAction G F]

/-- Weights attached to representatives are independent of the chosen
transport when representative orbits are disjoint and stabilizers preserve weights. -/
theorem consistent (rep : I → X) (w : I → F → ℝ)
    (separate : ∀ i j (g : G), g • rep i = rep j → i = j)
    (stabilizer : ∀ i (g : G), g • rep i = rep i → ∀ f, w i (g • f) = w i f)
    (i j : I) (g h : G) (x : X) (f : F)
    (hg : g • rep i = x) (hh : h • rep j = x) :
    w i (g⁻¹ • f) = w j (h⁻¹ • f) := by
  have ht : (g⁻¹*h) • rep j = rep i := by
    rw [mul_smul, hh, ← hg, inv_smul_smul]
  have hij : j = i := separate j i _ ht
  subst j
  have hw := stabilizer i (g⁻¹*h) ht (h⁻¹ • f)
  simpa only [mul_smul, smul_inv_smul] using hw

noncomputable def value (rep : I → X) (w : I → F → ℝ) (x : X) (f : F) : ℝ := by
  classical
  exact if h : ∃ i : I, ∃ g : G, g • rep i = x then
    w (Classical.choose h) ((Classical.choose (Classical.choose_spec h))⁻¹ • f)
  else 0

theorem value_eq (rep : I → X) (w : I → F → ℝ)
    (separate : ∀ i j (g : G), g • rep i = rep j → i = j)
    (stabilizer : ∀ i (g : G), g • rep i = rep i → ∀ f, w i (g • f) = w i f)
    (i : I) (g : G) (x : X) (f : F) (hg : g • rep i = x) :
    value (G := G) rep w x f = w i (g⁻¹ • f) := by
  classical
  have hex : ∃ j : I, ∃ h : G, h • rep j = x := ⟨i,g,hg⟩
  simp only [value, dif_pos hex]
  exact consistent rep w separate stabilizer _ i _ g x f
    (Classical.choose_spec (Classical.choose_spec hex)) hg

/-- The resulting coefficient is invariant under simultaneous transport of the
unmarked pattern and its marked flag. -/
theorem value_transport (rep : I → X) (w : I → F → ℝ)
    (separate : ∀ i j (g : G), g • rep i = rep j → i = j)
    (stabilizer : ∀ i (g : G), g • rep i = rep i → ∀ f, w i (g • f) = w i f)
    (i : I) (g s : G) (x : X) (f : F) (hg : g • rep i = x) :
    value (G := G) rep w (s • x) (s • f) = value (G := G) rep w x f := by
  have hsg : (s*g) • rep i = s • x := by rw [mul_smul,hg]
  rw [value_eq rep w separate stabilizer i (s*g) _ _ hsg,
      value_eq rep w separate stabilizer i g _ _ hg]
  simp [mul_smul]
end ColeskiOrbitWeights
#print axioms ColeskiOrbitWeights.value_transport

/- END bundled local module OrbitWeights -/
