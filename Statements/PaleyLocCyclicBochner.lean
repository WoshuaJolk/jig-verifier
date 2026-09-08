import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Circulant

/-!
# Finite Fourier extraction from a normalized real PSD circulant

This is standard finite Fourier theory, recorded as a reusable partial result.
It supplies the PSD-to-nonnegative-Fourier direction missing from the existing
Paley localization averaging and cosine-certificate statements. It asserts no
prime-specific coefficient bound, no Paley coordinate identification, and no
asymptotic theta estimate.

For every positive cyclic order n, a real positive semidefinite circulant with
f(0)=1 has a probability representation using all n standard characters. The
sum of f is n times the trivial-character mass. The weights are arbitrary real
numbers; rationality and a sparse Fourier support are not required.
-/

namespace Statements.PaleyLocCyclicBochner

abbrev statement : Prop :=
  ∀ (n : ℕ) [NeZero n] (f : ZMod n → ℝ),
    (Matrix.circulant f).PosSemidef → f 0 = 1 →
    ∃ μ : ZMod n → ℝ,
      (∀ j, 0 ≤ μ j) ∧
      (∑ j, μ j) = 1 ∧
      (∀ t, (f t : ℂ) = ∑ j, (μ j : ℂ) * ZMod.stdAddChar (j * t)) ∧
      (∑ t, f t) = (n : ℝ) * μ 0

theorem target : statement := sorry

end Statements.PaleyLocCyclicBochner
