import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# EllipticUPBTwoFourEven

Proposed infinite family derived from `EllipticBipartiteSeedFamily`.

For even `k ≥ 4` and even `t ≥ k+4` with `t+k` divisible by four, there is
an unextendible product basis of exactly

    M = t + k + 4 = f_N(2^[t], 4, k) + 1

states in `(ℂ²)^⊗t ⊗ ℂ⁴ ⊗ ℂᵏ`.
-/

namespace Statements.EllipticUPBTwoFourEven

abbrev statement : Prop :=
  ∀ k t : ℕ, 4 ≤ k → Even k → k + 4 ≤ t → (t + k) % 4 = 0 →
    let M := t + k + 4
    ∃ z : Fin M → Fin t → EuclideanSpace ℂ (Fin 2),
    ∃ y : Fin M → EuclideanSpace ℂ (Fin 4),
    ∃ x : Fin M → EuclideanSpace ℂ (Fin k),
      (∀ i q, z i q ≠ 0) ∧ (∀ i, y i ≠ 0 ∧ x i ≠ 0) ∧
      (∀ i i', i ≠ i' →
        (∃ q, inner ℂ (z i q) (z i' q) = 0) ∨
        inner ℂ (y i) (y i') = 0 ∨
        inner ℂ (x i) (x i') = 0) ∧
      (∀ az : Fin t → EuclideanSpace ℂ (Fin 2),
        ∀ ay : EuclideanSpace ℂ (Fin 4),
        ∀ ax : EuclideanSpace ℂ (Fin k),
        (∀ q, az q ≠ 0) → ay ≠ 0 → ax ≠ 0 →
        ∃ i,
          (∀ q, inner ℂ (z i q) (az q) ≠ 0) ∧
          inner ℂ (y i) ay ≠ 0 ∧
          inner ℂ (x i) ax ≠ 0)

theorem target : statement := sorry

end Statements.EllipticUPBTwoFourEven
