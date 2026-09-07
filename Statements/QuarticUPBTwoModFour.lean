import Mathlib.Analysis.InnerProductSpace.PiL2

/-! An explicit UPB subfamily in one four-dimensional factor and qubits.
This asserts existence and unextendibility at the stated size, with no
minimum-size lower bound or general mixed-dimensional conclusion. -/
namespace Statements.QuarticUPBTwoModFour

abbrev Space (k : ℕ) := EuclideanSpace ℂ (Fin k)

def HasUPB (m t : ℕ) : Prop :=
  ∃ z : Fin m → Fin t → Space 2, ∃ x : Fin m → Space 4,
    (∀ i q, z i q ≠ 0) ∧ (∀ i, x i ≠ 0) ∧
    (∀ i j, i ≠ j →
      (∃ q, inner ℂ (z i q) (z j q) = 0) ∨ inner ℂ (x i) (x j) = 0) ∧
    (∀ az : Fin t → Space 2, ∀ ax : Space 4,
      (∀ q, az q ≠ 0) → ax ≠ 0 →
      ∃ i, (∀ q, inner ℂ (z i q) (az q) ≠ 0) ∧ inner ℂ (x i) ax ≠ 0)

abbrev statement : Prop :=
  ∀ N : ℕ, 3 ≤ N → HasUPB (4*N+2) (4*N-3)

theorem target : statement := sorry

end Statements.QuarticUPBTwoModFour
