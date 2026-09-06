import Mathlib.Data.Rat.BigOperators
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Tactic

namespace Statements.Erdos30VectorSmoothingCertificate942838

open scoped BigOperators

def extendedWeight (w : Fin 8 → Fin 512 → ℚ) (r : Fin 8) (j : ℕ) : ℚ :=
  if hj : j < 512 then w r ⟨j, hj⟩ else 1

def energyA (mix : Fin 8 → ℚ) (p : Fin 8 → Fin 128 → ℚ) : ℚ :=
  128 * ∑ r, mix r * ∑ i, (p r i)^2

def energyB (mix : Fin 8 → ℚ) (w : Fin 8 → Fin 512 → ℚ) : ℚ :=
  1 + 2 * ((∑ r, mix r * ∑ j, (w r j)^2) / 128 - 4)

def ValidCertificate (mix : Fin 8 → ℚ) (p : Fin 8 → Fin 128 → ℚ)
    (w : Fin 8 → Fin 512 → ℚ) : Prop :=
  (∀ r, 0 ≤ mix r) ∧ (∑ r, mix r) = 1 ∧
  (∀ r i, 0 ≤ p r i) ∧ (∀ r, (∑ i, p r i) = 1) ∧
  (∀ r i, p r i = p r i.rev) ∧
  (∀ q : Fin 513, 1 ≤ ∑ r, mix r * ∑ i, p r i * extendedWeight w r (q.val + i.val)) ∧
  0 < energyA mix p ∧ 0 < energyB mix w ∧
  energyA mix p * energyB mix w < (942838 / 1000000 : ℚ)^2

abbrev statement : Prop :=
  ∃ (mix : Fin 8 → ℚ) (p : Fin 8 → Fin 128 → ℚ) (w : Fin 8 → Fin 512 → ℚ),
    ValidCertificate mix p w

theorem target : statement := sorry

end Statements.Erdos30VectorSmoothingCertificate942838
