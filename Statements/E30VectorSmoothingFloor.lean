import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

namespace Statements.E30VectorSmoothingFloor

open scoped BigOperators

def extendedWeight {R m L : ℕ} (w : Fin R → Fin (L * m) → ℝ)
    (r : Fin R) (j : ℕ) : ℝ :=
  if hj : j < L * m then w r ⟨j, hj⟩ else 1

def energyA {R m : ℕ} (mix : Fin R → ℝ) (p : Fin R → Fin m → ℝ) : ℝ :=
  (m : ℝ) * ∑ r, mix r * ∑ i, (p r i)^2

noncomputable def energyB {R m L : ℕ} (mix : Fin R → ℝ)
    (w : Fin R → Fin (L * m) → ℝ) : ℝ :=
  1 + 2 * ((∑ r, mix r * ∑ j, (w r j)^2) / (m : ℝ) - (L : ℝ))

/-- A uniform obstruction for the nonnegative, symmetric, diagonal
vector-smoothing framework, with no bound on its finite dimensions. -/
abbrev statement : Prop :=
  ∀ (R m L : ℕ), 0 < R → 0 < m → 0 < L →
    ∀ (mix : Fin R → ℝ) (p : Fin R → Fin m → ℝ)
      (w : Fin R → Fin (L * m) → ℝ),
      (∀ r, 0 ≤ mix r) → (∑ r, mix r) = 1 →
      (∀ r i, 0 ≤ p r i) → (∀ r, (∑ i, p r i) = 1) →
      (∀ r i, p r i = p r i.rev) →
      (∀ q : Fin (L * m + 1),
        1 ≤ ∑ r, mix r * ∑ i, p r i * extendedWeight w r (q.val + i.val)) →
      Real.pi ^ 2 ≤ 32 * energyA mix p * energyB mix w

theorem target : statement := sorry

end Statements.E30VectorSmoothingFloor
