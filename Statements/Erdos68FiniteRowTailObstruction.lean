import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Real.Basic

namespace Statements.Erdos68FiniteRowTailObstruction

/-- Using the explicit common termination position `K!`, every later target
position still has a first omitted row larger than one whole target unit. -/
abbrev statement : Prop :=
  ∀ K m : ℕ, 3 ≤ K → K.factorial < m →
    (1 : ℝ) / m.factorial <
      1 / (((K + 1).factorial - 1 : ℕ) : ℝ)

theorem target : statement := sorry

end Statements.Erdos68FiniteRowTailObstruction
