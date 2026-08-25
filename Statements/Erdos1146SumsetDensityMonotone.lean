import Mathlib.Combinatorics.Schnirelmann

namespace Statements.Erdos1146SumsetDensityMonotone

open scoped Pointwise

noncomputable def density (A : Set ℕ) : ℝ :=
  open scoped Classical in
  schnirelmannDensity A

/-- Adjoining any component through the zero-augmented sumset cannot lower
Schnirelmann density. -/
abbrev statement : Prop :=
  ∀ A B : Set ℕ,
    density B ≤ density ((A ∪ {0}) + (B ∪ {0}))

theorem target : statement := sorry

end Statements.Erdos1146SumsetDensityMonotone
