import Mathlib.Data.Finset.Interval
import Mathlib.Tactic

namespace Statements.Erdos44RotationGap

open Set Finset

def rot (n r x : ℕ) : ℕ := (x + n - r) % n

def ForwardDifferenceUnique (n : ℕ) (D : Finset ℕ) : Prop :=
  ∀ r ∈ D, ∀ x ∈ D, ∀ u ∈ D, ∀ v ∈ D,
    r ≠ x → u ≠ v → rot n r x = rot n u v → r = u ∧ x = v

/-- At most `K` rotation points can have another point within forward cyclic
distance `K`; hence a larger perfect-difference set has an isolating rotation. -/
abbrev statement : Prop :=
  ∀ (n K : ℕ) (D : Finset ℕ), 0 < n →
    ForwardDifferenceUnique n D →
    (∀ r ∈ D, ∀ x ∈ D, r ≠ x → 0 < rot n r x) →
    K < D.card →
      ∃ r ∈ D, ∀ x ∈ D, x ≠ r → K < rot n r x

theorem target : statement := by
  sorry

end Statements.Erdos44RotationGap
