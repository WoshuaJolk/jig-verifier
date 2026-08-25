import Mathlib.Combinatorics.Schnirelmann

namespace Statements.Erdos1146EssentialSmoothNumbers

open scoped Pointwise

def IsEssentialComponent (A : Set ℕ) : Prop :=
  open scoped Classical in
  ∀ B : Set ℕ,
    let b := schnirelmannDensity B
    0 < b → b < 1 →
      schnirelmannDensity ((A ∪ {0}) + (B ∪ {0})) > b

/-- Erdős problem 1146: the `2^m 3^n` smooth numbers form an essential
component for Schnirelmann density. -/
abbrev statement : Prop :=
  IsEssentialComponent {k | ∃ m n : ℕ, k = 2 ^ m * 3 ^ n}

theorem target : statement := sorry

end Statements.Erdos1146EssentialSmoothNumbers
