import Mathlib.NumberTheory.Divisors

namespace Statements.Erdos18PairMergeFails

/-- At the first four-digit block, no two of the canonical factorial-base
summands can be merged, although a nonlocal three-divisor replacement exists. -/
abbrev statement : Prop :=
  let digits : Finset ℕ := {210, 84, 7, 4}
  let replacement : Finset ℕ := {1, 24, 280}
  (∀ a ∈ digits, ∀ b ∈ digits, a < b →
      ¬(a + b ∣ Nat.factorial 7)) ∧
    replacement ⊆ (Nat.factorial 7).divisors ∧
    replacement.card = 3 ∧
    replacement.sum id = 305 ∧
    digits.sum id = 305

theorem target : statement := sorry

end Statements.Erdos18PairMergeFails
