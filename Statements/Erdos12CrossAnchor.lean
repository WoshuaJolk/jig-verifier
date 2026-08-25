import Mathlib.Algebra.BigOperators.Field
import Mathlib.Data.Real.Basic

/-!
# Cross-anchor reciprocal-mass control

For two members `a < d` of a Property P set, reduction modulo `a` pairs
opposite residue classes in the length-`a` window immediately after `d`.
Including `d` itself in the packing leaves at most `⌊a/2⌋` later points, whose
reciprocal mass is at most `⌊a/2⌋ / d`.
-/

namespace Statements.Erdos12CrossAnchor

abbrev statement : Prop :=
  ∀ (A : Set ℕ) (B : Finset ℕ),
    (∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A,
      a ∣ b + c → a < b → a < c → b = c) →
    ∀ a ∈ A, ∀ d ∈ A, a < d →
      (∀ b ∈ B, b ∈ A ∧ d < b ∧ b < d + a) →
      (∑ b ∈ B, (1 : ℝ) / (b : ℝ)) ≤
        ((a / 2 : ℕ) : ℝ) / (d : ℝ)

theorem target : statement := sorry

end Statements.Erdos12CrossAnchor
