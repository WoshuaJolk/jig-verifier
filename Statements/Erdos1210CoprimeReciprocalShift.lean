import Mathlib.Data.Real.Basic
import Mathlib.NumberTheory.PrimeCounting

open Finset

namespace Statements.Erdos1210CoprimeReciprocalShift

/-- Erdős Problem 1210, corrected pairwise-coprime-set formulation. -/
abbrev statement : Prop :=
  ∃ C : ℝ, ∀ n : ℕ, ∀ A : Finset ℕ,
    (∀ a ∈ A, 1 ≤ a ∧ a < n) →
    (∀ a ∈ A, ∀ b ∈ A, a ≠ b → a.Coprime b) →
      ∑ a ∈ A, (1 / ((n : ℝ) - a)) ≤
        (∑ p ∈ (range n).filter Nat.Prime, (1 / (p : ℝ))) + C

theorem target : statement := sorry

end Statements.Erdos1210CoprimeReciprocalShift
