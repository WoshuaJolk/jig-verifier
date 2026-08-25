import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Finset.Interval
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.Order.Archimedean.Real.Basic

open scoped BigOperators

namespace Statements.Erdos68FiniteScaledResidueFormula

/-- Scaling the finite sum by `m!` splits it into an explicit integer quotient
sum and a finite sum of normalized modular residues. Consequently its floor is
the quotient sum plus the floor of the residue sum; the newest residue is 1. -/
abbrev statement : Prop :=
  ∀ m : ℕ, 3 ≤ m →
    let A : ℕ :=
      ∑ n ∈ Finset.Icc 2 m,
        m.factorial / (n.factorial - 1)
    let R : ℝ :=
      ∑ n ∈ Finset.Icc 2 m,
        (m.factorial % (n.factorial - 1) : ℕ) /
          ((n.factorial - 1 : ℕ) : ℝ)
    (m.factorial : ℝ) *
        ∑ n ∈ Finset.Icc 2 m,
          (1 : ℝ) / (n.factorial - 1 : ℕ) =
      A + R ∧
    ⌊(m.factorial : ℝ) *
        ∑ n ∈ Finset.Icc 2 m,
          (1 : ℝ) / (n.factorial - 1 : ℕ)⌋ =
      (A : ℤ) + ⌊R⌋ ∧
    m.factorial % (m.factorial - 1) = 1

theorem target : statement := sorry

end Statements.Erdos68FiniteScaledResidueFormula
