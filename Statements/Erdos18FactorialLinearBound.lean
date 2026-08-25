import Mathlib.NumberTheory.Divisors
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Order.Lattice.Nat

namespace Statements.Erdos18FactorialLinearBound

open Filter

def subsetSums (A : Set ℕ) : Set ℕ :=
  {n | ∃ B : Finset ℕ, ↑B ⊆ A ∧ n = ∑ i ∈ B, i}

noncomputable def practicalH (n : ℕ) : ℕ :=
  Finset.sup (Finset.Icc 1 n) fun m =>
    sInf {k | ∃ D : Finset ℕ, D ⊆ n.divisors ∧ D.card = k ∧ m ∈ subsetSums D}

/-- Erdős's published linear baseline for factorials. -/
abbrev statement : Prop :=
  ∀ᶠ n : ℕ in atTop, practicalH n.factorial < n

theorem target : statement := sorry

end Statements.Erdos18FactorialLinearBound
