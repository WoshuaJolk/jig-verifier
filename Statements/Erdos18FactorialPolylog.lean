import Mathlib.NumberTheory.Divisors
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Order.Lattice.Nat

namespace Statements.Erdos18FactorialPolylog

open Filter Real

/-- Sums of finite subsets of `A`. This is inlined from the vocabulary used by
Google DeepMind's formal-conjectures statement of Erdős problem 18. -/
def subsetSums (A : Set ℕ) : Set ℕ :=
  {n | ∃ B : Finset ℕ, ↑B ⊆ A ∧ n = ∑ i ∈ B, i}

/-- The worst minimum number of distinct divisors needed for targets from `1`
through `n`, matching `Erdos18.practicalH` in formal-conjectures. -/
noncomputable def practicalH (n : ℕ) : ℕ :=
  Finset.sup (Finset.Icc 1 n) fun m =>
    sInf {k | ∃ D : Finset ℕ, D ⊆ n.divisors ∧ D.card = k ∧ m ∈ subsetSums D}

/-- Erdős problem 18, strongest factorial form: `h(n!)` is eventually bounded
by a fixed power of `log n`. -/
abbrev statement : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ᶠ n : ℕ in atTop, (practicalH n.factorial : ℝ) < (log n) ^ C

theorem target : statement := sorry

end Statements.Erdos18FactorialPolylog
