import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.NumberTheory.Divisors
import Mathlib.Order.Filter.AtTopBot.Basic

namespace Statements.Erdos18PracticalPolyloglog

open Filter Real

def subsetSums (A : Set ℕ) : Set ℕ :=
  {m | ∃ B : Finset ℕ, (B : Set ℕ) ⊆ A ∧ m = ∑ i ∈ B, i}

def IsPractical (n : ℕ) : Prop :=
  ∀ m : ℕ, m ≤ n → m ∈ subsetSums (n.divisors : Set ℕ)

noncomputable def practicalH (n : ℕ) : ℕ :=
  Finset.sup (Finset.Icc 1 n) fun m =>
    sInf {k | ∃ D : Finset ℕ, D ⊆ n.divisors ∧
      D.card = k ∧ m ∈ subsetSums (D : Set ℕ)}

/-- Erdős problem 18, first conjecture: infinitely many practical numbers
have uniformly polylogarithmic-in-logarithm divisor representations. -/
abbrev statement : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∃ᶠ m : ℕ in atTop,
      IsPractical m ∧
        (practicalH m : ℝ) < (log (log m)) ^ C

theorem target : statement := sorry

end Statements.Erdos18PracticalPolyloglog
