import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.NumberTheory.SmoothNumbers
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Order.Lattice.Nat

namespace Statements.Erdos961SmoothRunPolylogBound

open Filter Real

def HasRoughInEveryWindow (k n : ℕ) : Prop :=
  ∀ m ≥ k + 1, ∃ i ∈ Set.Ico m (m + n),
    i ∉ Nat.smoothNumbers (k + 1)

noncomputable def f (k : ℕ) : ℕ :=
  sInf {n | HasRoughInEveryWindow k n}

/-- Erdős Problem 961: the maximal length of a run of integers all of whose
prime factors are at most `k` is bounded by a fixed power of `log k`. -/
abbrev statement : Prop :=
  ∃ C : ℕ, ∀ᶠ k : ℕ in atTop, (f k : ℝ) < Real.log k ^ C

theorem target : statement := sorry

end Statements.Erdos961SmoothRunPolylogBound
