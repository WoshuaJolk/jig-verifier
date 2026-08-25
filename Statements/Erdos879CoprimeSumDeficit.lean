import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.NumberTheory.PrimeCounting

/-!
# Erdős problem 879

Is the maximum sum of a pairwise-coprime subset of `{1, ..., n}` within
`n^(1+o(1))` of the Erdős--van Lint benchmark?
-/

namespace Statements.Erdos879CoprimeSumDeficit

def Admissible (S : Finset ℕ) : Prop :=
  ∀ a ∈ S, ∀ b ∈ S, a ≠ b → Nat.Coprime a b

noncomputable def G (n : ℕ) : ℕ :=
  sSup {total : ℕ |
    ∃ S : Finset ℕ,
      (∀ a ∈ S, 1 ≤ a ∧ a ≤ n) ∧
      Admissible S ∧ total = ∑ a ∈ S, a}

def H (n : ℕ) : ℕ :=
  (∑ p ∈ (Finset.range n).filter Nat.Prime, p) +
    n * Nat.primeCounting (Nat.sqrt n)

abbrev statement : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      (H n : ℝ) - (G n : ℝ) < Real.rpow n (1 + ε)

theorem target : statement := sorry

end Statements.Erdos879CoprimeSumDeficit
