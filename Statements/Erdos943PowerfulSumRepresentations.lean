import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Finset.NatAntidiagonal
import Mathlib.Data.Nat.PrimeFin

open Asymptotics Filter

namespace Statements.Erdos943PowerfulSumRepresentations

/-- A natural number is powerful when every prime divisor occurs at
least to the second power. -/
def Powerful (n : ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → p ∣ n → p ^ 2 ∣ n

/-- Ordered representations of `n` as a sum of two powerful numbers. -/
noncomputable def sumRep (n : ℕ) : ℕ := by
  classical
  exact ((Finset.antidiagonal n).filter
    (fun pair : ℕ × ℕ => Powerful pair.1 ∧ Powerful pair.2)).card

/-- Erdős Problem 943: the number of representations as a sum of two
powerful numbers should have subpolynomial pointwise growth. -/
abbrev statement : Prop :=
  ∃ o : ℕ → ℝ, o =o[atTop] (1 : ℕ → ℝ) ∧
    ∀ᶠ n in atTop, (sumRep n : ℝ) ≤ (n : ℝ) ^ (o n)

theorem target : statement := sorry

end Statements.Erdos943PowerfulSumRepresentations
