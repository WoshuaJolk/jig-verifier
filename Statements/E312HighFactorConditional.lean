import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Multiset.Sum
import Mathlib.Data.Nat.Factors

namespace Statements.E312HighFactorConditional

noncomputable def mass (A : Multiset ℕ) : ℝ :=
  (A.map fun n : ℕ => (n : ℝ)⁻¹).sum

def positive (A : Multiset ℕ) : Prop := ∀ n ∈ A, 0 < n

def stable (A : Multiset ℕ) : Prop :=
  (∀ n ∈ A, 2 ≤ n) ∧ ∀ n ∈ A, A.count n < n.minFac

def factorCount (n : ℕ) : ℕ := n.primeFactorsList.length

noncomputable def approximates (A : Multiset ℕ) (δ : ℝ) : Prop :=
  ∃ B : Multiset ℕ, B ≤ A ∧ 1 - δ ≤ mass B ∧ mass B ≤ 1

noncomputable def generalEstimate : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ R₀ : ℝ, 1 < R₀ ∧
    ∀ A : Multiset ℕ, positive A → R₀ ≤ mass A →
      approximates A (Real.exp (-c * Real.sqrt (mass A * Real.log (mass A))))

noncomputable def primeEstimate : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ R₀ : ℝ, 1 < R₀ ∧
    ∀ (A : Multiset ℕ) (a : ℝ),
      (∀ p ∈ A, Nat.Prime p) → 0 < a → a < 1 →
      (∀ p ∈ A, (A.count p : ℝ) / p ≤ a) → R₀ ≤ mass A →
      approximates A (Real.exp (-c * min (mass A)
        (Real.sqrt (mass A * Real.log (mass A) / a))))

noncomputable def highFactorConclusion : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ c : ℝ, 0 < c ∧ ∃ R₀ : ℝ, 1 < R₀ ∧
    ∀ A : Multiset ℕ, stable A → R₀ ≤ mass A →
      (∀ n ∈ A, C * (Real.log (mass A)) ^ 2 ≤ (factorCount n : ℝ)) →
      approximates A (Real.exp (-c * mass A))

/-- A conditional restricted-class theorem, not full Erdős 312. -/
def statement : Prop :=
  generalEstimate → primeEstimate → highFactorConclusion

end Statements.E312HighFactorConditional
