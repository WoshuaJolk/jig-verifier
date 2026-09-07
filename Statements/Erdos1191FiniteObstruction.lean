import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Set.Card.Arithmetic
import Mathlib.Order.Interval.Finset.Nat

/- A finite compactness reformulation of Jig #280 / Erdős #1191.
   The proposition is an equivalence, not a proof of the density conjecture. -/
namespace Statements.Erdos1191FiniteObstruction

def IsSidon (A : Set ℕ) : Prop :=
  ∀ ⦃a b c d : ℕ⦄,
    a ∈ A → b ∈ A → c ∈ A → d ∈ A →
      a ≤ b → c ≤ d → a + b = c + d →
        a = c ∧ b = d

noncomputable def countUpTo (A : Set ℕ) (n : ℕ) : ℕ :=
  (A ∩ Set.Icc 1 n).ncard

noncomputable def normalizedCount (A : Set ℕ) (n : ℕ) : ℝ :=
  (countUpTo A n : ℝ) / Real.sqrt n * Real.sqrt (Real.log n)

def root : Prop := ∀ A : Set ℕ, A.Infinite → IsSidon A →
  ∀ ε : ℝ, 0 < ε → ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ normalizedCount A n < ε

def finiteObstruction : Prop := ∀ ε : ℝ, 0 < ε → ∀ N : ℕ,
  ∃ M : ℕ, N ≤ M ∧ ∀ B : Set ℕ, B ⊆ Set.Icc 1 M → IsSidon B →
    ∃ n : ℕ, N ≤ n ∧ n ≤ M ∧ normalizedCount B n < ε

abbrev statement : Prop := root ↔ finiteObstruction

-- Canonical placeholder only; this module must not be imported by the submission.
theorem target : statement := by
  sorry

end Statements.Erdos1191FiniteObstruction
