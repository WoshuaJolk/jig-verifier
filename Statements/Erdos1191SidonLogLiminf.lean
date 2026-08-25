import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Set.Card.Arithmetic
import Mathlib.Order.Interval.Finset.Nat

/-!
# Erdős problem 1191

Must every infinite Sidon set have logarithmically normalized lower density
equal to zero?
-/

namespace Statements.Erdos1191SidonLogLiminf

def IsSidon (A : Set ℕ) : Prop :=
  ∀ ⦃a b c d : ℕ⦄,
    a ∈ A → b ∈ A → c ∈ A → d ∈ A →
      a ≤ b → c ≤ d → a + b = c + d →
        a = c ∧ b = d

noncomputable def countUpTo (A : Set ℕ) (n : ℕ) : ℕ :=
  (A ∩ Set.Icc 1 n).ncard

noncomputable def normalizedCount (A : Set ℕ) (n : ℕ) : ℝ :=
  (countUpTo A n : ℝ) / Real.sqrt n * Real.sqrt (Real.log n)

abbrev statement : Prop :=
  ∀ A : Set ℕ, A.Infinite → IsSidon A →
    ∀ ε : ℝ, 0 < ε →
      ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ normalizedCount A n < ε

theorem target : statement := sorry

end Statements.Erdos1191SidonLogLiminf
