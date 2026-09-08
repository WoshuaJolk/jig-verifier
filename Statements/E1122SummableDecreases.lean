import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic

namespace Statements.E1122SummableDecreases

def IsAdditive (f : ℕ → ℝ) : Prop :=
  ∀ a b : ℕ, 0 < a → 0 < b → Nat.Coprime a b →
    f (a * b) = f a + f b

def HasExactDilation (f : ℕ → ℝ) : Prop :=
  ∃ q : ℕ, 2 ≤ q ∧ ∀ n : ℕ, 0 < n → f (q * n) = f q + f n

noncomputable def decreaseWeight (f : ℕ → ℝ) (n : ℕ) : ℝ := by
  classical
  exact if 0 < n ∧ f (n + 1) < f n then 1 / (n : ℝ) else 0

abbrev statement : Prop :=
  ∀ f : ℕ → ℝ, IsAdditive f → HasExactDilation f →
    Summable (decreaseWeight f) →
    ∃ c : ℝ, 0 ≤ c ∧ ∀ n : ℕ, 0 < n → f n = c * Real.log n

theorem target : statement := by
  sorry

end Statements.E1122SummableDecreases
