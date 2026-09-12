import Mathlib.NumberTheory.Real.Irrational

namespace Statements.Erdos206ExplicitWitness

open scoped BigOperators

noncomputable def egyptianSum (S : Finset ℕ) : ℝ :=
  S.sum (fun m => (1 : ℝ) / m)

def ValidEgyptian (S : Finset ℕ) : Prop :=
  ∀ m ∈ S, 0 < m

def IsUnderapprox (S : Finset ℕ) (x : ℝ) : Prop :=
  ValidEgyptian S ∧ egyptianSum S < x

def IsBestNTerm (S : Finset ℕ) (n : ℕ) (x : ℝ) : Prop :=
  S.card = n ∧ IsUnderapprox S x ∧
    ∀ T : Finset ℕ, T.card = n → IsUnderapprox T x →
      egyptianSum T ≤ egyptianSum S

def EventuallyGreedy (x : ℝ) : Prop :=
  x > 0 ∧ ∃ (m : ℕ → ℕ), StrictMono m ∧ (∀ k, 0 < m k) ∧
    ∃ n₀ : ℕ, ∀ n ≥ n₀,
      IsBestNTerm (Finset.image m (Finset.range n)) n x

/-- The explicit-example supplement to Erdős Problem 206, formalized by
requiring an irrational non-eventually-greedy real together with rational
approximations at a fixed effective rate. -/
abbrev statement : Prop :=
  ∃ (x : ℝ) (approximate : ℕ → ℚ),
    (1 / 4 : ℝ) < x ∧ x < 1 / 2 ∧ Irrational x ∧
    ¬ EventuallyGreedy x ∧
    ∀ n : ℕ, |x - (approximate n : ℝ)| ≤ (1 / 2 : ℝ) ^ n / 2

theorem target : statement := by sorry

end Statements.Erdos206ExplicitWitness
