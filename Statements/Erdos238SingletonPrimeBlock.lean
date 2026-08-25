import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Data.Nat.Prime.Nth
import Mathlib.Order.Filter.AtTopBot.Basic

open Filter

namespace Statements.Erdos238SingletonPrimeBlock

noncomputable def primeGap (n : ℕ) : ℕ :=
  (n + 1).nth Nat.Prime - n.nth Nat.Prime

/-- The one-prime boundary case of the block predicate in Erdős Problem 238. -/
abbrev statement : Prop :=
  ∀ c₂ : ℝ, ∀ᶠ (x : ℝ) in atTop,
    ∃ f : Fin 1 → ℕ, ∃ m : ℕ,
      (∀ i, f i ≤ x ∧ f i = (m + i.1).nth Nat.Prime) ∧
      ∀ i : Fin (1 - 1), c₂ < primeGap (m + i.1)

theorem target : statement := sorry

end Statements.Erdos238SingletonPrimeBlock
