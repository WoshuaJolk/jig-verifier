import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Set.Card
import Mathlib.Data.Real.Basic

namespace Statements.Erdos39DenseInfiniteSidon

/-- Erdős Problem 39: an infinite Sidon set whose counting function is
`Ω_ε(N^(1/2-ε))` for every positive real `ε`. -/
abbrev statement : Prop :=
  ∃ A : Set ℕ, A.Infinite ∧
    (∀ i₁ ∈ A, ∀ j₁ ∈ A, ∀ i₂ ∈ A, ∀ j₂ ∈ A,
      i₁ + i₂ = j₁ + j₂ →
        (i₁ = j₁ ∧ i₂ = j₂) ∨ (i₁ = j₂ ∧ i₂ = j₁)) ∧
    ∀ ε : ℝ, 0 < ε →
      (fun N : ℕ ↦ (N : ℝ) ^ (1 / 2 - ε)) =O[Filter.atTop]
        (fun N : ℕ ↦ (((Set.Icc 1 N) ∩ A).ncard : ℝ))

theorem target : statement := sorry

end Statements.Erdos39DenseInfiniteSidon
