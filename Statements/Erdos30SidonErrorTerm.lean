import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Order.Interval.Finset.Nat

namespace Statements.Erdos30SidonErrorTerm

open Filter

def IsSidon (A : Set ℕ) : Prop :=
  ∀ i₁ ∈ A, ∀ j₁ ∈ A, ∀ i₂ ∈ A, ∀ j₂ ∈ A,
    i₁ + i₂ = j₁ + j₂ →
      (i₁ = j₁ ∧ i₂ = j₂) ∨ (i₁ = j₂ ∧ i₂ = j₁)

noncomputable def sidonNumber (N : ℕ) : ℕ := by
  classical
  exact ((Finset.Icc 1 N).powerset.filter fun (B : Finset ℕ) =>
    IsSidon (B : Set ℕ)).sup Finset.card

/-- Erdős problem 30: the maximal Sidon-set size differs from `√N` by
`O_ε(N^ε)` for every positive `ε`. -/
abbrev statement : Prop :=
  ∀ ε : ℝ, 0 < ε →
    (fun N : ℕ => (sidonNumber N : ℝ) - Real.sqrt N)
      =O[atTop] (fun N : ℕ => (N : ℝ) ^ ε)

theorem target : statement := sorry

end Statements.Erdos30SidonErrorTerm
