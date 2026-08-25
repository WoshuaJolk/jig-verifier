import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Data.Set.Lattice
import Mathlib.Order.Monotone.Basic

namespace Statements.Erdos1112GapDichotomy

open scoped BigOperators

def HasGapsIn (d₁ d₂ : ℕ) (a : ℕ → ℕ) : Prop :=
  0 < a 0 ∧ ∀ i, a i + d₁ ≤ a (i + 1) ∧ a (i + 1) ≤ a i + d₂

def kFoldSumset (k : ℕ) (a : ℕ → ℕ) : Set ℕ :=
  {n | ∃ f : Fin k → ℕ, n = ∑ j, a (f j)}

def IsLacunaryWithInt (r : ℤ) (b : ℕ → ℕ) : Prop :=
  0 < b 0 ∧ StrictMono b ∧
    ∀ i, r * (b i : ℤ) ≤ (b (i + 1) : ℤ)

def RatioWorksInt (k d₁ d₂ : ℕ) (r : ℤ) : Prop :=
  ∀ b : ℕ → ℕ, IsLacunaryWithInt r b →
    ∃ a : ℕ → ℕ, HasGapsIn d₁ d₂ a ∧
      Disjoint (kFoldSumset k a) (Set.range b)

def QuestionInt (k d₁ d₂ : ℕ) : Prop :=
  ∃ r : ℤ, RatioWorksInt k d₁ d₂ r

/-- Erdős 1112 is resolved exactly when the allowed upper gap is at least
one larger than the sumset multiplicity. -/
abbrev statement : Prop :=
  ∀ k d₁ d₂ : ℕ, 3 ≤ k → 1 ≤ d₁ → d₁ < d₂ →
    (QuestionInt k d₁ d₂ ↔ k + 1 ≤ d₂)

theorem target : statement := sorry

end Statements.Erdos1112GapDichotomy
