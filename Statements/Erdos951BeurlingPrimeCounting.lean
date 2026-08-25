import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Data.Finsupp.Defs
import Mathlib.Data.Real.Basic
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Topology.Algebra.Order.Floor

open Filter

namespace Statements.Erdos951BeurlingPrimeCounting

/-- The generalized integer attached to a finitely supported exponent vector. -/
def beurlingInteger (a : ℕ → ℝ) (k : ℕ →₀ ℕ) : ℝ :=
  k.prod fun i e ↦ (a i) ^ e

/-- Distinct generalized integers are separated by at least one. -/
def Separated (a : ℕ → ℝ) : Prop :=
  ∀ k l : ℕ →₀ ℕ, k ≠ l →
    |beurlingInteger a k - beurlingInteger a l| ≥ 1

/-- Erdős Problem 951: eventual comparison of a separated Beurling-prime
sequence with the ordinary prime-counting function. -/
abbrev statement : Prop :=
  ∀ a : ℕ → ℝ, 1 < a 0 → StrictMono a → Separated a →
    ∀ᶠ x : ℝ in atTop,
      {i : ℕ | a i ≤ x}.ncard ≤ Nat.primeCounting ⌊x⌋₊

theorem target : statement := sorry

end Statements.Erdos951BeurlingPrimeCounting
