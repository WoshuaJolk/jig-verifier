import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Finset.Powerset

/- Source: O'Neill–Verstraëte, Graphs and Combinatorics 38:101 (2022),
   Section 5, Problem 1. This is the asymptotic question, not the stronger
   explicit constant furnished by the accompanying proof. -/
namespace Statements.OVWeightedInclusionRank

abbrev statement : Prop :=
  ∀ (p k : ℕ), p.Prime → 2 ≤ k →
    ∃ C : ℕ, 0 < C ∧ ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      ∀ M : Matrix {A : Finset (Fin n) // A.card = k}
        {B : Finset (Fin n) // B.card = n - k} (ZMod p),
        (∀ A B, M A B ≠ 0 ↔ A.val ⊆ B.val) →
        n ^ k ≤ C * M.rank ^ (p - 1)

end Statements.OVWeightedInclusionRank
