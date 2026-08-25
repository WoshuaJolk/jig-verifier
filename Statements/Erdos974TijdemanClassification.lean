import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.Complex.Basic

namespace Statements.Erdos974TijdemanClassification

open Finset
open scoped BigOperators

/-- Tijdeman's complete two-run classification for Erdős Problem 974.
For odd cardinality the values are all roots of unity. For even cardinality
they are two distinct regular polygons on the unit circle. -/
abbrev statement : Prop :=
  (∀ {n : ℕ} [NeZero n] (z : Fin n → ℂ) (a b : ℕ),
    z 0 = 1 →
    a < b →
    (∀ k < n - 1, ∑ i, z i ^ (a + k) = 0) →
    (∀ k < n - 1, ∑ i, z i ^ (b + k) = 0) →
    Odd n →
    univ.image z = Polynomial.nthRootsFinset n 1) ∧
  (∀ {m : ℕ} [NeZero m] (z : Fin (2 * m) → ℂ) (a b : ℕ),
    z 0 = 1 →
    a < b →
    (∀ k < 2 * m - 1, ∑ i, z i ^ (a + k) = 0) →
    (∀ k < 2 * m - 1, ∑ i, z i ^ (b + k) = 0) →
    ∃ c : ℂ, ‖c‖ = 1 ∧ c ≠ 1 ∧
      univ.image z =
        Polynomial.nthRootsFinset m 1 ∪ Polynomial.nthRootsFinset m c)

theorem target : statement := by
  sorry

end Statements.Erdos974TijdemanClassification
