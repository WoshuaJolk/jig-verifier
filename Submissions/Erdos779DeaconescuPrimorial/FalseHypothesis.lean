import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Prime.Nth

namespace Submissions.Erdos779DeaconescuPrimorial.FalseHypothesis

open Finset Nat
open scoped BigOperators

/-- Deaconescu's conjecture. The Lean index is shifted: `n = 1` represents
the first two source primes because `Nat.nth Nat.Prime` is zero-indexed. -/
abbrev statement : Prop :=
  ∀ n : ℕ, 1 ≤ n →
    let P := ∏ i ∈ range (n + 1), i.nth Nat.Prime
    ∃ p : ℕ, p.Prime ∧ (P + p).Prime ∧
      n.nth Nat.Prime < p ∧ p < P

theorem proof : False → statement := False.elim

end Submissions.Erdos779DeaconescuPrimorial.FalseHypothesis
