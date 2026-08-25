import Mathlib.Data.Finset.Pairwise
import Mathlib.Data.Nat.Prime.Nth

/-!
# A finite obstruction for Erdős problem 852

A run of pairwise distinct prime gaps all bounded by `B` has length at most
`B + 1`, by the pigeonhole principle.
-/

namespace Statements.Erdos852BoundedDistinctRun

noncomputable def primeGap (n : ℕ) : ℕ :=
  Nat.nth Nat.Prime (n + 1) - Nat.nth Nat.Prime n

def DistinctRun (start length : ℕ) : Prop :=
  (Finset.range length : Set ℕ).Pairwise fun i j =>
    primeGap (start + i) ≠ primeGap (start + j)

abbrev statement : Prop :=
  ∀ start length B : ℕ,
    DistinctRun start length →
      (∀ i < length, primeGap (start + i) ≤ B) →
        length ≤ B + 1

theorem target : statement := sorry

end Statements.Erdos852BoundedDistinctRun
