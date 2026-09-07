import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.BigOperators.Group.Multiset.Basic

namespace Statements.Erdos241SignedSumPacking

open Finset

noncomputable def maxUniqueSums (N r : ℕ) : ℕ :=
  open scoped Classical in
  let candidates := (Icc 1 N).powerset.filter (fun A ↦
    ∀ m₁ m₂ : Multiset ℕ,
      m₁.card = r → m₂.card = r →
      (∀ x ∈ m₁, x ∈ A) → (∀ x ∈ m₂, x ∈ A) →
      m₁.sum = m₂.sum → m₁ = m₂)
  candidates.sup card


/-- Elementary signed-sum packing bound for the exact finite B3 extremum. -/
abbrev statement : Prop :=
  ∀ N : ℕ, 1 ≤ N →
    maxUniqueSums N 3 + maxUniqueSums N 3 * (maxUniqueSums N 3).choose 2 ≤ 3 * N - 2

theorem target : statement := sorry

end Statements.Erdos241SignedSumPacking
