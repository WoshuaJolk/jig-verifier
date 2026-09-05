import Mathlib.Data.Finset.Powerset
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.Order.Archimedean.Real.Basic

/-!
# Erdős Problem 1 — distinct subset sums

The canonical statement follows `ErdosProblems/1.lean` in
`google-deepmind/formal-conjectures`.
-/

namespace Statements.Erdos1DistinctSubsetSumsRefuted

/-- A finite set `A ⊆ {1, …, N}` whose subset-sum map is injective. -/
abbrev IsSumDistinctSet (A : Finset ℕ) (N : ℕ) : Prop :=
  A ⊆ Finset.Icc 1 N ∧
    (fun (S : A.powerset) => S.1.sum id).Injective

/-- Erdős Problem 1: the largest element of a sum-distinct set is bounded below
by a positive absolute constant times `2 ^ |A|`. -/
abbrev originalStatement : Prop :=
  ∃ C > (0 : ℝ), ∀ (N : ℕ) (A : Finset ℕ), IsSumDistinctSet A N →
    N ≠ 0 → C * 2 ^ A.card < N

/-- Literal negation of the entire distinct-subset-sums root. -/
abbrev statement : Prop := ¬ originalStatement

theorem target : statement := sorry

end Statements.Erdos1DistinctSubsetSumsRefuted
