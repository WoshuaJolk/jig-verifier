import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Order.Lattice.Nat

open Filter

namespace Statements.Erdos117AbelianCoverRate

/-- A group presented in the ambient Lean universe. Packaging the carrier with
its group law lets the extremum range over all groups, as in the source. -/
structure PresentedGroup where
  Carrier : Type
  group : Group Carrier

instance (G : PresentedGroup) : Group G.Carrier := G.group

/-- A finite subset is pairwise noncommuting when every two distinct members
fail to commute. -/
def PairwiseNoncommuting (G : PresentedGroup) (s : Finset G.Carrier) : Prop :=
  ∀ x ∈ s, ∀ y ∈ s, x ≠ y → x * y ≠ y * x

/-- `CliqueBound G n` is the source condition `ω(G) ≤ n`, without requiring
the maximum clique to have been chosen. -/
def CliqueBound (G : PresentedGroup) (n : ℕ) : Prop :=
  ∀ s : Finset G.Carrier, PairwiseNoncommuting G s → s.card ≤ n

/-- An abelian subgroup, stated pointwise to avoid any typeclass ambiguity. -/
def IsAbelianSubgroup {G : PresentedGroup} (H : Subgroup G.Carrier) : Prop :=
  ∀ x ∈ H, ∀ y ∈ H, x * y = y * x

/-- A finite family of abelian subgroups whose union is the whole group. -/
def IsAbelianCover (G : PresentedGroup)
    (C : Finset (Subgroup G.Carrier)) : Prop :=
  (∀ H ∈ C, IsAbelianSubgroup H) ∧
    ∀ x : G.Carrier, ∃ H ∈ C, x ∈ H

/-- The least cardinality of a finite abelian-subgroup cover. This agrees with
the source's `a(G)` whenever such a cover exists. -/
noncomputable def abelianCoverNumber (G : PresentedGroup) : ℕ :=
  sInf {k : ℕ | ∃ C : Finset (Subgroup G.Carrier),
    C.card = k ∧ IsAbelianCover G C}

/-- Covering numbers attained by groups with noncommuting clique number at
most `n`. -/
def coverValues (n : ℕ) : Set ℕ :=
  {k : ℕ | ∃ G : PresentedGroup,
    CliqueBound G n ∧ abelianCoverNumber G = k}

/-- The source's extremal function
`h(n) = sup {a(G) : ω(G) ≤ n}`. -/
noncomputable def extremalCoverNumber (n : ℕ) : ℕ :=
  sSup (coverValues n)

/-- Erdős Problem 117 at the sharp exponential scale, exactly Theorem 2.2 of
Lecomte (arXiv:2608.20507v1). The first conjunct prevents the `Nat.sInf ∅ = 0`
fallback from silently treating a group with no finite abelian cover as having
covering number zero. -/
abbrev statement : Prop :=
  (∀ n : ℕ, ∀ G : PresentedGroup, CliqueBound G n →
    ∃ C : Finset (Subgroup G.Carrier), IsAbelianCover G C) ∧
  (∀ n : ℕ, BddAbove (coverValues n)) ∧
  (fun n : ℕ =>
      Real.logb 2 (extremalCoverNumber n : ℝ) - (n : ℝ) / 2) =O[atTop]
    (fun n : ℕ =>
      Real.sqrt (n : ℝ) * Real.log ((n : ℝ) + 2) ^ (3 : ℕ))

theorem target : statement := sorry

end Statements.Erdos117AbelianCoverRate
