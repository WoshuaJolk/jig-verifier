import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Order.Lattice.Nat

open Filter

namespace Statements.Erdos117AbelianCoverRateStructural

/-- `ω(G) ≤ n`: every pairwise noncommuting finite subset has at most `n` elements. -/
def CliqueBound (G : Type) [Group G] (n : ℕ) : Prop :=
  ∀ s : Finset G, (∀ x ∈ s, ∀ y ∈ s, x ≠ y → x * y ≠ y * x) → s.card ≤ n

/-- A finite family of abelian subgroups whose union is the whole group. -/
def IsAbelianCover (G : Type) [Group G] (C : Finset (Subgroup G)) : Prop :=
  (∀ H ∈ C, ∀ x ∈ H, ∀ y ∈ H, x * y = y * x) ∧ ∀ g : G, ∃ H ∈ C, g ∈ H

/-- `a(G)`: the least cardinality of a finite abelian cover, `0` if there is none. -/
noncomputable def abelianCoverNumber (G : Type) [Group G] : ℕ :=
  sInf {k : ℕ | ∃ C : Finset (Subgroup G), C.card = k ∧ IsAbelianCover G C}

/-- The values `a(G)` over groups with `ω(G) ≤ n`. -/
def coverValues (n : ℕ) : Set ℕ :=
  {k : ℕ | ∃ (G : Type) (_ : Group G), CliqueBound G n ∧ abelianCoverNumber G = k}

/-- `h(n) = sup {a(G) : ω(G) ≤ n}`. -/
noncomputable def extremalCoverNumber (n : ℕ) : ℕ :=
  sSup (coverValues n)

/-- Erdős Problem 117 at the sharp exponential scale, Theorem 2.2 of
arXiv:2608.20507: `log₂ h(n) = n/2 + O(√n (log (n+2))³)`. The first two
conjuncts rule out the `sInf ∅ = 0` and `sSup` fallbacks: every clique-bounded
group has a finite abelian cover, and the values are bounded. -/
abbrev statement : Prop :=
  (∀ n : ℕ, ∀ (G : Type) [Group G], CliqueBound G n →
    ∃ C : Finset (Subgroup G), IsAbelianCover G C) ∧
  (∀ n : ℕ, BddAbove (coverValues n)) ∧
  (fun n : ℕ => Real.logb 2 (extremalCoverNumber n : ℝ) - (n : ℝ) / 2) =O[atTop]
    (fun n : ℕ => Real.sqrt (n : ℝ) * Real.log ((n : ℝ) + 2) ^ (3 : ℕ))

theorem target : statement := sorry

end Statements.Erdos117AbelianCoverRateStructural
