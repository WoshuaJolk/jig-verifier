import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.GroupTheory.GroupAction.ConjAct
import Mathlib.GroupTheory.Index

namespace Statements.Erdos117BFCSourceInterface

open Subgroup

universe u

/-- Source-interface and endpoint reduction for the Neumann--Vaughan-Lee
`r`-BFC theorem.

For finite groups this identifies the paper's BFC number
`[G : C_G(x)]` with the cardinality of Mathlib's `IsConj` subtype, proves
the corresponding pointwise-bound equivalence, and discharges both the
`r = 1` and abelian branches of

`|G'| ≤ r ^ ((3 + 5 * log₂ r) / 2)`.

The nonabelian `r ≥ 2` estimate is deliberately not asserted. -/
abbrev statement : Prop :=
  ∀ (G : Type u) (_ : Group G) (_ : Finite G),
    (∀ x : G,
      Nat.card {y : G // IsConj x y} = (centralizer {x}).index) ∧
    (∀ r : ℕ,
      (∀ x : G, Nat.card {y : G // IsConj x y} ≤ r) ↔
      (∀ x : G, (centralizer {x}).index ≤ r)) ∧
    ((∀ x : G, Nat.card {y : G // IsConj x y} ≤ 1) →
      IsMulCommutative G ∧ Nat.card (commutator G) = 1) ∧
    (∀ r : ℕ, 1 ≤ r → IsMulCommutative G →
      (Nat.card (commutator G) : ℝ) ≤
        (r : ℝ) ^ ((3 + 5 * Real.logb 2 r) / 2))

theorem target : statement := sorry

end Statements.Erdos117BFCSourceInterface
