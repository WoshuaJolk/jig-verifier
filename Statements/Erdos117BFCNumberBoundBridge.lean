import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.GroupTheory.Commutator.Basic

namespace Statements.Erdos117BFCNumberBoundBridge

open Subgroup

universe u

def ConjugacyBound (G : Type u) [Group G] (r : ℕ) : Prop :=
  ∀ x : G, Nat.card {y : G // IsConj x y} ≤ r

def IsBFCNumber (G : Type u) [Group G] (n : ℕ) : Prop :=
  ConjugacyBound G n ∧ ∃ x : G, Nat.card {y : G // IsConj x y} = n

/--
Interface from the exact BFC-number formulation in Neumann--Vaughan-Lee to
the arbitrary-upper-bound formulation consumed by p/363 s=18. For a finite
group, the maximum conjugacy-class cardinality is attained. Monotonicity of
`x ↦ x^((3+5 log₂ x)/2)` on natural inputs at least one then transports the
source theorem from the exact maximum to any advertised bound `r`.
-/
abbrev statement : Prop :=
  ∀ (G : Type u) (_ : Group G) (_ : Finite G) (r : ℕ),
    (∀ n : ℕ, 1 ≤ n → IsBFCNumber G n →
      (Nat.card (commutator G) : ℝ) ≤
        (n : ℝ) ^ ((3 + 5 * Real.logb 2 n) / 2)) →
    ConjugacyBound G r →
    (Nat.card (commutator G) : ℝ) ≤
      (r : ℝ) ^ ((3 + 5 * Real.logb 2 r) / 2)

theorem target : statement := by
  sorry

end Statements.Erdos117BFCNumberBoundBridge
