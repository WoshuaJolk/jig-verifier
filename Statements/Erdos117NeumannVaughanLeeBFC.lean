import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.GroupTheory.Commutator.Basic

namespace Statements.Erdos117NeumannVaughanLeeBFC

open Subgroup

universe u

def ConjugacyBound (G : Type u) [Group G] (r : ℕ) : Prop :=
  ∀ x : G, Nat.card {y : G // IsConj x y} ≤ r

def IsBFCNumber (G : Type u) [Group G] (n : ℕ) : Prop :=
  ConjugacyBound G n ∧ ∃ x : G, Nat.card {y : G // IsConj x y} = n

/--
Finite-group specialization of the general bound proved by
Neumann--Vaughan-Lee, *An Essay on BFC Groups*, Proc. London Math. Soc.
(3) 35 (1977), 213--237.

The original theorem is stated for an arbitrary BFC group whose BFC-number
`n` is the maximum conjugacy-class cardinality. Cartwright's authorial survey,
*Bounded Conjugacy Conditions*, Theorem 5(ii), transcribes the result exactly:
the logarithm is base two and the printed inequality is non-strict. This target
keeps the exact-maximum assumption; p/363's separately verified finite-maximum
bridge converts it to the arbitrary-upper-bound interface consumed by s=18.
-/
abbrev statement : Prop :=
  ∀ (G : Type u) (_ : Group G) (_ : Finite G) (n : ℕ),
    IsBFCNumber G n →
    (Nat.card (commutator G) : ℝ) ≤
      (n : ℝ) ^ ((3 + 5 * Real.logb 2 n) / 2)

theorem target : statement := by
  sorry

end Statements.Erdos117NeumannVaughanLeeBFC
