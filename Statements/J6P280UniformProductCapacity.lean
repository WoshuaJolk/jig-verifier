import Mathlib.Algebra.Order.Rearrangement
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Data.Fintype.BigOperators

open scoped BigOperators
open Finset

namespace Statements.J6P280UniformProductCapacity

def IsSidon (A : Set ℤ) : Prop :=
  ∀ ⦃a b c d : ℤ⦄, a ∈ A → b ∈ A → c ∈ A → d ∈ A →
    a + b = c + d → (a = c ∧ b = d) ∨ (a = d ∧ b = c)


def relative {I : Type*} (base : I) (x : I → ℤ) : I → ℤ :=
  fun i => x i - x base

noncomputable def patterns {I : Type*} (base : I) (omega : Finset (I → ℤ)) :
    Finset (I → ℤ) := by
  classical
  exact omega.image (relative base)


abbrev statement : Prop :=
  ∀ {I : Type*} [Fintype I] [DecidableEq I]
    (base : I) (F U : I → Finset ℤ) (A : Set ℤ) (K0 K D : Finset ℤ)
    (hU : ∀ j, (U j).Nonempty)
    (hA : IsSidon A)
    (hsub : ∀ j, ∀ a ∈ F j, a ∈ A)
    (hdis : (Set.univ : Set I).PairwiseDisjoint F)
    (hFD : ∀ j, ∀ a ∈ F j, ∀ b ∈ F j, a - b ∈ D)
    (hTD : ∀ t ∈ U base, ∀ u ∈ U base, u - t ∈ D)
    (hK0 : ∀ j, ∀ a ∈ F j, ∀ t ∈ U base, t + a ∈ K0)
    (hK : ∀ j, ∀ z ∈ patterns base (Fintype.piFinset U), ∀ x ∈ K0, x + z j ∈ K)
    (hzero : 0 ∈ D)
    (hsize : 1 ≤ ∑ j, ((F j).card : ℝ)),
    (∑ j, ∑ x ∈ K,
      (∑ a ∈ F j, if x - a ∈ U j then 1 / ((U j).card : ℝ) else 0) ^ 2) ≤
      1 + ((∑ j, ((F j).card : ℝ)) - 1) *
        (((patterns base (Fintype.piFinset U)).card : ℝ) /
          ((Fintype.piFinset U).card : ℝ))

end Statements.J6P280UniformProductCapacity
