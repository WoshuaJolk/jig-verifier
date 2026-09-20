import Mathlib.Algebra.Order.Rearrangement
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open scoped BigOperators
open Finset

namespace Statements.J6P280NonuniformProductCapacity

def IsSidon (A : Set ℤ) : Prop :=
  ∀ ⦃a b c d : ℤ⦄, a ∈ A → b ∈ A → c ∈ A → d ∈ A →
    a + b = c + d → (a = c ∧ b = d) ∨ (a = d ∧ b = c)

section Vocabulary
variable {I : Type*} [DecidableEq I] [DecidableEq (I → ℤ)]

def relative (o : I) (u : I → ℤ) (i : I) : ℤ := u i - u o

noncomputable def patterns (o : I) (O : Finset (I → ℤ)) : Finset (I → ℤ) := by
  classical
  exact O.image (relative o)

variable [Fintype I]

def tupleValue (U : I → Finset ℤ) (u : (j : I) → U j) : I → ℤ := fun j => u j

noncomputable def independentSpace (U : I → Finset ℤ) : Finset (I → ℤ) := by
  classical
  exact Finset.univ.image (tupleValue U)

end Vocabulary

abbrev statement : Prop :=
  ∀ {I : Type*} [DecidableEq I] [DecidableEq (I → ℤ)] [Fintype I]
    (o : I) (i : Finset I) (U F : I → Finset ℤ) (f : I → ℤ → ℝ)
    (A : Set ℤ) (T K0 K D : Finset ℤ) (alpha : I → ℝ)
    (hA : IsSidon A) (hsub : ∀ j ∈ i, ∀ a ∈ F j, a ∈ A)
    (hdis : (i : Set I).PairwiseDisjoint F)
    (hFD : ∀ j ∈ i, ∀ a ∈ F j, ∀ b ∈ F j, a - b ∈ D)
    (hTD : ∀ t ∈ T, ∀ u ∈ T, u - t ∈ D)
    (hK0 : ∀ j ∈ i, ∀ a ∈ F j, ∀ t ∈ T, t + a ∈ K0)
    (hK : ∀ j ∈ i, ∀ z ∈ patterns o (independentSpace U), ∀ x ∈ K0, x + z j ∈ K)
    (hzero : 0 ∈ D) (hT : U o ⊆ T)
    (hfpos : ∀ j, ∀ x ∈ U j, 0 < f j x)
    (hfprob : ∀ j, ∑ x ∈ U j, f j x = 1)
    (hfsupport : ∀ j x, x ∉ U j → f j x = 0)
    (ha : ∀ j, 0 ≤ alpha j) (halpha : ∀ j, ∀ x ∈ U j, f j x ≤ alpha j)
    (hsize : 1 ≤ ∑ j ∈ i, ((F j).card : ℝ)),
    (∑ j ∈ i, ∑ x ∈ K, (∑ a ∈ F j, f j (x-a)) ^ 2) ≤
      1 + ((∑ j ∈ i, ((F j).card : ℝ)) - 1) *
        (((patterns o (independentSpace U)).card : ℝ) * ∏ j, alpha j)

end Statements.J6P280NonuniformProductCapacity
