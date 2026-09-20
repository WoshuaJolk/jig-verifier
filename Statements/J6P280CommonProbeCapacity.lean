import Mathlib.Algebra.Order.Rearrangement
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open scoped BigOperators
open Finset

namespace Statements.J6P280CommonProbeCapacity

def IsSidon (A : Set ℤ) : Prop :=
  ∀ ⦃a b c d : ℤ⦄, a ∈ A → b ∈ A → c ∈ A → d ∈ A →
    a + b = c + d → (a = c ∧ b = d) ∨ (a = d ∧ b = c)


abbrev statement : Prop :=
  ∀ {I : Type*} [DecidableEq I]
    (i : Finset I) (F : I → Finset ℤ) (A : Set ℤ)
    (T K D : Finset ℤ) (mu : ℤ → ℝ) (hA : IsSidon A)
    (hsub : ∀ j ∈ i, ∀ a ∈ F j, a ∈ A)
    (hdis : (i : Set I).PairwiseDisjoint F)
    (hFD : ∀ j ∈ i, ∀ a ∈ F j, ∀ b ∈ F j, a - b ∈ D)
    (hTD : ∀ t ∈ T, ∀ u ∈ T, u - t ∈ D)
    (hK : ∀ j ∈ i, ∀ a ∈ F j, ∀ t ∈ T, t + a ∈ K)
    (hzero : 0 ∈ D) (hmu : ∀ t, 0 ≤ mu t)
    (hsupport : ∀ t, t ∉ T → mu t = 0)
    (hprob : ∑ t ∈ T, mu t = 1),
    (∑ j ∈ i, ∑ x ∈ K, (∑ a ∈ F j, mu (x - a)) ^ 2) ≤
      1 + ((∑ j ∈ i, ((F j).card : ℝ)) - 1) * (∑ t ∈ T, (mu t) ^ 2)

end Statements.J6P280CommonProbeCapacity
