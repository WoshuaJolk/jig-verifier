import Mathlib.Data.Finset.Powerset
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Data.Nat.ModEq

namespace Statements.Erdos1CRTJointFiberBarrier

abbrev IsSumDistinctSet (A : Finset ℕ) (N : ℕ) : Prop :=
  A ⊆ Finset.Icc 1 N ∧
    (fun (S : A.powerset) => S.1.sum id).Injective

/-- Exact joint residue fibers for two coprime moduli are just fibers modulo
the product, and hence satisfy only the product-modulus interval bound. -/
abbrev statement : Prop :=
  ∀ (N : ℕ) (A : Finset ℕ), IsSumDistinctSet A N →
    ∀ (q₁ q₂ t₁ t₂ k : ℕ) (co : q₁.Coprime q₂), q₁ ≠ 0 → q₂ ≠ 0 →
      let c : ℕ := Nat.chineseRemainder co t₁ t₂
      let joint := (A.powersetCard k).filter fun S =>
        S.sum id % q₁ = t₁ % q₁ ∧ S.sum id % q₂ = t₂ % q₂
      let product := (A.powersetCard k).filter fun S =>
        S.sum id % (q₁ * q₂) = c % (q₁ * q₂)
      joint = product ∧ (q₁ * q₂) * (joint.card - 1) ≤ k * N

theorem target : statement := sorry

end Statements.Erdos1CRTJointFiberBarrier
