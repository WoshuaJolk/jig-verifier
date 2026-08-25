import Mathlib.Data.Finset.Powerset
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.Nat.ModEq
import Mathlib.Tactic

namespace Submissions.Erdos1CRTJointFiberBarrier.Erdos1CRTJointFiberBarrierProof

abbrev IsSumDistinctSet (A : Finset ℕ) (N : ℕ) : Prop :=
  A ⊆ Finset.Icc 1 N ∧
    (fun (S : A.powerset) => S.1.sum id).Injective

private theorem modular_sum_bound (N : ℕ) (A : Finset ℕ)
    (h : IsSumDistinctSet A N) (q t k : ℕ) :
    q * (((A.powersetCard k).filter fun S => S.sum id % q = t % q).card - 1) ≤
      k * N := by
  by_cases hq : q = 0
  · simp [hq]
  let F := (A.powersetCard k).filter fun S => S.sum id % q = t % q
  have hcount : F.card ≤ k * N / q + 1 := by
    exact
      (Finset.card_le_card_of_injOn (fun S => S.sum id / q)
        (fun S hS =>
          Finset.mem_range.mpr <| Nat.lt_add_one_of_le <|
            Nat.div_le_div_right <|
              (Finset.sum_le_card_nsmul S id N fun x hx =>
                (Finset.mem_Icc.mp <| h.1 <|
                  Finset.mem_powersetCard.mp (Finset.mem_filter.mp hS).1 |>.1 hx).2).trans <|
                Nat.mul_le_mul_right N
                  (Finset.mem_powersetCard.mp (Finset.mem_filter.mp hS).1).2.le)
        (fun S hS T hT hdiv => by
          have hmod : S.sum id ≡ T.sum id [MOD q] := by
            change S.sum id % q = T.sum id % q
            exact (Finset.mem_filter.mp hS).2.trans
              (Finset.mem_filter.mp hT).2.symm
          have hsum : S.sum id = T.sum id := Nat.ext_div_modEq hdiv hmod
          have hSA : S ⊆ A :=
            (Finset.mem_powersetCard.mp (Finset.mem_filter.mp hS).1).1
          have hTA : T ⊆ A :=
            (Finset.mem_powersetCard.mp (Finset.mem_filter.mp hT).1).1
          have hST : (⟨S, Finset.mem_powerset.mpr hSA⟩ : A.powerset) =
              ⟨T, Finset.mem_powerset.mpr hTA⟩ := h.2 hsum
          exact congrArg Subtype.val hST)).trans_eq (Finset.card_range _)
  change q * (F.card - 1) ≤ k * N
  have hsub : F.card - 1 ≤ k * N / q :=
    Nat.sub_le_iff_le_add.mpr hcount
  calc
    q * (F.card - 1) ≤ q * (k * N / q) := Nat.mul_le_mul_left q hsub
    _ = (k * N / q) * q := Nat.mul_comm _ _
    _ ≤ k * N := Nat.div_mul_le_self _ _

theorem proof : ∀ (N : ℕ) (A : Finset ℕ), IsSumDistinctSet A N →
    ∀ (q₁ q₂ t₁ t₂ k : ℕ) (co : q₁.Coprime q₂), q₁ ≠ 0 → q₂ ≠ 0 →
      let c : ℕ := Nat.chineseRemainder co t₁ t₂
      let joint := (A.powersetCard k).filter fun S =>
        S.sum id % q₁ = t₁ % q₁ ∧ S.sum id % q₂ = t₂ % q₂
      let product := (A.powersetCard k).filter fun S =>
        S.sum id % (q₁ * q₂) = c % (q₁ * q₂)
      joint = product ∧ (q₁ * q₂) * (joint.card - 1) ≤ k * N := by
  intro N A h q₁ q₂ t₁ t₂ k co hq₁ hq₂
  dsimp only
  let c : ℕ := Nat.chineseRemainder co t₁ t₂
  have heq :
      ((A.powersetCard k).filter fun S =>
          S.sum id % q₁ = t₁ % q₁ ∧ S.sum id % q₂ = t₂ % q₂) =
        ((A.powersetCard k).filter fun S =>
          S.sum id % (q₁ * q₂) = c % (q₁ * q₂)) := by
    ext S
    simp only [Finset.mem_filter, and_congr_right_iff]
    intro hS
    constructor
    · intro hs
      change S.sum id ≡ c [MOD q₁ * q₂]
      apply Nat.chineseRemainder_modEq_unique co
      · exact hs.1
      · exact hs.2
    · intro hs
      have hp : S.sum id ≡ c [MOD q₁ * q₂] := hs
      have hj := (Nat.modEq_and_modEq_iff_modEq_mul co).mpr hp
      exact ⟨hj.1.trans (Nat.chineseRemainder co t₁ t₂).prop.1,
        hj.2.trans (Nat.chineseRemainder co t₁ t₂).prop.2⟩
  refine ⟨heq, ?_⟩
  rw [heq]
  exact modular_sum_bound N A h (q₁ * q₂) c k

end Submissions.Erdos1CRTJointFiberBarrier.Erdos1CRTJointFiberBarrierProof
