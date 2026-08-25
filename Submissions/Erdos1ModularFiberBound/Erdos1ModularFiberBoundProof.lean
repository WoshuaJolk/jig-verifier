import Mathlib.Data.Finset.Powerset
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.BigOperators.ModEq
import Mathlib.Tactic

open scoped BigOperators

namespace Submissions.Erdos1ModularFiberBound.Erdos1ModularFiberBoundProof

abbrev IsSumDistinctSet (A : Finset ℕ) (N : ℕ) : Prop :=
  A ⊆ Finset.Icc 1 N ∧
    (fun (S : A.powerset) => S.1.sum id).Injective

theorem proof : ∀ (N : ℕ) (A : Finset ℕ), IsSumDistinctSet A N →
    ∀ (q r k : ℕ),
      q * (Nat.choose (A.filter fun a => a % q = r % q).card k - 1) ≤ k * N := by
  intro N A h q r k
  by_cases hq : q = 0
  · simp [hq]
  let B := A.filter fun a => a % q = r % q
  have hBA : B ⊆ A := Finset.filter_subset _ _
  have hcount : Nat.choose B.card k ≤ k * N / q + 1 := by
    rw [← Finset.card_powersetCard]
    exact
      (Finset.card_le_card_of_injOn (fun S => S.sum id / q)
        (fun S hS =>
          Finset.mem_range.mpr <| Nat.lt_add_one_of_le <|
            Nat.div_le_div_right <|
              (Finset.sum_le_card_nsmul S id N fun x hx =>
                (Finset.mem_Icc.mp <| h.1 <| hBA <|
                  Finset.mem_powersetCard.mp hS |>.1 hx).2).trans <|
                Nat.mul_le_mul_right N (Finset.mem_powersetCard.mp hS).2.le)
        (fun S hS T hT hdiv => by
          have hSmod : S.sum id ≡ k * r [MOD q] := by
            calc
              S.sum id ≡ ∑ _x ∈ S, r [MOD q] := Nat.ModEq.sum fun x hx => by
                change x % q = r % q
                exact (Finset.mem_filter.mp <|
                  Finset.mem_powersetCard.mp hS |>.1 hx).2
              _ = k * r := by
                simp [(Finset.mem_powersetCard.mp hS).2]
          have hTmod : T.sum id ≡ k * r [MOD q] := by
            calc
              T.sum id ≡ ∑ _x ∈ T, r [MOD q] := Nat.ModEq.sum fun x hx => by
                change x % q = r % q
                exact (Finset.mem_filter.mp <|
                  Finset.mem_powersetCard.mp hT |>.1 hx).2
              _ = k * r := by
                simp [(Finset.mem_powersetCard.mp hT).2]
          have hsum : S.sum id = T.sum id :=
            Nat.ext_div_modEq hdiv (hSmod.trans hTmod.symm)
          have hSA : S ⊆ A := fun x hx =>
            hBA ((Finset.mem_powersetCard.mp hS).1 hx)
          have hTA : T ⊆ A := fun x hx =>
            hBA ((Finset.mem_powersetCard.mp hT).1 hx)
          have hST : (⟨S, Finset.mem_powerset.mpr hSA⟩ : A.powerset) =
              ⟨T, Finset.mem_powerset.mpr hTA⟩ := h.2 hsum
          exact congrArg Subtype.val hST)).trans_eq (Finset.card_range _)
  change q * (Nat.choose B.card k - 1) ≤ k * N
  have hsub : Nat.choose B.card k - 1 ≤ k * N / q :=
    Nat.sub_le_iff_le_add.mpr hcount
  calc
    q * (Nat.choose B.card k - 1) ≤ q * (k * N / q) :=
      Nat.mul_le_mul_left q hsub
    _ = (k * N / q) * q := Nat.mul_comm _ _
    _ ≤ k * N := Nat.div_mul_le_self _ _

end Submissions.Erdos1ModularFiberBound.Erdos1ModularFiberBoundProof
