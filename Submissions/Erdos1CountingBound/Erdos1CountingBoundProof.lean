import Mathlib.Data.Finset.Powerset
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Range
import Mathlib.Algebra.Order.BigOperators.Group.Finset

namespace Submissions.Erdos1CountingBound.Erdos1CountingBoundProof

abbrev IsSumDistinctSet (A : Finset ℕ) (N : ℕ) : Prop :=
  A ⊆ Finset.Icc 1 N ∧
    (fun (S : A.powerset) => S.1.sum id).Injective

theorem proof : ∀ (N : ℕ) (A : Finset ℕ), IsSumDistinctSet A N →
    2 ^ A.card ≤ A.card * N + 1 := by
  intro N A h
  rw [← Finset.card_powerset]
  exact
    (Finset.card_le_card_of_injOn (Finset.sum · id)
      (fun S hS =>
        Finset.mem_range.mpr <| Nat.lt_add_one_of_le <|
          (Finset.sum_le_card_nsmul S id N fun i hi =>
            (Finset.mem_Icc.mp
              (h.1 (Finset.mem_powerset.mp hS hi))).2).trans
            (Nat.mul_le_mul_right N
              (Finset.card_le_card (Finset.mem_powerset.mp hS))))
      (fun a ha b hb hab => by
        have := @h.2 ⟨a, ha⟩ ⟨b, hb⟩ hab
        simp at this
        exact this)).trans_eq
      (Finset.card_range _)

end Submissions.Erdos1CountingBound.Erdos1CountingBoundProof
