import Mathlib.Data.Set.Card
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Order.Interval.Set.Infinite

namespace Submissions.Erdos325BinaryToTernaryInclusion.Worker01

def IsSumTwoPower (k n : ℕ) : Prop :=
  ∃ a b, a ^ k + b ^ k = n

def IsSumThreePower (k n : ℕ) : Prop :=
  ∃ a b c, a ^ k + b ^ k + c ^ k = n

theorem proof :
    ∀ k x : ℕ, 0 < k →
      {n ∈ Set.Iic x | IsSumTwoPower k n}.ncard ≤
        {n ∈ Set.Iic x | IsSumThreePower k n}.ncard := by
  intro k x hk
  apply Set.ncard_le_ncard
  · rintro n ⟨hn, a, b, hab⟩
    refine ⟨hn, a, b, 0, ?_⟩
    simpa [zero_pow (Nat.ne_of_gt hk)] using hab
  · refine (Finset.Icc 0 x).finite_toSet.subset ?_
    intro n hn
    simp only [Set.mem_sep_iff] at hn
    simpa using hn.1

end Submissions.Erdos325BinaryToTernaryInclusion.Worker01
