import Mathlib.Data.Nat.Totient
import Mathlib.Data.Nat.PrimeFin
import Mathlib.Tactic

namespace Submissions.Erdos828ShiftsZeroAndMinusOne.ExplicitFamilies

theorem proof :
    Set.Infinite {n : ℕ | (Nat.totient n : ℤ) ∣ (n : ℤ)} ∧
      Set.Infinite {n : ℕ | (Nat.totient n : ℤ) ∣ (n : ℤ) - 1} := by
  constructor
  · apply Set.infinite_of_injective_forall_mem (f := fun k : ℕ => 2 ^ (k + 1))
    · intro a b hab
      apply Nat.pow_right_injective (by decide) at hab
      omega
    · intro k
      change (Nat.totient (2 ^ (k + 1)) : ℤ) ∣ (2 ^ (k + 1) : ℕ)
      rw [Nat.totient_prime_pow Nat.prime_two (by omega)]
      norm_num [pow_succ]
  · apply Nat.infinite_setOfPred_prime.mono
    intro p hp
    change (Nat.totient p : ℤ) ∣ (p : ℤ) - 1
    rw [Nat.totient_prime hp]
    norm_num [Nat.cast_sub hp.one_lt.le]

end Submissions.Erdos828ShiftsZeroAndMinusOne.ExplicitFamilies
