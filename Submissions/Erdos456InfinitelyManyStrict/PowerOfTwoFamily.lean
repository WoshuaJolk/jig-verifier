import Mathlib.Data.Nat.Totient
import Mathlib.NumberTheory.LSeries.PrimesInAP
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Tactic

open Nat

namespace Submissions.Erdos456InfinitelyManyStrict.PowerOfTwoFamily

noncomputable def p (n : ℕ) : ℕ :=
  sInf {q | q.Prime ∧ q ≡ 1 [MOD n]}

noncomputable def m (n : ℕ) : ℕ :=
  sInf {q | 0 < q ∧ n ∣ totient q}

theorem proof : {n | m n < p n}.Infinite := by
  apply Set.infinite_of_injective_forall_mem (f := fun j : ℕ => 2 ^ (2 * j + 3))
  · intro a b hab
    apply Nat.pow_right_injective (by decide) at hab
    omega
  · intro j
    let k := 2 * j + 3
    change m (2 ^ k) < p (2 ^ k)
    have hm : m (2 ^ k) ≤ 2 ^ (k + 1) := by
      unfold m
      refine Nat.sInf_le ⟨by positivity, ?_⟩
      rw [Nat.totient_prime_pow Nat.prime_two (by omega)]
      norm_num
    have hp : 2 ^ (k + 1) + 1 ≤ p (2 ^ k) := by
      unfold p
      let q := sInf {x | x.Prime ∧ x ≡ 1 [MOD 2 ^ k]}
      change 2 ^ (k + 1) + 1 ≤ q
      have hne : {x | x.Prime ∧ x ≡ 1 [MOD 2 ^ k]}.Nonempty := by
        obtain ⟨r, _, hr, hmod⟩ := Nat.forall_exists_prime_gt_and_modEq 0
          (pow_ne_zero k (by decide)) (Nat.coprime_one_left (2 ^ k))
        exact ⟨r, hr, hmod⟩
      obtain ⟨hprime, hmod⟩ : q.Prime ∧ q ≡ 1 [MOD 2 ^ k] := Nat.sInf_mem hne
      rw [Nat.pow_succ]
      by_contra hbound
      have hxle : q ≤ 2 ^ k * 2 := by omega
      have hlower : 2 ^ k + 1 ≤ q := by
        simpa [add_comm] using hmod.symm.add_le_of_lt hprime.one_lt
      have hupper : q ≤ 2 ^ k + 1 :=
        (hmod.trans Nat.add_modEq_left.symm).le_of_lt_add (by omega)
      have hxeq : q = 2 ^ k + 1 := by omega
      have hkodd : Odd k := ⟨j + 1, by dsimp [k]; omega⟩
      have hxeqthree : q = 3 := (hprime.dvd_iff_eq (by decide)).mp (by
        rw [hxeq]
        simpa using hkodd.nat_add_dvd_pow_add_pow 2 1)
      have heighteen : 8 ≤ 2 ^ k := by
        change 2 ^ 3 ≤ 2 ^ k
        exact Nat.pow_le_pow_right (by decide) (by dsimp [k]; omega)
      omega
    omega

end Submissions.Erdos456InfinitelyManyStrict.PowerOfTwoFamily
