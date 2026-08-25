import Mathlib.Data.Nat.PrimeFin
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Tactic

namespace Submissions.Erdos479ResidueFour.Direct

lemma twice_odd_prime_works {p : ℕ} (hp : p.Prime) (hpodd : Odd p) :
    2 ^ (2 * p) ≡ 4 [MOD 2 * p] := by
  have hcop : Nat.Coprime 2 p := Nat.coprime_two_left.mpr hpodd
  have hfermat : 2 ^ (p - 1) ≡ 1 [MOD p] := by
    simpa [Nat.totient_prime hp] using Nat.ModEq.pow_totient hcop
  have hpmod : 2 ^ (2 * p) ≡ 4 [MOD p] := by
    calc
      2 ^ (2 * p) =
          4 * (2 ^ (p - 1)) ^ 2 := by
            have hp1 := hp.one_le
            rw [show 2 * p = 2 + (p - 1) * 2 by omega, pow_add, pow_mul]
            norm_num
      _ ≡ 4 * 1 ^ 2 [MOD p] := (hfermat.pow 2).mul_left 4
      _ = 4 := by norm_num
  have htwo : 2 ^ (2 * p) ≡ 4 [MOD 2] := by
    simp [Nat.ModEq, hp.pos]
  exact (Nat.modEq_and_modEq_iff_modEq_mul hcop).mp ⟨htwo, hpmod⟩

/-- Route 2: `k=4` has the infinite family `n=2p` over odd primes. -/
theorem proof :
    {n : ℕ | 2 ^ n ≡ 4 [MOD n]}.Infinite := by
  let P : Set ℕ := {p : ℕ | p.Prime} \ {2}
  have hP : P.Infinite :=
    Nat.infinite_setOfPred_prime.sdiff (Set.finite_singleton 2)
  have hinj : Set.InjOn (fun p : ℕ => 2 * p) P := by
    intro p _ q _ hpq
    exact Nat.mul_left_cancel (by omega) hpq
  have himage : ((fun p : ℕ => 2 * p) '' P).Infinite := hP.image hinj
  refine himage.mono ?_
  rintro n ⟨p, ⟨hp, hpne⟩, rfl⟩
  exact twice_odd_prime_works hp (hp.odd_of_ne_two (by simpa using hpne))

end Submissions.Erdos479ResidueFour.Direct
