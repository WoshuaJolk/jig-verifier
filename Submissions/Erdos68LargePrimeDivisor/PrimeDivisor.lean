import Mathlib.Data.Nat.Prime.Factorial
import Mathlib.Tactic

namespace Submissions.Erdos68LargePrimeDivisor.PrimeDivisor

/-- Every denominator `n! - 1` occurring from `n = 3` onward has a prime
divisor larger than its factorial index. -/
theorem proof :
    ∀ n : ℕ, 3 ≤ n →
      ∃ p : ℕ, p.Prime ∧ n < p ∧ p ∣ n.factorial - 1 := by
  intro n hn
  have hfac : 6 ≤ n.factorial := by
    have hmono := Nat.factorial_le hn
    norm_num at hmono ⊢
    exact hmono
  have hne : n.factorial - 1 ≠ 1 := by omega
  obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hne
  refine ⟨p, hp, ?_, hpd⟩
  by_contra h
  have hple : p ≤ n := Nat.not_lt.mp h
  have hpf : p ∣ n.factorial := hp.dvd_factorial.mpr hple
  have hpone : p ∣ 1 := by
    have hd := Nat.dvd_sub hpf hpd
    rwa [Nat.sub_sub_self (by omega : 1 ≤ n.factorial)] at hd
  exact hp.not_dvd_one hpone

end Submissions.Erdos68LargePrimeDivisor.PrimeDivisor
