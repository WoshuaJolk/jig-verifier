import Mathlib.Data.Nat.Prime.Infinite
import Mathlib.Data.Nat.Prime.Pow
import Mathlib.Tactic

namespace Submissions.Erdos463ArbitrarilyLargeWindows.PrimeSquares

theorem proof :
    ∀ B : ℕ, ∃ n m : ℕ,
      (1 < m ∧ ¬m.Prime) ∧
      n + B < m ∧ m < n + m.minFac := by
  intro B
  obtain ⟨p, hp_bound, hp⟩ := Nat.exists_infinite_primes (B + 2)
  let d := B + 1
  let m := p ^ 2
  let n := m - d
  have hd_lt_p : d < p := by
    dsimp [d]
    omega
  have hp_le_m : p ≤ m := by
    dsimp [m]
    nlinarith [hp.two_le]
  have hd_le_m : d ≤ m :=
    (Nat.le_of_lt hd_lt_p).trans hp_le_m
  have hn_add : n + d = m :=
    Nat.sub_add_cancel hd_le_m
  refine ⟨n, m, ?_, ?_, ?_⟩
  · constructor
    · exact hp.one_lt.trans_le hp_le_m
    · dsimp [m]
      exact Nat.Prime.not_prime_pow (by norm_num)
  · dsimp [d] at hn_add
    omega
  · have hmin : m.minFac = p := by
      dsimp [m]
      exact hp.pow_minFac (by norm_num)
    rw [hmin]
    omega

end Submissions.Erdos463ArbitrarilyLargeWindows.PrimeSquares
