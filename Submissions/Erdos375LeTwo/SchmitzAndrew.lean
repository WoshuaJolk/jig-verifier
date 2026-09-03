import Mathlib

namespace Submissions.Erdos375LeTwo.SchmitzAndrew

/-- Grimm's conjecture for block length at most 2. Block length 0 is vacuous;
length 1 needs a single prime factor; length 2 needs two distinct prime factors,
which exist because a common prime factor of `n+1` and `n+2` would divide their
difference `1`. -/
theorem proof : ∀ n : ℕ, 1 ≤ n → ∀ k : ℕ, k ≤ 2 →
    (∀ i < k, ¬ (n + i + 1).Prime) →
      ∃ p : Fin k → ℕ, Function.Injective p ∧
        ∀ i, (p i).Prime ∧ p i ∣ n + i + 1 := by
  intro n hn k hk _
  interval_cases k
  · exact ⟨Fin.elim0, fun a => a.elim0, fun i => i.elim0⟩
  · obtain ⟨p, hp, hd⟩ := Nat.exists_prime_and_dvd (n := n + 1) (by omega)
    refine ⟨fun _ => p, Function.injective_of_subsingleton _, fun i => ?_⟩
    fin_cases i
    exact ⟨hp, by simpa using hd⟩
  · obtain ⟨p0, hp0, hd0⟩ := Nat.exists_prime_and_dvd (n := n + 1) (by omega)
    obtain ⟨p1, hp1, hd1⟩ := Nat.exists_prime_and_dvd (n := n + 2) (by omega)
    have hne : p0 ≠ p1 := by
      intro heq
      rw [← heq] at hd1
      have hsub : p0 ∣ (n + 2) - (n + 1) := Nat.dvd_sub hd1 hd0
      have hone : (n + 2) - (n + 1) = 1 := by omega
      rw [hone] at hsub
      exact hp0.one_lt.ne' (Nat.dvd_one.mp hsub)
    refine ⟨![p0, p1], ?_, fun i => ?_⟩
    · intro x y hxy
      fin_cases x <;> fin_cases y <;> simp_all
    · fin_cases i
      · exact ⟨hp0, by simpa using hd0⟩
      · exact ⟨hp1, by simpa using hd1⟩

end Submissions.Erdos375LeTwo.SchmitzAndrew
