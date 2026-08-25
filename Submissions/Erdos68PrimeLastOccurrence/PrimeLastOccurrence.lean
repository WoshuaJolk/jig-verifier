import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Finset.Interval
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic

namespace Submissions.Erdos68PrimeLastOccurrence.PrimeLastOccurrence

private lemma occurrence_lt_prime {p n : ℕ} (hp : p.Prime)
    (hn : 2 ≤ n) (hdiv : p ∣ n.factorial - 1) :
    n < p := by
  by_contra hnp
  have hpn : p ≤ n := by omega
  have hfac : p ∣ n.factorial :=
    Nat.dvd_factorial hp.pos hpn
  have hone : p ∣ 1 := by
    have hsub := Nat.dvd_sub hfac hdiv
    have hfacLarge : 1 ≤ n.factorial := by
      have := Nat.factorial_pos n
      omega
    simpa [Nat.sub_sub_self hfacLarge] using hsub
  exact hp.not_dvd_one hone

/-- Every occurrence of a prime in the sequence `n! - 1` lies below the prime.
Consequently, from any occurrence one can choose a final occurrence `K < p`,
after which that prime divides no denominator at all. -/
theorem proof :
    ∀ p : ℕ, p.Prime → ∀ n : ℕ, 2 ≤ n →
      p ∣ n.factorial - 1 →
      ∃ K : ℕ,
        n ≤ K ∧ K < p ∧ p ∣ K.factorial - 1 ∧
          ∀ m : ℕ, K < m → ¬p ∣ m.factorial - 1 := by
  intro p hp n hn hdiv
  have hnp : n < p := occurrence_lt_prime hp hn hdiv
  let A : Finset ℕ :=
    (Finset.Icc 2 (p - 1)).filter
      (fun k => p ∣ k.factorial - 1)
  have hnmem : n ∈ A := by
    simp only [A, Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨hn, by omega⟩, hdiv⟩
  have hA : A.Nonempty := ⟨n, hnmem⟩
  let K : ℕ := A.max' hA
  have hKmem : K ∈ A := Finset.max'_mem A hA
  have hKdata :
      2 ≤ K ∧ K ≤ p - 1 ∧ p ∣ K.factorial - 1 := by
    have h :=
      (show (2 ≤ K ∧ K ≤ p - 1) ∧ p ∣ K.factorial - 1 by
        simpa only [A, Finset.mem_filter, Finset.mem_Icc] using hKmem)
    exact ⟨h.1.1, h.1.2, h.2⟩
  have hnK : n ≤ K := Finset.le_max' A n hnmem
  refine ⟨K, hnK, by omega, hKdata.2.2, ?_⟩
  intro m hKm hmdiv
  have hm2 : 2 ≤ m := by omega
  have hmp : m < p := occurrence_lt_prime hp hm2 hmdiv
  have hmmem : m ∈ A := by
    simp only [A, Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨hm2, by omega⟩, hmdiv⟩
  have hmK : m ≤ K := Finset.le_max' A m hmmem
  omega

end Submissions.Erdos68PrimeLastOccurrence.PrimeLastOccurrence
