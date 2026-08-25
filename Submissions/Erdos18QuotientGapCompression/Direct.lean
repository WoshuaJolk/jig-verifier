import Mathlib.NumberTheory.Divisors
import Mathlib.Tactic

namespace Submissions.Erdos18QuotientGapCompression.Direct

theorem factorial_split {n : ℕ} (hn : 0 < n) :
    n.factorial = n * (n - 1).factorial := by
  conv_lhs => rw [show n = (n - 1) + 1 by omega]
  rw [Nat.factorial_succ]
  congr 1
  omega

theorem proof :
    ∀ n m q r x : ℕ, 7 ≤ n →
      m = q * n + r →
      r < n →
      n ≤ x →
      x ≤ q →
      q < x + n →
      x ∣ (n - 1).factorial →
      ∃ D : Finset ℕ,
        D ⊆ n.factorial.divisors ∧
        D.card ≤ 3 ∧
        m = D.sum id := by
  intro n m q r x hn hm hr hnx hxq hqx hxfact
  let t := q - x
  let a := x * n
  let b := t * n
  have hnpos : 0 < n := by omega
  have htlt : t < n := by
    dsimp [t]
    omega
  have hq : q = x + t := by
    dsimp [t]
    omega
  have hafact : a ∣ n.factorial := by
    dsimp [a]
    rw [factorial_split hnpos]
    simpa [mul_comm] using Nat.mul_dvd_mul_right hxfact n
  have ha_pos : 0 < a := by
    dsimp [a]
    nlinarith
  have hb_lt : b < a := by
    dsimp [a, b]
    nlinarith
  have hr_lt_a : r < a := by
    have : n ≤ a := by
      dsimp [a]
      nlinarith
    omega
  have hbpos_dvd (hbpos : 0 < b) : b ∣ n.factorial := by
    have htpos : 0 < t := by
      dsimp [b] at hbpos
      nlinarith
    have htle : t ≤ n - 1 := by omega
    have htfact : t ∣ (n - 1).factorial :=
      Nat.dvd_factorial htpos htle
    dsimp [b]
    rw [factorial_split hnpos]
    simpa [mul_comm] using Nat.mul_dvd_mul_right htfact n
  have hrpos_dvd (hrpos : 0 < r) : r ∣ n.factorial :=
    Nat.dvd_factorial hrpos (by omega)
  have hsum : m = a + b + r := by
    rw [hm, hq]
    dsimp [a, b]
    simp [add_mul]
  by_cases hb0 : b = 0
  · by_cases hr0 : r = 0
    · refine ⟨{a}, ?_, by simp, ?_⟩
      · intro d hd
        rw [Finset.mem_singleton.mp hd]
        exact Nat.mem_divisors.mpr ⟨hafact, Nat.factorial_ne_zero n⟩
      · simp [hsum, hb0, hr0]
    · have hrpos : 0 < r := Nat.pos_of_ne_zero hr0
      have hara : r ≠ a := by omega
      refine ⟨{a, r}, ?_, by simp [Ne.symm hara], ?_⟩
      · intro d hd
        simp only [Finset.mem_insert, Finset.mem_singleton] at hd
        rcases hd with rfl | rfl
        · exact Nat.mem_divisors.mpr ⟨hafact, Nat.factorial_ne_zero n⟩
        · exact Nat.mem_divisors.mpr ⟨hrpos_dvd hrpos, Nat.factorial_ne_zero n⟩
      · simpa [hb0, Ne.symm hara] using hsum
  · have hbpos : 0 < b := Nat.pos_of_ne_zero hb0
    have hab : b ≠ a := by omega
    by_cases hr0 : r = 0
    · refine ⟨{a, b}, ?_, by simp [Ne.symm hab], ?_⟩
      · intro d hd
        simp only [Finset.mem_insert, Finset.mem_singleton] at hd
        rcases hd with rfl | rfl
        · exact Nat.mem_divisors.mpr ⟨hafact, Nat.factorial_ne_zero n⟩
        · exact Nat.mem_divisors.mpr ⟨hbpos_dvd hbpos, Nat.factorial_ne_zero n⟩
      · simpa [hr0, Ne.symm hab] using hsum
    · have hrpos : 0 < r := Nat.pos_of_ne_zero hr0
      have har : r ≠ a := by omega
      have hbr : r ≠ b := by
        have htpos : 0 < t := by
          dsimp [b] at hbpos
          nlinarith
        have : n ≤ t * n := by nlinarith
        dsimp [b]
        omega
      refine ⟨{a, b, r}, ?_,
        by simp [Ne.symm hab, Ne.symm har, Ne.symm hbr], ?_⟩
      · intro d hd
        simp only [Finset.mem_insert, Finset.mem_singleton] at hd
        rcases hd with rfl | rfl | rfl
        · exact Nat.mem_divisors.mpr ⟨hafact, Nat.factorial_ne_zero n⟩
        · exact Nat.mem_divisors.mpr ⟨hbpos_dvd hbpos, Nat.factorial_ne_zero n⟩
        · exact Nat.mem_divisors.mpr ⟨hrpos_dvd hrpos, Nat.factorial_ne_zero n⟩
      · simpa [Nat.add_assoc, Ne.symm hab, Ne.symm har, Ne.symm hbr] using hsum

end Submissions.Erdos18QuotientGapCompression.Direct
