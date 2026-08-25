import Mathlib.NumberTheory.Divisors
import Mathlib.Tactic

namespace Submissions.Erdos18FiniteQuotientCoverage.Direct

def quotientCovered (N q : ℕ) : Prop :=
  ∃ E : Finset ℕ,
    E ⊆ N.factorial.divisors ∧
    E.card ≤ 2 ∧
    q = E.sum id

theorem factorial_split {n : ℕ} (hn : 0 < n) :
    n.factorial = n * (n - 1).factorial := by
  conv_lhs => rw [show n = (n - 1) + 1 by omega]
  rw [Nat.factorial_succ]
  congr 1
  omega

theorem divisorPairLift :
    ∀ n m q r x y : ℕ, 7 ≤ n →
      m = q * n + r →
      r < n →
      0 < x →
      0 < y →
      x ≠ y →
      q = x + y →
      x ∣ (n - 1).factorial →
      y ∣ (n - 1).factorial →
      ∃ D : Finset ℕ,
        D ⊆ n.factorial.divisors ∧
        D.card ≤ 3 ∧
        m = D.sum id := by
  intro n m q r x y hn hm hr hx hy hxy hq hxfact hyfact
  let a := x * n
  let b := y * n
  have hnpos : 0 < n := by omega
  have hadiv : a ∣ n.factorial := by
    dsimp [a]
    rw [factorial_split hnpos]
    simpa [mul_comm] using Nat.mul_dvd_mul_right hxfact n
  have hbdiv : b ∣ n.factorial := by
    dsimp [b]
    rw [factorial_split hnpos]
    simpa [mul_comm] using Nat.mul_dvd_mul_right hyfact n
  have ha_pos : 0 < a := by
    dsimp [a]
    nlinarith
  have hb_pos : 0 < b := by
    dsimp [b]
    nlinarith
  have hab : a ≠ b := by
    dsimp [a, b]
    intro heq
    apply hxy
    exact Nat.eq_of_mul_eq_mul_right hnpos heq
  have hr_lt_a : r < a := by
    dsimp [a]
    nlinarith
  have hr_lt_b : r < b := by
    dsimp [b]
    nlinarith
  have hsum : m = a + b + r := by
    rw [hm, hq]
    dsimp [a, b]
    simp [add_mul]
  by_cases hr0 : r = 0
  · refine ⟨{a, b}, ?_, by simp [hab], ?_⟩
    · intro d hd
      simp only [Finset.mem_insert, Finset.mem_singleton] at hd
      rcases hd with rfl | rfl
      · exact Nat.mem_divisors.mpr ⟨hadiv, Nat.factorial_ne_zero n⟩
      · exact Nat.mem_divisors.mpr ⟨hbdiv, Nat.factorial_ne_zero n⟩
    · simpa [hr0, hab] using hsum
  · have hrpos : 0 < r := Nat.pos_of_ne_zero hr0
    have hrdiv : r ∣ n.factorial :=
      Nat.dvd_factorial hrpos (by omega)
    have hra : r ≠ a := by omega
    have hrb : r ≠ b := by omega
    refine ⟨{a, b, r}, ?_,
      by simp [hab, Ne.symm hra, Ne.symm hrb], ?_⟩
    · intro d hd
      simp only [Finset.mem_insert, Finset.mem_singleton] at hd
      rcases hd with rfl | rfl | rfl
      · exact Nat.mem_divisors.mpr ⟨hadiv, Nat.factorial_ne_zero n⟩
      · exact Nat.mem_divisors.mpr ⟨hbdiv, Nat.factorial_ne_zero n⟩
      · exact Nat.mem_divisors.mpr ⟨hrdiv, Nat.factorial_ne_zero n⟩
    · simpa [Nat.add_assoc, hab, Ne.symm hra, Ne.symm hrb] using hsum

theorem coveredQuotientLift :
    ∀ n m q r : ℕ, 7 ≤ n →
      m = q * n + r →
      r < n →
      quotientCovered (n - 1) q →
      ∃ D : Finset ℕ,
        D ⊆ n.factorial.divisors ∧
        D.card ≤ 3 ∧
        m = D.sum id := by
  intro n m q r hn hm hr hcovered
  have hnpos : 0 < n := by omega
  obtain ⟨E, hEsub, hEcard, hEsum⟩ := hcovered
  let scaled := E.image (· * n)
  have hinj : Set.InjOn (fun d : ℕ => d * n) E := by
    intro a ha b hb hab
    exact Nat.eq_of_mul_eq_mul_right hnpos hab
  have hscaledCard : scaled.card = E.card := by
    dsimp [scaled]
    exact Finset.card_image_iff.mpr hinj
  have hscaledSub : scaled ⊆ n.factorial.divisors := by
    intro d hd
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hd
    have hediv : e ∣ (n - 1).factorial :=
      Nat.dvd_of_mem_divisors (hEsub he)
    refine Nat.mem_divisors.mpr ⟨?_, Nat.factorial_ne_zero n⟩
    rw [factorial_split hnpos]
    simpa [mul_comm] using Nat.mul_dvd_mul_right hediv n
  have hscaledSum : scaled.sum id = q * n := by
    dsimp [scaled]
    rw [Finset.sum_image (fun a _ b _ hab =>
      Nat.eq_of_mul_eq_mul_right hnpos hab)]
    simpa [Finset.sum_mul, hEsum]
  by_cases hr0 : r = 0
  · refine ⟨scaled, hscaledSub, ?_, ?_⟩
    · rw [hscaledCard]
      omega
    · rw [hscaledSum]
      omega
  · have hrpos : 0 < r := Nat.pos_of_ne_zero hr0
    have hrdiv : r ∈ n.factorial.divisors := by
      exact Nat.mem_divisors.mpr
        ⟨Nat.dvd_factorial hrpos (by omega), Nat.factorial_ne_zero n⟩
    have hdisj : Disjoint scaled {r} := by
      rw [Finset.disjoint_singleton_right]
      intro hrs
      obtain ⟨e, he, her⟩ := Finset.mem_image.mp hrs
      have hepos : 0 < e := Nat.pos_of_dvd_of_pos
        (Nat.dvd_of_mem_divisors (hEsub he)) (Nat.factorial_pos (n - 1))
      have hnle : n ≤ e * n := by nlinarith
      omega
    refine ⟨scaled ∪ {r}, ?_, ?_, ?_⟩
    · intro d hd
      rcases Finset.mem_union.mp hd with hd | hd
      · exact hscaledSub hd
      · rw [Finset.mem_singleton.mp hd]
        exact hrdiv
    · rw [Finset.card_union_of_disjoint hdisj, hscaledCard]
      simp
      omega
    · rw [Finset.sum_union hdisj, hscaledSum]
      simpa using hm

theorem finiteCoverage :
    ∀ n : ℕ, 7 ≤ n →
      (∀ q : ℕ,
        q < (n - 1) * (n - 2) * (n - 3) →
        quotientCovered (n - 1) q) →
      ∀ m : ℕ,
        m < n * (n - 1) * (n - 2) * (n - 3) →
        ∃ D : Finset ℕ,
          D ⊆ n.factorial.divisors ∧
          D.card ≤ 3 ∧
          m = D.sum id := by
  intro n hn hcover m hm
  have hnpos : 0 < n := by omega
  let q := m / n
  let r := m % n
  have hr : r < n := Nat.mod_lt m hnpos
  have hq :
      q < (n - 1) * (n - 2) * (n - 3) := by
    dsimp [q]
    rw [Nat.div_lt_iff_lt_mul hnpos]
    simpa [mul_assoc, mul_comm, mul_left_comm] using hm
  obtain ⟨E, hEsub, hEcard, hEsum⟩ := hcover q hq
  let scaled := E.image (· * n)
  have hinj : Set.InjOn (fun d : ℕ => d * n) E := by
    intro a ha b hb hab
    exact Nat.eq_of_mul_eq_mul_right hnpos hab
  have hscaledCard : scaled.card = E.card := by
    dsimp [scaled]
    exact Finset.card_image_iff.mpr hinj
  have hscaledSub : scaled ⊆ n.factorial.divisors := by
    intro d hd
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hd
    have hediv : e ∣ (n - 1).factorial :=
      Nat.dvd_of_mem_divisors (hEsub he)
    refine Nat.mem_divisors.mpr ⟨?_, Nat.factorial_ne_zero n⟩
    rw [factorial_split hnpos]
    simpa [mul_comm] using Nat.mul_dvd_mul_right hediv n
  have hscaledSum : scaled.sum id = q * n := by
    dsimp [scaled]
    rw [Finset.sum_image (fun a _ b _ hab =>
      Nat.eq_of_mul_eq_mul_right hnpos hab)]
    simpa [Finset.sum_mul, hEsum]
  have hmqr : m = q * n + r := by
    dsimp [q, r]
    simpa [mul_comm] using (Nat.div_add_mod m n).symm
  by_cases hr0 : r = 0
  · refine ⟨scaled, hscaledSub, ?_, ?_⟩
    · rw [hscaledCard]
      omega
    · rw [hscaledSum]
      omega
  · have hrpos : 0 < r := Nat.pos_of_ne_zero hr0
    have hrdiv : r ∈ n.factorial.divisors := by
      exact Nat.mem_divisors.mpr
        ⟨Nat.dvd_factorial hrpos (by omega), Nat.factorial_ne_zero n⟩
    have hdisj : Disjoint scaled {r} := by
      rw [Finset.disjoint_singleton_right]
      intro hrs
      obtain ⟨e, he, her⟩ := Finset.mem_image.mp hrs
      have hepos : 0 < e := Nat.pos_of_dvd_of_pos
        (Nat.dvd_of_mem_divisors (hEsub he)) (Nat.factorial_pos (n - 1))
      have hnle : n ≤ e * n := by nlinarith
      omega
    refine ⟨scaled ∪ {r}, ?_, ?_, ?_⟩
    · intro d hd
      rcases Finset.mem_union.mp hd with hd | hd
      · exact hscaledSub hd
      · rw [Finset.mem_singleton.mp hd]
        exact hrdiv
    · rw [Finset.card_union_of_disjoint hdisj, hscaledCard]
      simp
      omega
    · rw [Finset.sum_union hdisj, hscaledSum]
      simpa using hmqr

theorem quotient55Covered : quotientCovered 6 55 := by
  refine ⟨{40, 15}, ?_, by norm_num, by norm_num⟩
  norm_num [Finset.subset_iff, Nat.mem_divisors, Nat.factorial]

theorem gap55 (r : ℕ) (hr : r < 7) :
    ∃ D : Finset ℕ,
      D ⊆ (Nat.factorial 7).divisors ∧
      D.card ≤ 3 ∧
      55 * 7 + r = D.sum id :=
  coveredQuotientLift 7 (55 * 7 + r) 55 r
    (by norm_num) rfl hr quotient55Covered

theorem model305 :
    ∃ D : Finset ℕ,
      D ⊆ (Nat.factorial 7).divisors ∧
      D.card ≤ 3 ∧
      305 = D.sum id := by
  apply coveredQuotientLift 7 305 43 4
  · norm_num
  · norm_num
  · norm_num
  · refine ⟨{40, 3}, ?_, by norm_num, by norm_num⟩
    norm_num [Finset.subset_iff, Nat.mem_divisors, Nat.factorial]

theorem firstPairGapCarry :
    ∀ r : ℕ, r < 7 →
      ∃ D : Finset ℕ,
        D ⊆ (Nat.factorial 7).divisors ∧
        D.card ≤ 3 ∧
        59 * 7 + r = D.sum id := by
  intro r hr
  interval_cases r
  · exact ⟨{336, 70, 7}, by
      norm_num [Finset.subset_iff, Nat.mem_divisors], by norm_num, by norm_num⟩
  · exact ⟨{336, 72, 6}, by
      norm_num [Finset.subset_iff, Nat.mem_divisors], by norm_num, by norm_num⟩
  · exact ⟨{336, 72, 7}, by
      norm_num [Finset.subset_iff, Nat.mem_divisors], by norm_num, by norm_num⟩
  · exact ⟨{336, 72, 8}, by
      norm_num [Finset.subset_iff, Nat.mem_divisors], by norm_num, by norm_num⟩
  · exact ⟨{336, 80, 1}, by
      norm_num [Finset.subset_iff, Nat.mem_divisors], by norm_num, by norm_num⟩
  · exact ⟨{336, 80, 2}, by
      norm_num [Finset.subset_iff, Nat.mem_divisors], by norm_num, by norm_num⟩
  · exact ⟨{336, 80, 3}, by
      norm_num [Finset.subset_iff, Nat.mem_divisors], by norm_num, by norm_num⟩

theorem proof :
    (∀ n m q r x y : ℕ, 7 ≤ n →
      m = q * n + r →
      r < n →
      0 < x →
      0 < y →
      x ≠ y →
      q = x + y →
      x ∣ (n - 1).factorial →
      y ∣ (n - 1).factorial →
      ∃ D : Finset ℕ,
        D ⊆ n.factorial.divisors ∧
        D.card ≤ 3 ∧
        m = D.sum id) ∧
    (∀ n m q r : ℕ, 7 ≤ n →
      m = q * n + r →
      r < n →
      quotientCovered (n - 1) q →
      ∃ D : Finset ℕ,
        D ⊆ n.factorial.divisors ∧
        D.card ≤ 3 ∧
        m = D.sum id) ∧
    (∀ n : ℕ, 7 ≤ n →
      (∀ q : ℕ,
        q < (n - 1) * (n - 2) * (n - 3) →
        quotientCovered (n - 1) q) →
      ∀ m : ℕ,
        m < n * (n - 1) * (n - 2) * (n - 3) →
        ∃ D : Finset ℕ,
          D ⊆ n.factorial.divisors ∧
          D.card ≤ 3 ∧
          m = D.sum id) ∧
    (∀ r : ℕ, r < 7 →
      ∃ D : Finset ℕ,
        D ⊆ (Nat.factorial 7).divisors ∧
        D.card ≤ 3 ∧
        59 * 7 + r = D.sum id) :=
  ⟨divisorPairLift, coveredQuotientLift, finiteCoverage, firstPairGapCarry⟩

end Submissions.Erdos18FiniteQuotientCoverage.Direct
