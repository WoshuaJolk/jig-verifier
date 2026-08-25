import Mathlib.NumberTheory.Divisors
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Tactic

namespace Submissions.Erdos18FactorialLinearBound.Induction

open Filter

def subsetSums (A : Set ℕ) : Set ℕ :=
  {n | ∃ B : Finset ℕ, ↑B ⊆ A ∧ n = ∑ i ∈ B, i}

noncomputable def practicalH (n : ℕ) : ℕ :=
  Finset.sup (Finset.Icc 1 n) fun m =>
    sInf {k | ∃ D : Finset ℕ, D ⊆ n.divisors ∧ D.card = k ∧ m ∈ subsetSums D}

theorem bounded_representation :
    ∀ k m : ℕ, m ≤ (k + 2).factorial →
      ∃ B : Finset ℕ,
        B ⊆ (k + 2).factorial.divisors ∧
        B.card ≤ k + 1 ∧
        m = B.sum id := by
  intro k
  induction k with
  | zero =>
      intro m hm
      norm_num at hm ⊢
      interval_cases m
      · exact ⟨∅, by simp, by simp, by simp⟩
      · exact ⟨{1}, by norm_num, by simp, by simp⟩
      · exact ⟨{2}, by norm_num, by simp, by simp⟩
  | succ k ih =>
      intro m hm
      let n := k + 2
      have hn : n + 1 = k + 3 := by omega
      have hfactorial : (k + 3).factorial = (n + 1) * n.factorial := by
        rw [← hn, Nat.factorial_succ]
      by_cases hle : m ≤ n.factorial
      · obtain ⟨B, hBsub, hBcard, hBsum⟩ := ih m (by simpa [n] using hle)
        refine ⟨B, ?_, by omega, hBsum⟩
        exact hBsub.trans (by
          exact_mod_cast Nat.divisors_subset_of_dvd
            (Nat.factorial_ne_zero _)
            (Nat.factorial_dvd_factorial (by omega : n ≤ k + 3)))
      · push Not at hle
        rw [hfactorial] at hm
        let q := m / (n + 1)
        let r := m % (n + 1)
        have hdiv : m = (n + 1) * q + r := (Nat.div_add_mod m (n + 1)).symm
        have hrlt : r < n + 1 := Nat.mod_lt m (by omega)
        have hq : q ≤ n.factorial := Nat.div_le_of_le_mul hm
        obtain ⟨B, hBsub, hBcard, hBsum⟩ := ih q (by simpa [n] using hq)
        let B' := B.image (· * (n + 1))
        have hinj : Set.InjOn (fun d : ℕ => d * (n + 1)) B := by
          intro a ha b hb hab
          exact Nat.eq_of_mul_eq_mul_right (by omega) hab
        have hB'card : B'.card = B.card := by
          simp [B', Finset.card_image_iff.mpr hinj]
        have hB'sub : B' ⊆ (k + 3).factorial.divisors := by
          intro x hx
          obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hx
          refine Nat.mem_divisors.mpr ⟨?_, Nat.factorial_ne_zero _⟩
          rw [hfactorial, mul_comm]
          exact mul_dvd_mul_left (n + 1)
            (Nat.dvd_of_mem_divisors (hBsub hd))
        have hB'sum : B'.sum id = (n + 1) * q := by
          rw [show B' = B.image (· * (n + 1)) from rfl]
          rw [Finset.sum_image (fun a _ b _ hab =>
            Nat.eq_of_mul_eq_mul_right (by omega) hab)]
          simpa [Finset.mul_sum, mul_comm] using congrArg (fun x => (n + 1) * x) hBsum.symm
        by_cases hr : r = 0
        · refine ⟨B', hB'sub, ?_, ?_⟩
          · rw [hB'card]
            omega
          · omega
        · have hrpos : 0 < r := Nat.pos_of_ne_zero hr
          have hrdiv : r ∈ (k + 3).factorial.divisors := by
            refine Nat.mem_divisors.mpr ⟨?_, Nat.factorial_ne_zero _⟩
            exact (Nat.dvd_factorial (by omega) (by omega)).trans
              (Nat.factorial_dvd_factorial (by omega : n ≤ k + 3))
          have hdisj : Disjoint B' {r} := by
            rw [Finset.disjoint_singleton_right]
            intro hrB
            obtain ⟨d, hd, hdr⟩ := Finset.mem_image.mp hrB
            have hdpos : 0 < d := Nat.pos_of_dvd_of_pos
              (Nat.dvd_of_mem_divisors (hBsub hd)) (Nat.factorial_pos n)
            have hlarge : n + 1 ≤ d * (n + 1) := by nlinarith
            omega
          refine ⟨B' ∪ {r}, ?_, ?_, ?_⟩
          · intro x hx
            rcases Finset.mem_union.mp hx with hx | hx
            · exact hB'sub hx
            · rw [Finset.mem_singleton.mp hx]
              simpa [Nat.add_assoc] using hrdiv
          · rw [Finset.card_union_of_disjoint hdisj, hB'card]
            simp
            omega
          · rw [Finset.sum_union hdisj, hB'sum]
            simp [hdiv]

theorem proof :
    ∀ᶠ n : ℕ in atTop, practicalH n.factorial < n := by
  filter_upwards [eventually_ge_atTop 2] with n hn
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  have hbound : practicalH (2 + k).factorial ≤ k + 1 := by
    simp only [practicalH, Finset.sup_le_iff, Finset.mem_Icc]
    intro m hm
    obtain ⟨B, hBsub, hBcard, hBsum⟩ :=
      bounded_representation k m (by simpa [Nat.add_comm] using hm.2)
    apply hBcard.trans'
    exact Nat.sInf_le ⟨B, by simpa [Nat.add_comm] using hBsub,
      rfl, B, rfl.subset, hBsum⟩
  omega

end Submissions.Erdos18FactorialLinearBound.Induction
