import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.NumberTheory.Divisors
import Mathlib.Tactic

namespace Submissions.Erdos18GridFailureRescue.Direct

def valuationBound (N t : ℕ) : Prop :=
  ∀ p : ℕ, p.Prime →
    t.factorization p ≤ N.factorial.factorization p

def threeRep (N m : ℕ) : Prop :=
  ∃ D : Finset ℕ,
    D ⊆ N.factorial.divisors ∧
    D.card ≤ 3 ∧
    m = D.sum id

theorem factorial_split {n : ℕ} (hn : 0 < n) :
    n.factorial = n * (n - 1).factorial := by
  conv_lhs => rw [show n = (n - 1) + 1 by omega]
  rw [Nat.factorial_succ]
  congr 1
  omega

theorem dvd_factorial_of_valuationBound {N t : ℕ}
    (ht : 0 < t) (h : valuationBound N t) :
    t ∣ N.factorial := by
  apply (Nat.factorization_prime_le_iff_dvd ht.ne'
    (Nat.factorial_ne_zero N)).mp
  exact h

theorem proof :
    (∀ k q v y w z r : ℕ,
      6 ≤ k →
      q = k * v + y →
      q + v = w + 1 →
      y + r = z + 1 →
      0 < v →
      0 < y →
      0 < w →
      0 < z →
      r < k + 1 →
      y ∣ k.factorial →
      ((valuationBound (k - 1) v ∧ k * v ≠ y) ∨
        (valuationBound (k - 1) w ∧
          valuationBound (k + 1) z ∧
          k + 1 ≠ k * w ∧
          k + 1 ≠ z ∧
          k * w ≠ z)) →
      threeRep (k + 1) ((k + 1) * q + r)) ∧
    (18837 ∣ Nat.factorial 27 ∧
      28 * 18837 = 527436 ∧
      ∀ r : ℕ, r < 29 → 74 + r ∣ Nat.factorial 29 →
        let D : Finset ℕ := {29, 527436, 74 + r}
        D ⊆ (Nat.factorial 29).divisors ∧
          D.card = 3 ∧
          18191 * 29 + r = D.sum id) := by
  constructor
  · intro k q v y w z r hk hq hw hz hv hy hwpos hzpos hr hydiv hcases
    have hkpos : 0 < k := by omega
    rcases hcases with hgrid | hrescue
    · obtain ⟨hvbound, hxy⟩ := hgrid
      have hvdiv : v ∣ (k - 1).factorial :=
        dvd_factorial_of_valuationBound hv hvbound
      have hxdiv : k * v ∣ k.factorial := by
        rw [factorial_split hkpos]
        simpa using Nat.mul_dvd_mul_left k hvdiv
      let sx := (k + 1) * (k * v)
      let sy := (k + 1) * y
      have hsxdiv : sx ∣ (k + 1).factorial := by
        dsimp [sx]
        rw [Nat.factorial_succ]
        exact Nat.mul_dvd_mul_left (k + 1) hxdiv
      have hsydiv : sy ∣ (k + 1).factorial := by
        dsimp [sy]
        rw [Nat.factorial_succ]
        exact Nat.mul_dvd_mul_left (k + 1) hydiv
      have hsxy : sx ≠ sy := by
        dsimp [sx, sy]
        intro heq
        apply hxy
        exact Nat.eq_of_mul_eq_mul_left (by omega) heq
      have hkvpos : 0 < k * v := Nat.mul_pos hkpos hv
      have hsx_large : k + 1 ≤ sx := by
        dsimp [sx]
        exact Nat.le_mul_of_pos_right (k + 1) hkvpos
      have hsy_large : k + 1 ≤ sy := by
        dsimp [sy]
        exact Nat.le_mul_of_pos_right (k + 1) hy
      have hsum : (k + 1) * q + r = sx + sy + r := by
        rw [hq]
        dsimp [sx, sy]
        ring
      by_cases hr0 : r = 0
      · refine ⟨{sx, sy}, ?_, by simp [hsxy], ?_⟩
        · intro d hd
          simp only [Finset.mem_insert, Finset.mem_singleton] at hd
          rcases hd with rfl | rfl
          · exact Nat.mem_divisors.mpr
              ⟨hsxdiv, Nat.factorial_ne_zero (k + 1)⟩
          · exact Nat.mem_divisors.mpr
              ⟨hsydiv, Nat.factorial_ne_zero (k + 1)⟩
        · simpa [hr0, hsxy] using hsum
      · have hrpos : 0 < r := Nat.pos_of_ne_zero hr0
        have hrdiv : r ∣ (k + 1).factorial :=
          Nat.dvd_factorial hrpos hr.le
        have hrsx : r ≠ sx := by omega
        have hrsy : r ≠ sy := by omega
        refine ⟨{sx, sy, r}, ?_,
          by simp [hsxy, Ne.symm hrsx, Ne.symm hrsy], ?_⟩
        · intro d hd
          simp only [Finset.mem_insert, Finset.mem_singleton] at hd
          rcases hd with rfl | rfl | rfl
          · exact Nat.mem_divisors.mpr
              ⟨hsxdiv, Nat.factorial_ne_zero (k + 1)⟩
          · exact Nat.mem_divisors.mpr
              ⟨hsydiv, Nat.factorial_ne_zero (k + 1)⟩
          · exact Nat.mem_divisors.mpr
              ⟨hrdiv, Nat.factorial_ne_zero (k + 1)⟩
        · simpa [Nat.add_assoc, hsxy, Ne.symm hrsx, Ne.symm hrsy] using hsum
    · obtain ⟨hwbound, hzbound, hnkw, hnz, hkwz⟩ := hrescue
      have hwdiv : w ∣ (k - 1).factorial :=
        dvd_factorial_of_valuationBound hwpos hwbound
      have hkwdiv : k * w ∣ k.factorial := by
        rw [factorial_split hkpos]
        simpa using Nat.mul_dvd_mul_left k hwdiv
      have hkwdiv' : k * w ∣ (k + 1).factorial :=
        hkwdiv.trans (Nat.factorial_dvd_factorial (by omega))
      have hzdiv : z ∣ (k + 1).factorial :=
        dvd_factorial_of_valuationBound hzpos hzbound
      have hndiv : k + 1 ∣ (k + 1).factorial :=
        Nat.dvd_factorial (by omega) (by omega)
      have hsum :
          (k + 1) * q + r = (k + 1) + k * w + z := by
        have hqmul := congrArg (fun t : ℕ => (k + 1) * t) hq
        have hwmul := congrArg (fun t : ℕ => k * t) hw
        nlinarith
      refine ⟨{k + 1, k * w, z}, ?_,
        by simp [hnkw, hnz, hkwz], ?_⟩
      · intro d hd
        simp only [Finset.mem_insert, Finset.mem_singleton] at hd
        rcases hd with rfl | rfl | rfl
        · exact Nat.mem_divisors.mpr
            ⟨hndiv, Nat.factorial_ne_zero (k + 1)⟩
        · exact Nat.mem_divisors.mpr
            ⟨hkwdiv', Nat.factorial_ne_zero (k + 1)⟩
        · exact Nat.mem_divisors.mpr
            ⟨hzdiv, Nat.factorial_ne_zero (k + 1)⟩
      · simpa [Nat.add_assoc, hnkw, hnz, hkwz] using hsum
  · constructor
    · norm_num [Nat.factorial]
    constructor
    · norm_num
    · intro r hr hrdiv
      have h₁ : 29 ≠ 527436 := by norm_num
      have h₂ : 29 ≠ 74 + r := by omega
      have h₃ : 527436 ≠ 74 + r := by omega
      refine ⟨?_, by simp [h₁, h₂, h₃], ?_⟩
      · intro d hd
        simp only [Finset.mem_insert, Finset.mem_singleton] at hd
        rcases hd with rfl | rfl | rfl
        · norm_num [Nat.mem_divisors]
        · norm_num [Nat.mem_divisors, Nat.factorial]
        · exact Nat.mem_divisors.mpr
            ⟨hrdiv, Nat.factorial_ne_zero 29⟩
      · simp [h₁, h₂, h₃]
        omega

end Submissions.Erdos18GridFailureRescue.Direct
