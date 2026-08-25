import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.NumberTheory.Divisors
import Mathlib.Tactic

namespace Submissions.Erdos18GridValuationCriterion.Direct

theorem factorial_split {n : ℕ} (hn : 0 < n) :
    n.factorial = n * (n - 1).factorial := by
  conv_lhs => rw [show n = (n - 1) + 1 by omega]
  rw [Nat.factorial_succ]
  congr 1
  omega

theorem two_distinct_factors_dvd_factorial {u w k : ℕ}
    (hu : 0 < u) (hw : 0 < w) (huk : u ≤ k) (hwk : w ≤ k)
    (huw : u ≠ w) :
    u * w ∣ k.factorial := by
  rcases lt_or_gt_of_ne huw with huwlt | hwult
  · have hudiv : u ∣ (w - 1).factorial :=
      Nat.dvd_factorial hu (by omega)
    have hprod : u * w ∣ w.factorial := by
      rw [factorial_split hw]
      simpa [mul_comm] using Nat.mul_dvd_mul_right hudiv w
    exact hprod.trans (Nat.factorial_dvd_factorial hwk)
  · have hwdiv : w ∣ (u - 1).factorial :=
      Nat.dvd_factorial hw (by omega)
    have hprod : w * u ∣ u.factorial := by
      rw [factorial_split hu]
      simpa [mul_comm] using Nat.mul_dvd_mul_right hwdiv u
    simpa [mul_comm] using hprod.trans (Nat.factorial_dvd_factorial huk)

theorem gridCriterion :
    ∀ k a b c u d v : ℕ,
      6 ≤ k →
      a < k - 2 →
      b < k - 1 →
      c < k →
      0 < u →
      0 < d →
      d < k →
      0 < v →
      u * d = k - c →
      u + v = a * (k - 1) + b + 1 →
      u ≠ k - d →
      k * v ≠ u * (k - d) →
      (∀ p : ℕ, p.Prime →
        v.factorization p ≤ (k - 1).factorial.factorization p) →
      ∃ E : Finset ℕ,
        E ⊆ k.factorial.divisors ∧
        E.card = 2 ∧
        a * k * (k - 1) + b * k + c = E.sum id := by
  intro k a b c u d v hk ha hb hc hu hd hdlt hv hud huv huy hxy hval
  have hkpos : 0 < k := by omega
  have hdle : d ≤ k := hdlt.le
  have hwpos : 0 < k - d := by
    exact Nat.sub_pos_of_lt hdlt
  have hule : u ≤ k := by
    have huprod : u ≤ u * d := Nat.le_mul_of_pos_right u hd
    rw [hud] at huprod
    exact huprod.trans (Nat.sub_le k c)
  have hwle : k - d ≤ k := Nat.sub_le _ _
  have hvdvd : v ∣ (k - 1).factorial := by
    apply (Nat.factorization_prime_le_iff_dvd hv.ne'
      (Nat.factorial_ne_zero (k - 1))).mp
    exact hval
  have hxdiv : k * v ∣ k.factorial := by
    rw [factorial_split hkpos]
    simpa using Nat.mul_dvd_mul_left k hvdvd
  have hydiv : u * (k - d) ∣ k.factorial :=
    two_distinct_factors_dvd_factorial hu hwpos hule hwle huy
  have hkd : k - d + d = k := Nat.sub_add_cancel hdle
  have hsum :
      a * k * (k - 1) + b * k + c =
        k * v + u * (k - d) := by
    apply Nat.add_right_cancel (m := u * d)
    calc
      a * k * (k - 1) + b * k + c + u * d =
          a * k * (k - 1) + b * k + k := by
            rw [hud]
            omega
      _ = k * (u + v) := by
            rw [huv]
            ring
      _ = k * v + u * (k - d) + u * d := by
            symm
            calc
              k * v + u * (k - d) + u * d =
                  k * v + u * ((k - d) + d) := by ring
              _ = k * v + u * k := by rw [hkd]
              _ = k * (u + v) := by ring
  refine ⟨{k * v, u * (k - d)}, ?_, by simp [hxy], ?_⟩
  · intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl
    · exact Nat.mem_divisors.mpr ⟨hxdiv, Nat.factorial_ne_zero k⟩
    · exact Nat.mem_divisors.mpr ⟨hydiv, Nat.factorial_ne_zero k⟩
  · simpa [hxy] using hsum

theorem twentyNineGridObstruction :
    ¬(649 ∣ Nat.factorial 27) ∧
      ¬(647 ∣ Nat.factorial 27) ∧
      ¬(641 ∣ Nat.factorial 27) := by
  norm_num [Nat.factorial]

theorem twentyNineAllGridChoicesFail :
    ∀ u d v : ℕ, 0 < u → 0 < d →
      u * d = 9 →
      u + v = 650 →
      ¬(v ∣ Nat.factorial 27) := by
  intro u d v hu hd hud huv
  have hu9 : u ≤ 9 := by
    have : u ≤ u * d := Nat.le_mul_of_pos_right u hd
    omega
  interval_cases u <;> norm_num at hud
  all_goals
    have hv : v = 649 ∨ v = 647 ∨ v = 641 := by omega
    rcases hv with rfl | rfl | rfl <;> norm_num [Nat.factorial]

theorem proof :
    (∀ k a b c u d v : ℕ,
      6 ≤ k →
      a < k - 2 →
      b < k - 1 →
      c < k →
      0 < u →
      0 < d →
      d < k →
      0 < v →
      u * d = k - c →
      u + v = a * (k - 1) + b + 1 →
      u ≠ k - d →
      k * v ≠ u * (k - d) →
      (∀ p : ℕ, p.Prime →
        v.factorization p ≤ (k - 1).factorial.factorization p) →
      ∃ E : Finset ℕ,
        E ⊆ k.factorial.divisors ∧
        E.card = 2 ∧
        a * k * (k - 1) + b * k + c = E.sum id) ∧
    (∀ u d v : ℕ, 0 < u → 0 < d →
      u * d = 9 →
      u + v = 650 →
      ¬(v ∣ Nat.factorial 27)) :=
  ⟨gridCriterion, twentyNineAllGridChoicesFail⟩

end Submissions.Erdos18GridValuationCriterion.Direct
