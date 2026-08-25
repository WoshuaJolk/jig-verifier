import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Tactic

open Filter
open scoped BigOperators

namespace Submissions.Erdos935LengthOneUpper.Direct

noncomputable def powerfulPart (n : ℕ) : ℕ :=
  n.factorization.prod fun p e => if 2 ≤ e then p ^ e else 1

def consecutiveProduct (n ℓ : ℕ) : ℕ :=
  ∏ i ∈ Finset.range (ℓ + 1), (n + i)

lemma powerfulPart_le (n : ℕ) (hn : n ≠ 0) :
    powerfulPart n ≤ n := by
  conv_rhs => rw [← Nat.prod_factorization_pow_eq_self hn]
  unfold powerfulPart Finsupp.prod
  apply Finset.prod_le_prod
  · simp
  · intro p hp
    by_cases h : 2 ≤ n.factorization p
    · dsimp
      rw [if_pos h]
    · dsimp
      rw [if_neg h]
      have hp' := Nat.Prime.pos (Nat.prime_of_mem_primeFactors hp)
      exact Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ (by omega))

lemma consecutiveProduct_one (n : ℕ) :
    consecutiveProduct n 1 = n * (n + 1) := by
  simp [consecutiveProduct, Finset.prod_range_succ]

theorem length_one_upper :
    ∀ ε : ℝ, 0 < ε →
      ∀ᶠ n : ℕ in atTop,
        (powerfulPart (consecutiveProduct n 1) : ℝ) <
          (n : ℝ) ^ (2 + ε) := by
  intro ε hε
  have hpow :
      Tendsto (fun n : ℕ => (n : ℝ) ^ ε) atTop atTop :=
    (tendsto_rpow_atTop hε).comp tendsto_natCast_atTop_atTop
  filter_upwards
      [hpow.eventually (eventually_gt_atTop (2 : ℝ)),
       eventually_ge_atTop 1] with n hnε hn
  have hprod0 : consecutiveProduct n 1 ≠ 0 := by
    rw [consecutiveProduct_one]
    positivity
  have hpart := powerfulPart_le (consecutiveProduct n 1) hprod0
  rw [consecutiveProduct_one] at hpart
  calc
    (powerfulPart (consecutiveProduct n 1) : ℝ)
        ≤ ((n * (n + 1) : ℕ) : ℝ) := by
          rw [consecutiveProduct_one]
          exact_mod_cast hpart
    _ = (n : ℝ) * (n + 1 : ℕ) := by norm_num
    _ ≤ (n : ℝ) * (2 * n : ℕ) := by
      gcongr
      omega
    _ < (n : ℝ) * ((n : ℝ) * ((n : ℝ) ^ ε)) := by
      have hnpos : (0 : ℝ) < n := by positivity
      norm_num only [Nat.cast_mul, Nat.cast_ofNat]
      apply mul_lt_mul_of_pos_left _ hnpos
      simpa [mul_comm] using mul_lt_mul_of_pos_left hnε hnpos
    _ = (n : ℝ) ^ (2 + ε) := by
      rw [Real.rpow_add (by positivity)]
      norm_num [Real.rpow_two]
      ring

theorem proof :
    (let powerfulPart : ℕ → ℕ := fun n =>
       n.factorization.prod fun p e => if 2 ≤ e then p ^ e else 1
     let consecutiveProduct : ℕ → ℕ → ℕ := fun n ℓ =>
       ∏ i ∈ Finset.range (ℓ + 1), (n + i)
     ∀ ε : ℝ, 0 < ε →
       ∀ᶠ n : ℕ in atTop,
         (powerfulPart (consecutiveProduct n 1) : ℝ) <
           (n : ℝ) ^ (2 + ε)) := by
  simpa only [powerfulPart, consecutiveProduct] using length_one_upper

end Submissions.Erdos935LengthOneUpper.Direct
