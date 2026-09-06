import Mathlib.NumberTheory.FactorisationProperties
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.IntervalCases

namespace Submissions.Erdos470SevenPrimesIfNotThree.Direct

open ArithmeticFunction Finset

/-- `σ(p^a) * (p - 1) + 1 = p^(a+1)` for a prime `p`. -/
lemma sigma_prime_pow_mul_pred_add_one {p : ℕ} (hp : p.Prime) (a : ℕ) :
    ArithmeticFunction.sigma 1 (p ^ a) * (p - 1) + 1 = p ^ (a + 1) := by
  rw [sigma_one_apply_prime_pow hp]
  have h := geom_sum_mul_add (p - 1) (a + 1)
  have hp1 : p - 1 + 1 = p := Nat.sub_add_cancel hp.one_lt.le
  rw [hp1] at h
  exact h

/-- The general bound `σ(n) ∏_{p|n} (p-1) < n ∏_{p|n} p` for `n ≥ 2`. -/
theorem sigma_mul_prod_pred_lt (n : ℕ) (hn : 2 ≤ n) :
    ArithmeticFunction.sigma 1 n * ∏ p ∈ n.primeFactors, (p - 1) <
      n * ∏ p ∈ n.primeFactors, p := by
  have hn0 : n ≠ 0 := by omega
  have hσ : ArithmeticFunction.sigma 1 n =
      ∏ p ∈ n.primeFactors, ArithmeticFunction.sigma 1 (p ^ n.factorization p) := by
    rw [isMultiplicative_sigma.multiplicative_factorization _ hn0, Finsupp.prod,
      Nat.support_factorization]
  have hnprod : n = ∏ p ∈ n.primeFactors, p ^ n.factorization p := by
    conv_lhs => rw [← Nat.prod_factorization_pow_eq_self hn0]
    rw [Finsupp.prod, Nat.support_factorization]
  have hne : n.primeFactors.Nonempty := Nat.nonempty_primeFactors.mpr (by omega)
  calc ArithmeticFunction.sigma 1 n * ∏ p ∈ n.primeFactors, (p - 1)
      = ∏ p ∈ n.primeFactors,
          (ArithmeticFunction.sigma 1 (p ^ n.factorization p) * (p - 1)) := by
        rw [hσ, Finset.prod_mul_distrib]
    _ < ∏ p ∈ n.primeFactors, (p ^ n.factorization p * p) := by
        apply Finset.prod_lt_prod_of_nonempty
        · intro p hp
          have hpp := Nat.prime_of_mem_primeFactors hp
          have h := sigma_prime_pow_mul_pred_add_one hpp (n.factorization p)
          have h2 : 2 ≤ p ^ (n.factorization p + 1) :=
            le_trans hpp.two_le (Nat.le_self_pow (by omega) p)
          omega
        · intro p hp
          have hpp := Nat.prime_of_mem_primeFactors hp
          have h := sigma_prime_pow_mul_pred_add_one hpp (n.factorization p)
          rw [pow_succ] at h
          omega
        · exact hne
    _ = (∏ p ∈ n.primeFactors, p ^ n.factorization p) * ∏ p ∈ n.primeFactors, p := by
        rw [Finset.prod_mul_distrib]
    _ = n * ∏ p ∈ n.primeFactors, p := by rw [← hnprod]

/-- The finite check behind the tiered bound: for `A ⊆ {5,7,11,13}` and `6 - |A|`
further primes each `≥ 17`, the product of `p/(p-1)` stays at most `2`. -/
lemma finite_check : ∀ A ∈ ({5, 7, 11, 13} : Finset ℕ).powerset,
    (∏ p ∈ A, p) * 17 ^ (6 - A.card) ≤ 2 * (∏ p ∈ A, (p - 1)) * 16 ^ (6 - A.card) := by
  decide

/-- Any set of at most six primes all `≥ 5` has `∏ p ≤ 2 ∏ (p - 1)`. -/
lemma prod_le_two_mul_prod_pred (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime ∧ 5 ≤ p)
    (hcard : S.card ≤ 6) : ∏ p ∈ S, p ≤ 2 * ∏ p ∈ S, (p - 1) := by
  -- split into the small part A (≤ 16) and the large part B (≥ 17)
  set A := S.filter (fun p => p ≤ 16) with hAdef
  set B := S.filter (fun p => ¬ p ≤ 16) with hBdef
  have hsplit : ∀ f : ℕ → ℚ, (∏ p ∈ A, f p) * (∏ p ∈ B, f p) = ∏ p ∈ S, f p :=
    fun f => Finset.prod_filter_mul_prod_filter_not S (fun p => p ≤ 16) f
  have hcardAB : A.card + B.card = S.card := Finset.card_filter_add_card_filter_not _
  have hA : A ⊆ {5, 7, 11, 13} := by
    intro p hp
    rw [hAdef, Finset.mem_filter] at hp
    obtain ⟨hpS, hp16⟩ := hp
    obtain ⟨hpp, hp5⟩ := hS p hpS
    interval_cases p <;> first | decide | (norm_num at hpp)
  have hB : ∀ p ∈ B, 17 ≤ p := by
    intro p hp
    rw [hBdef, Finset.mem_filter] at hp
    omega
  -- the finite check, instantiated at A, in ℚ
  have hAcheck := finite_check A (Finset.mem_powerset.mpr hA)
  have hAcard : A.card ≤ 4 := le_trans (Finset.card_le_card hA) (by decide)
  have hBcard : B.card ≤ 6 - A.card := by omega
  -- work in ℚ
  have hposA : (0 : ℚ) < ∏ p ∈ A, ((p : ℚ) - 1) := by
    apply Finset.prod_pos
    intro p hp
    have := (hS p (Finset.mem_of_mem_filter p hp)).2
    have : (5 : ℚ) ≤ p := by exact_mod_cast this
    linarith
  have hcastA : ((∏ p ∈ A, (p - 1) : ℕ) : ℚ) = ∏ p ∈ A, ((p : ℚ) - 1) := by
    rw [Nat.cast_prod]
    refine Finset.prod_congr rfl fun p hp => ?_
    have := (hS p (Finset.mem_of_mem_filter p hp)).2
    rw [Nat.cast_sub (by omega)]
    simp
  have hcastB : ((∏ p ∈ B, (p - 1) : ℕ) : ℚ) = ∏ p ∈ B, ((p : ℚ) - 1) := by
    rw [Nat.cast_prod]
    refine Finset.prod_congr rfl fun p hp => ?_
    have := hB p hp
    rw [Nat.cast_sub (by omega)]
    simp
  have hcastS : ((∏ p ∈ S, (p - 1) : ℕ) : ℚ) = ∏ p ∈ S, ((p : ℚ) - 1) := by
    rw [Nat.cast_prod]
    refine Finset.prod_congr rfl fun p hp => ?_
    have := (hS p hp).2
    rw [Nat.cast_sub (by omega)]
    simp
  -- A-part in ℚ: ∏_A p * (17/16)^(6 - |A|) ≤ 2 ∏_A (p - 1)
  have hAq : (∏ p ∈ A, (p : ℚ)) * (17 / 16 : ℚ) ^ (6 - A.card) ≤
      2 * ∏ p ∈ A, ((p : ℚ) - 1) := by
    have h : ((∏ p ∈ A, p : ℕ) : ℚ) * (17 : ℚ) ^ (6 - A.card) ≤
        2 * ((∏ p ∈ A, (p - 1) : ℕ) : ℚ) * (16 : ℚ) ^ (6 - A.card) := by
      exact_mod_cast hAcheck
    rw [Nat.cast_prod, hcastA] at h
    rw [div_pow]
    rw [mul_div_assoc', div_le_iff₀ (by positivity)]
    linarith
  -- B-part in ℚ: ∏_B p ≤ (17/16)^|B| ∏_B (p - 1) ≤ (17/16)^(6-|A|) ∏_B (p - 1)
  have hBq : (∏ p ∈ B, (p : ℚ)) ≤ (17 / 16 : ℚ) ^ B.card * ∏ p ∈ B, ((p : ℚ) - 1) := by
    rw [← Finset.prod_const, ← Finset.prod_mul_distrib]
    apply Finset.prod_le_prod
    · intro p hp; positivity
    · intro p hp
      have := hB p hp
      have : (17 : ℚ) ≤ p := by exact_mod_cast this
      linarith
  have hposB : (0 : ℚ) ≤ ∏ p ∈ B, ((p : ℚ) - 1) := by
    apply Finset.prod_nonneg
    intro p hp
    have := hB p hp
    have : (17 : ℚ) ≤ p := by exact_mod_cast this
    linarith
  have hpow : (17 / 16 : ℚ) ^ B.card ≤ (17 / 16 : ℚ) ^ (6 - A.card) :=
    pow_le_pow_right₀ (by norm_num) hBcard
  have hprodA_nonneg : (0 : ℚ) ≤ ∏ p ∈ A, (p : ℚ) := Finset.prod_nonneg fun p _ => by positivity
  have hq : (∏ p ∈ S, (p : ℚ)) ≤ 2 * ∏ p ∈ S, ((p : ℚ) - 1) := by
    rw [← hsplit (fun p => (p : ℚ)), ← hsplit (fun p => (p : ℚ) - 1)]
    calc (∏ p ∈ A, (p : ℚ)) * (∏ p ∈ B, (p : ℚ))
        ≤ (∏ p ∈ A, (p : ℚ)) * ((17 / 16 : ℚ) ^ B.card * ∏ p ∈ B, ((p : ℚ) - 1)) :=
          mul_le_mul_of_nonneg_left hBq hprodA_nonneg
      _ ≤ (∏ p ∈ A, (p : ℚ)) * ((17 / 16 : ℚ) ^ (6 - A.card) * ∏ p ∈ B, ((p : ℚ) - 1)) := by
          apply mul_le_mul_of_nonneg_left _ hprodA_nonneg
          exact mul_le_mul_of_nonneg_right hpow hposB
      _ = ((∏ p ∈ A, (p : ℚ)) * (17 / 16 : ℚ) ^ (6 - A.card)) * ∏ p ∈ B, ((p : ℚ) - 1) := by
          ring
      _ ≤ (2 * ∏ p ∈ A, ((p : ℚ) - 1)) * ∏ p ∈ B, ((p : ℚ) - 1) :=
          mul_le_mul_of_nonneg_right hAq hposB
      _ = 2 * ((∏ p ∈ A, ((p : ℚ) - 1)) * ∏ p ∈ B, ((p : ℚ) - 1)) := by ring
  have hq' : ((∏ p ∈ S, p : ℕ) : ℚ) ≤ 2 * ((∏ p ∈ S, (p - 1) : ℕ) : ℚ) := by
    rw [Nat.cast_prod, hcastS]; exact hq
  exact_mod_cast hq'

/-- An odd abundant number not divisible by 3 has at least seven distinct prime factors. -/
theorem seven_le_of_odd_abundant_not_three (n : ℕ) (hodd : Odd n) (h3 : ¬ 3 ∣ n)
    (hab : n.Abundant) : 7 ≤ n.primeFactors.card := by
  have hn0 : n ≠ 0 := hab.pos.ne'
  have hn1 : n ≠ 1 := by
    rintro rfl
    exact absurd hab (by decide)
  have hn2 : 2 ≤ n := by omega
  have hS : ∀ p ∈ n.primeFactors, p.Prime ∧ 5 ≤ p := by
    intro p hp
    have hpp := Nat.prime_of_mem_primeFactors hp
    have hpn := Nat.dvd_of_mem_primeFactors hp
    refine ⟨hpp, ?_⟩
    have hp2 : p ≠ 2 := by
      rintro rfl
      exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr hpn)
    have hp3 : p ≠ 3 := by
      rintro rfl
      exact h3 hpn
    have hp4 : p ≠ 4 := by
      rintro rfl
      norm_num at hpp
    have := hpp.two_le
    omega
  by_contra hlt
  have hcard : n.primeFactors.card ≤ 6 := by omega
  have hkey := prod_le_two_mul_prod_pred n.primeFactors hS hcard
  have hgen := sigma_mul_prod_pred_lt n hn2
  have hpos : 0 < ∏ p ∈ n.primeFactors, (p - 1) := by
    apply Finset.prod_pos
    intro p hp
    have := (hS p hp).2
    omega
  have habund := Nat.abundant_iff_sum_divisors.mp hab
  rw [← sigma_one_apply] at habund
  have h1 : ArithmeticFunction.sigma 1 n * ∏ p ∈ n.primeFactors, (p - 1) <
      (2 * n) * ∏ p ∈ n.primeFactors, (p - 1) := by
    calc ArithmeticFunction.sigma 1 n * ∏ p ∈ n.primeFactors, (p - 1)
        < n * ∏ p ∈ n.primeFactors, p := hgen
      _ ≤ n * (2 * ∏ p ∈ n.primeFactors, (p - 1)) := Nat.mul_le_mul_left _ hkey
      _ = (2 * n) * ∏ p ∈ n.primeFactors, (p - 1) := by ring
  have h2 := Nat.lt_of_mul_lt_mul_right h1
  omega

theorem proof : ∀ n : ℕ, Odd n → ¬ 3 ∣ n → n.Weird → 7 ≤ n.primeFactors.card :=
  fun n hodd h3 hw => seven_le_of_odd_abundant_not_three n hodd h3 hw.1

end Submissions.Erdos470SevenPrimesIfNotThree.Direct
