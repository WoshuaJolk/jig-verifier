import Mathlib.NumberTheory.FactorisationProperties
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace Submissions.Erdos470ThreePrimeFactors.Direct

open ArithmeticFunction Finset

/-- `σ(p^a) * (p - 1) + 1 = p^(a+1)` for a prime `p`. -/
lemma sigma_prime_pow_mul_pred_add_one {p : ℕ} (hp : p.Prime) (a : ℕ) :
    ArithmeticFunction.sigma 1 (p ^ a) * (p - 1) + 1 = p ^ (a + 1) := by
  rw [sigma_one_apply_prime_pow hp]
  have h := geom_sum_mul_add (p - 1) (a + 1)
  have hp1 : p - 1 + 1 = p := Nat.sub_add_cancel hp.one_lt.le
  rw [hp1] at h
  exact h

/-- The core inequality: for distinct odd primes `p < q` and `a b ≥ 1`,
`σ(p^a * q^b) < 2 * p^a * q^b`. -/
lemma sigma_two_odd_primes_lt {p q a b : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hp3 : 3 ≤ p) (hq5 : 5 ≤ q) (hpq : p ≠ q) :
    ArithmeticFunction.sigma 1 (p ^ a * q ^ b) < 2 * (p ^ a * q ^ b) := by
  have hcop : Nat.Coprime (p ^ a) (q ^ b) := (Nat.coprime_pow_primes a b hp hq hpq)
  rw [isMultiplicative_sigma.map_mul_of_coprime hcop]
  have hA := sigma_prime_pow_mul_pred_add_one hp a
  have hB := sigma_prime_pow_mul_pred_add_one hq b
  set A := ArithmeticFunction.sigma 1 (p ^ a) with hAdef
  set B := ArithmeticFunction.sigma 1 (q ^ b) with hBdef
  set u := p ^ a with hu
  set v := q ^ b with hv
  rw [pow_succ] at hA hB
  -- hA : A * (p - 1) + 1 = u * p, hB : B * (q - 1) + 1 = v * q
  obtain ⟨x, rfl⟩ : ∃ x, p = x + 1 := ⟨p - 1, by omega⟩
  obtain ⟨y, rfl⟩ : ∃ y, q = y + 1 := ⟨q - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at hA hB
  have hx : 2 ≤ x := by omega
  have hy : 4 ≤ y := by omega
  have hxy : 0 < x * y := by positivity
  -- A * x < (x+1) * u and B * y < (y+1) * v
  have h1 : A * x < (x + 1) * u := by nlinarith
  have h2 : B * y < (y + 1) * v := by nlinarith
  have h3 : (x + 1) * (y + 1) ≤ 2 * (x * y) := by nlinarith
  have h4 : A * B * (x * y) < 2 * (u * v) * (x * y) := by
    calc A * B * (x * y) = (A * x) * (B * y) := by ring
      _ < ((x + 1) * u) * ((y + 1) * v) :=
          Nat.mul_lt_mul_of_lt_of_lt h1 h2
      _ = (x + 1) * (y + 1) * (u * v) := by ring
      _ ≤ 2 * (x * y) * (u * v) := Nat.mul_le_mul_right _ h3
      _ = 2 * (u * v) * (x * y) := by ring
  exact Nat.lt_of_mul_lt_mul_right h4

/-- An odd abundant number has at least three distinct prime factors. -/
theorem three_le_card_primeFactors_of_odd_abundant (n : ℕ) (hodd : Odd n)
    (hab : n.Abundant) : 3 ≤ n.primeFactors.card := by
  have hn0 : n ≠ 0 := hab.pos.ne'
  have hn1 : n ≠ 1 := by
    rintro rfl
    exact absurd hab (by decide)
  have hn2 : 2 ≤ n := by omega
  -- at least two, as in the existing proof
  have hnpp : ¬IsPrimePow n := by
    intro hpp
    have hdef := hpp.deficient
    unfold Nat.Deficient at hdef
    unfold Nat.Abundant at hab
    omega
  have hnontrivial : n.primeFactors.Nontrivial :=
    (Nat.not_isPrimePow_iff_nontrivial_of_two_le hn2).mp hnpp
  have h2 : 2 ≤ n.primeFactors.card := Finset.one_lt_card_iff_nontrivial.mpr hnontrivial
  by_contra hlt
  have hcard : n.primeFactors.card = 2 := by omega
  obtain ⟨p, q, hpq, hpf⟩ := Finset.card_eq_two.mp hcard
  have hp : p.Prime := Nat.prime_of_mem_primeFactors (by rw [hpf]; simp)
  have hq : q.Prime := Nat.prime_of_mem_primeFactors (by rw [hpf]; simp)
  have hpn : p ∣ n := Nat.dvd_of_mem_primeFactors (by rw [hpf]; simp)
  have hqn : q ∣ n := Nat.dvd_of_mem_primeFactors (by rw [hpf]; simp)
  -- n = p ^ a * q ^ b
  have hfact : n = p ^ n.factorization p * q ^ n.factorization q := by
    conv_lhs => rw [← Nat.prod_factorization_pow_eq_self hn0]
    rw [Finsupp.prod, Nat.support_factorization, hpf, Finset.prod_pair hpq]
  -- p, q odd
  have hp2 : p ≠ 2 := by
    rintro rfl
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr hpn)
  have hq2 : q ≠ 2 := by
    rintro rfl
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr hqn)
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  have hq3 : 3 ≤ q := by have := hq.two_le; omega
  have hpodd : Odd p := hp.odd_of_ne_two hp2
  have hqodd : Odd q := hq.odd_of_ne_two hq2
  have habund := Nat.abundant_iff_sum_divisors.mp hab
  rw [← sigma_one_apply] at habund
  -- WLOG p < q
  rcases lt_or_gt_of_ne hpq with hlt' | hgt'
  · have hq5 : 5 ≤ q := by
      rcases hqodd with ⟨k, hk⟩
      omega
    have := sigma_two_odd_primes_lt (a := n.factorization p) (b := n.factorization q)
      hp hq hp3 hq5 hpq
    rw [← hfact] at this
    omega
  · have hp5 : 5 ≤ p := by
      rcases hpodd with ⟨k, hk⟩
      omega
    have := sigma_two_odd_primes_lt (a := n.factorization q) (b := n.factorization p)
      hq hp hq3 hp5 hpq.symm
    rw [mul_comm, ← hfact] at this
    omega

theorem proof : ∀ n : ℕ, Odd n → n.Weird → 3 ≤ n.primeFactors.card :=
  fun n hodd hw => three_le_card_primeFactors_of_odd_abundant n hodd hw.1

end Submissions.Erdos470ThreePrimeFactors.Direct
