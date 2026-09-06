import Mathlib.NumberTheory.FactorisationProperties
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.IntervalCases

namespace Submissions.Erdos470SigmaProductBound.Direct

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

theorem proof : ∀ n : ℕ, 2 ≤ n →
    ArithmeticFunction.sigma 1 n * ∏ p ∈ n.primeFactors, (p - 1) <
      n * ∏ p ∈ n.primeFactors, p :=
  fun n hn => sigma_mul_prod_pred_lt n hn

end Submissions.Erdos470SigmaProductBound.Direct
