import Mathlib.Data.Nat.Prime.Basic

namespace Submissions.Erdos672PrimeExponentReduction.FactorExponent

theorem proof :
    ∀ x exponent : ℕ, exponent > 1 →
      (∃ q : ℕ, x = q ^ exponent) →
        ∃ p : ℕ, p.Prime ∧ p ∣ exponent ∧
          ∃ r : ℕ, x = r ^ p := by
  intro x exponent hexponent ⟨q, hq⟩
  obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd (by omega : exponent ≠ 1)
  obtain ⟨multiple, hmultiple⟩ := hpdvd
  refine ⟨p, hp, ⟨multiple, hmultiple⟩, q ^ multiple, ?_⟩
  calc
    x = q ^ exponent := hq
    _ = q ^ (multiple * p) := by rw [hmultiple, Nat.mul_comm]
    _ = (q ^ multiple) ^ p := pow_mul q multiple p

end Submissions.Erdos672PrimeExponentReduction.FactorExponent
