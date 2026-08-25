import Mathlib.Data.Nat.Prime.Basic

/-!
# Prime-exponent reduction for Erdős problem 672

To exclude all nontrivial perfect powers, it is enough to exclude powers with
prime exponent.
-/

namespace Statements.Erdos672PrimeExponentReduction

abbrev statement : Prop :=
  ∀ x exponent : ℕ, exponent > 1 →
    (∃ q : ℕ, x = q ^ exponent) →
      ∃ p : ℕ, p.Prime ∧ p ∣ exponent ∧
        ∃ r : ℕ, x = r ^ p

theorem target : statement := sorry

end Statements.Erdos672PrimeExponentReduction
