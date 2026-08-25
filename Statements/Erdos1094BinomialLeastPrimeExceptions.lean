import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Set.Finite.Basic

namespace Statements.Erdos1094BinomialLeastPrimeExceptions

/-- Erdős Problem 1094: only finitely many admissible binomial coefficients
have least prime factor larger than both `n/k` and `k`. -/
abbrev statement : Prop :=
  {(n, k) : ℕ × ℕ |
      0 < k ∧ 2 * k ≤ n ∧
        (n.choose k).minFac > max (n / k) k}.Finite

theorem target : statement := sorry

end Statements.Erdos1094BinomialLeastPrimeExceptions
