import Mathlib.NumberTheory.ArithmeticFunction.Misc

namespace Statements.Erdos470SigmaProductBound

/-- For every `n ≥ 2`, `σ(n) · ∏_{p | n} (p - 1) < n · ∏_{p | n} p`, the product over the
distinct prime factors of `n`; equivalently `σ(n)/n < ∏_{p | n} p/(p-1)`. -/
abbrev statement : Prop :=
  ∀ n : ℕ, 2 ≤ n →
    ArithmeticFunction.sigma 1 n * ∏ p ∈ n.primeFactors, (p - 1) <
      n * ∏ p ∈ n.primeFactors, p

theorem target : statement := sorry

end Statements.Erdos470SigmaProductBound
