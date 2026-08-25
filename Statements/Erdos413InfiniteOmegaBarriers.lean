import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Set.Finite.Basic

namespace Statements.Erdos413InfiniteOmegaBarriers

def omega (n : ℕ) : ℕ :=
  n.factorization.support.card

def IsBarrier (n : ℕ) : Prop :=
  ∀ m < n, m + omega m ≤ n

/-- Erdős Problem 413, part (i): there are infinitely many barriers for
the number of distinct prime factors. -/
abbrev statement : Prop :=
  Set.Infinite {n : ℕ | IsBarrier n}

theorem target : statement := sorry

end Statements.Erdos413InfiniteOmegaBarriers
