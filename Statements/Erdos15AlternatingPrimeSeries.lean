import Mathlib.Data.Nat.Prime.Nth
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.Ring.Real

/-!
# Erdős problem 15

Does the real alternating series `∑ (-1)^(n+1) (n+1) / p_n` converge,
where `p_n` is the zero-indexed sequence of primes?
-/

namespace Statements.Erdos15AlternatingPrimeSeries

noncomputable def term (n : ℕ) : ℝ :=
  (-1 : ℝ) ^ (n + 1) * (n + 1) / Nat.nth Nat.Prime n

abbrev statement : Prop := Summable term

theorem target : statement := sorry

end Statements.Erdos15AlternatingPrimeSeries
