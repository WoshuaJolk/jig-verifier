import Mathlib.Analysis.PSeries
import Mathlib.Data.Nat.Prime.Nth
import Mathlib.Topology.Algebra.InfiniteSum.Real

namespace Statements.Erdos15AlternatingPartialSums

open Filter
open scoped Topology

/-- The terms of Erdős problem 15: `pₙ` is the zero-indexed sequence of primes. -/
noncomputable def term (n : ℕ) : ℝ :=
  (-1 : ℝ) ^ (n + 1) * (n + 1) / Nat.nth Nat.Prime n

/-- **Erdős problem 15, as asked.**

Does the alternating series `∑ (-1)^{n+1}(n+1)/pₙ` converge?  Convergence of the
partial sums, not `Summable`: the series is not absolutely convergent
(`|term n| = (n+1)/pₙ ≥ 1/pₙ` and `∑ 1/p` diverges), so `Summable term` is false
and is not what the problem asks. -/
abbrev statement : Prop :=
  ∃ L : ℝ, Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N, term n) atTop (𝓝 L)

theorem target : statement := sorry

end Statements.Erdos15AlternatingPartialSums
