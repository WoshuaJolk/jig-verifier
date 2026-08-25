import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Int.ModEq
import Mathlib.Order.Interval.Finset.Nat

namespace Statements.Erdos25TruncatedCongruenceLogDensity

open Filter Finset Real Nat Set
open scoped Topology

/-- The logarithmic density predicate used by the formal-conjectures statement. -/
def HasLogDensity25 (A : Set ℕ) (d : ℝ) : Prop :=
  open scoped Classical in
  Tendsto (fun n : ℕ => (∑ k ≤ n with k ∈ A, (k : ℝ)⁻¹ / .log n : ℝ)) atTop (𝓝 d)

/-- Erdős Problem 25: every truncated one-class congruence sieve has logarithmic density. -/
abbrev statement : Prop :=
  ∀ (seq_n : ℕ → ℕ) (seq_a : ℕ → ℤ), (∀ i, 0 < seq_n i) → StrictMono seq_n →
    ∃ d, HasLogDensity25
      {x : ℕ | ∀ i, (x : ℤ) < seq_n i ∨ ¬((x : ℤ) ≡ seq_a i [ZMOD seq_n i])} d

theorem target : statement := sorry

end Statements.Erdos25TruncatedCongruenceLogDensity
