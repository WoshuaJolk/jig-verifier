import Mathlib

namespace Statements.Erdos16PrimePowerAPDensity

open Filter Nat Set
open scoped Topology

/-- The odd natural numbers not representable as a prime plus a nonnegative power of two. -/
def exceptional : Set ℕ :=
  {n | Odd n ∧ ¬ ∃ k p : ℕ, p.Prime ∧ n = 2 ^ k + p}

/-- Natural density zero, using strict initial segments. -/
def densityZero (S : Set ℕ) : Prop :=
  open scoped Classical in
  Tendsto (fun x : ℕ => (count (· ∈ S) x : ℝ) / (x : ℝ)) atTop (𝓝 0)

/-- Erdős Problem 16 (Chen): the exceptional set is not the union of one infinite arithmetic progression and a density-zero set. -/
abbrev statement : Prop :=
  ¬ ∃ A B : Set ℕ, exceptional = A ∪ B ∧
    (∃ a d : ℕ, d > 0 ∧ A = {x | ∃ m : ℕ, x = a + m * d}) ∧
    densityZero B

theorem target : statement := sorry

end Statements.Erdos16PrimePowerAPDensity
