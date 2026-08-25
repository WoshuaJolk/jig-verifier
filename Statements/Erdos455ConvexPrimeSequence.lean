import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Topology.Instances.Real.Lemmas

open Filter

namespace Statements.Erdos455ConvexPrimeSequence

/-- Erdős Problem 455: a strictly increasing prime sequence with
nondecreasing consecutive gaps grows superquadratically. -/
abbrev statement : Prop :=
  ∀ q : ℕ → ℕ, StrictMono q →
    (∀ n, (q n).Prime ∧
      q (n + 2) - q (n + 1) ≥ q (n + 1) - q n) →
    Tendsto (fun n : ℕ => (q n : ℝ) / n ^ 2) atTop atTop

theorem target : statement := sorry

end Statements.Erdos455ConvexPrimeSequence
