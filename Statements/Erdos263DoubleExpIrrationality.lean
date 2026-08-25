import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Instances.Irrational

open Filter
open scoped Topology

namespace Statements.Erdos263DoubleExpIrrationality

def IsIrrationalitySequence (a : ℕ → ℕ) : Prop :=
  (∀ n : ℕ, a n > 0) ∧
  StrictMono a ∧
  (∀ b : ℕ → ℕ, (∀ n : ℕ, b n > 0) ∧
    atTop.Tendsto (fun n : ℕ => (a n : ℝ) / (b n : ℝ)) (𝓝 1) →
      Irrational (∑' n, 1 / (b n : ℝ)))

/-- Erdős Problem 263(i), with the corrected increasing-sequence definition. -/
abbrev statement : Prop :=
  IsIrrationalitySequence (fun n : ℕ => 2 ^ 2 ^ n)

theorem target : statement := sorry

end Statements.Erdos263DoubleExpIrrationality
