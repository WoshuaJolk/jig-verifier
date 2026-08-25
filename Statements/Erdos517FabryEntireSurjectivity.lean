import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic

namespace Statements.Erdos517FabryEntireSurjectivity

open Filter Set

def HasFabryGaps (n : ℕ → ℕ) : Prop :=
  StrictMono n ∧ Tendsto (fun k ↦ n k / (k : ℝ)) atTop atTop

/-- Erdős Problem 517 (Fejér–Pólya): an everywhere-convergent power series
with nonzero coefficients and Fabry gaps assumes every complex value
infinitely often. -/
abbrev statement : Prop :=
  ∀ {f : ℂ → ℂ} {n : ℕ → ℕ}, HasFabryGaps n →
    ∀ {a : ℕ → ℂ}, (∀ k, a k ≠ 0) →
      (∀ z, HasSum (fun k ↦ a k * z ^ n k) (f z)) →
        ∀ z : ℂ, {x : ℂ | f x = z}.Infinite

theorem target : statement := sorry

end Statements.Erdos517FabryEntireSurjectivity
