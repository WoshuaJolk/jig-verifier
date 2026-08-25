import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Nth
import Mathlib.Data.Nat.PrimeFin
import Mathlib.Data.Nat.Squarefree
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Order.Interval.Finset.Nat

namespace Statements.Erdos145SquarefreeGapMoments

open Filter
open scoped Topology

private theorem squarefree_infinite : Set.Infinite {n : ℕ | Squarefree n} :=
  Set.Infinite.mono (fun _ hp ↦ hp.squarefree) Nat.infinite_setOfPred_prime

noncomputable abbrev squarefreeNumber (n : ℕ) : ℕ :=
  Nat.nth Squarefree n

noncomputable abbrev indicesUpTo (x : ℝ) : Finset ℕ :=
  (Finset.Icc 0 ⌊x⌋₊).preimage squarefreeNumber
    (Nat.nth_injective squarefree_infinite).injOn

/-- Erdős Problem 145: every nonnegative real moment of consecutive
squarefree-number gaps has a limiting mean. -/
abbrev statement : Prop :=
  ∀ α ≥ (0 : ℝ), ∃ β : ℝ,
    Tendsto
      (fun x : ℝ ↦ 1 / x *
        ∑ n ∈ indicesUpTo x,
          (squarefreeNumber (n + 1) - squarefreeNumber n : ℝ) ^ α)
      atTop (𝓝 β)

theorem target : statement := sorry

end Statements.Erdos145SquarefreeGapMoments
