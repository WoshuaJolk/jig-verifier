import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Order.Interval.Finset.Nat

namespace Statements.Erdos421InitialTermAtLeastTwo

open Set

def DistinctBlocks (d : ℕ → ℕ) : Prop :=
  {(u, v) : ℕ × ℕ | u ≤ v}.InjOn
    (fun uv ↦ ∏ i ∈ Finset.Icc uv.1 uv.2, d i)

/-- Any positive sequence with distinct nonempty consecutive-block products
must start at least at two: if `d 0 = 1`, blocks `[0,1]` and `[1,1]`
collide. -/
abbrev statement : Prop :=
  ∀ d : ℕ → ℕ, 1 ≤ d 0 → DistinctBlocks d → 2 ≤ d 0

theorem target : statement := sorry

end Statements.Erdos421InitialTermAtLeastTwo
