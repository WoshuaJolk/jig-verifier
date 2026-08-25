import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Data.Nat.BitIndices
import Mathlib.Data.Set.Finite.Lattice
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Order.Filter.AtTopBot.Basic

namespace Statements.Erdos354UnitDyadicStreamComplete

open Filter

noncomputable def floorMultiples (a γ : ℝ) (n : ℕ) : ℤ :=
  ⌊γ ^ n * a⌋

noncomputable def interleave (a b γ : ℝ) (n : ℕ) : ℤ :=
  if n % 2 = 0 then floorMultiples a γ (n / 2)
  else floorMultiples b γ (n / 2)

def subseqSums (A : ℕ → ℤ) : Set ℤ :=
  {n | ∃ B : Finset ℕ, n = ∑ i ∈ B, A i}

def IsAddComplete (A : ℕ → ℤ) : Prop :=
  ∀ᶠ k in atTop, k ∈ subseqSums A

/-- When one parameter is `1`, its dyadic floor stream is the binary
place-value sequence, so the interleaving is complete for every second
parameter. -/
abbrev statement : Prop :=
  ∀ β : ℝ, IsAddComplete (interleave 1 β 2)

theorem target : statement := sorry

end Statements.Erdos354UnitDyadicStreamComplete
