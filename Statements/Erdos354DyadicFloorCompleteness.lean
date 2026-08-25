import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Data.Set.Finite.Lattice
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Order.Filter.AtTopBot.Basic

namespace Statements.Erdos354DyadicFloorCompleteness

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

/-- Erdős problem 354(i): the interleaved dyadic floor sequences are
additively complete whenever the ratio of their positive parameters is
irrational. -/
abbrev statement : Prop :=
  ∀ α β : ℝ, 0 < α → 0 < β → Irrational (α / β) →
    IsAddComplete (interleave α β 2)

theorem target : statement := sorry

end Statements.Erdos354DyadicFloorCompleteness
