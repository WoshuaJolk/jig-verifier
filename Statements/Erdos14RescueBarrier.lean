import Mathlib

namespace Statements.Erdos14RescueBarrier

open scoped BigOperators

def varianceDefect (N : ℕ) (f : ℕ → ℕ) : ℕ :=
  N * (∑ i ∈ Finset.range N, f i ^ 2) -
    (∑ i ∈ Finset.range N, f i) ^ 2

def exceptionCount (N : ℕ) (f g : ℕ → ℕ) : ℕ :=
  ((Finset.range N).filter fun i => f i + g i ≠ 1).card

/-- Linear cross-profile defect alone cannot force exceptions: a second
representation channel may rescue every deficient position. -/
abbrev statement : Prop :=
  ∀ N : ℕ, 2 ≤ N →
    ∃ f g : ℕ → ℕ,
      (∃ i ∈ Finset.range N, ∃ j ∈ Finset.range N, f i ≠ f j) ∧
      varianceDefect N f = N - 1 ∧
      exceptionCount N f g = 0

theorem target : statement := sorry

end Statements.Erdos14RescueBarrier
