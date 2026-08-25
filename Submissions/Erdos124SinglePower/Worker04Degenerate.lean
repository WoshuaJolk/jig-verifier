import Mathlib.Algebra.Group.Pointwise.Set.BigOperators

namespace Submissions.Erdos124SinglePower.Worker04Degenerate

def sumsOfDistinctPowers (d k : ℕ) : Set ℕ :=
  {x | ∃ s : Finset ℕ, (∀ i ∈ s, k ≤ i) ∧ ∑ i ∈ s, d ^ i = x}

theorem proof :
    False → ∀ d k : ℕ, d ^ k ∈ sumsOfDistinctPowers d k :=
  False.elim

end Submissions.Erdos124SinglePower.Worker04Degenerate
