import Mathlib.Algebra.Group.Pointwise.Set.BigOperators

namespace Submissions.Erdos124SinglePower.Worker04Smoke

def sumsOfDistinctPowers (d k : ℕ) : Set ℕ :=
  {x | ∃ s : Finset ℕ, (∀ i ∈ s, k ≤ i) ∧ ∑ i ∈ s, d ^ i = x}

theorem proof :
    ∀ d k : ℕ, d ^ k ∈ sumsOfDistinctPowers d k := by
  intro d k
  exact ⟨{k}, by simp, by simp⟩

end Submissions.Erdos124SinglePower.Worker04Smoke
