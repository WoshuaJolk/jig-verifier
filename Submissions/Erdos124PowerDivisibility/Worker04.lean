import Mathlib.Algebra.Group.Pointwise.Set.BigOperators
import Mathlib.Algebra.BigOperators.Ring.Finset

namespace Submissions.Erdos124PowerDivisibility.Worker04

def sumsOfDistinctPowers (d k : ℕ) : Set ℕ :=
  {x | ∃ s : Finset ℕ, (∀ i ∈ s, k ≤ i) ∧ ∑ i ∈ s, d ^ i = x}

theorem proof :
    ∀ d k n : ℕ, n ∈ sumsOfDistinctPowers d k → d ^ k ∣ n := by
  rintro d k n ⟨s, hs, rfl⟩
  apply Finset.dvd_sum
  intro i hi
  exact pow_dvd_pow d (hs i hi)

end Submissions.Erdos124PowerDivisibility.Worker04
