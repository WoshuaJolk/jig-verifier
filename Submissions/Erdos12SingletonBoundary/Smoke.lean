import Mathlib.Topology.Algebra.InfiniteSum.Real

namespace Submissions.Erdos12SingletonBoundary.Smoke

theorem proof :
    ∀ a ∈ ({3} : Set ℕ), ∀ b ∈ ({3} : Set ℕ), ∀ c ∈ ({3} : Set ℕ),
      a ∣ b + c → a < b → a < c → b = c := by
  simp

end Submissions.Erdos12SingletonBoundary.Smoke
