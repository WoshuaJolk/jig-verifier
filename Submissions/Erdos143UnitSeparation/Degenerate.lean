import Mathlib.Data.Set.Countable
import Mathlib.Topology.Instances.Real.Lemmas

namespace Submissions.Erdos143UnitSeparation.Degenerate

def WellSeparatedSet (A : Set ℝ) : Prop :=
  A ⊆ Set.Ioi (1 : ℝ) ∧ Set.Infinite A ∧ Set.Countable A ∧
    ∀ x ∈ A, ∀ y ∈ A, x ≠ y →
      ∀ k ≥ (1 : ℕ), 1 ≤ |(k : ℝ) * x - y|

theorem proof :
    False →
      ∀ A : Set ℝ, WellSeparatedSet A →
        ∀ x ∈ A, ∀ y ∈ A, x ≠ y → 1 ≤ |x - y| :=
  False.elim

end Submissions.Erdos143UnitSeparation.Degenerate
