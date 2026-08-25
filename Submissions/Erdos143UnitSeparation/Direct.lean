import Mathlib.Data.Set.Countable
import Mathlib.Topology.Instances.Real.Lemmas

namespace Submissions.Erdos143UnitSeparation.Direct

def WellSeparatedSet (A : Set ℝ) : Prop :=
  A ⊆ Set.Ioi (1 : ℝ) ∧ Set.Infinite A ∧ Set.Countable A ∧
    ∀ x ∈ A, ∀ y ∈ A, x ≠ y →
      ∀ k ≥ (1 : ℕ), 1 ≤ |(k : ℝ) * x - y|

theorem proof :
    ∀ A : Set ℝ, WellSeparatedSet A →
      ∀ x ∈ A, ∀ y ∈ A, x ≠ y → 1 ≤ |x - y| := by
  intro A hA x hx y hy hxy
  rcases hA with ⟨_, _, _, hsep⟩
  simpa using hsep x hx y hy hxy 1 (by decide)

end Submissions.Erdos143UnitSeparation.Direct
