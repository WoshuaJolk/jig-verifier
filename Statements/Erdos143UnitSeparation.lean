import Mathlib.Data.Set.Countable
import Mathlib.Topology.Instances.Real.Lemmas

namespace Statements.Erdos143UnitSeparation

def WellSeparatedSet (A : Set ℝ) : Prop :=
  A ⊆ Set.Ioi (1 : ℝ) ∧ Set.Infinite A ∧ Set.Countable A ∧
    ∀ x ∈ A, ∀ y ∈ A, x ≠ y →
      ∀ k ≥ (1 : ℕ), 1 ≤ |(k : ℝ) * x - y|

/-- Taking `k = 1` gives ordinary unit separation of distinct points. -/
abbrev statement : Prop :=
  ∀ A : Set ℝ, WellSeparatedSet A →
    ∀ x ∈ A, ∀ y ∈ A, x ≠ y → 1 ≤ |x - y|

theorem target : statement := sorry

end Statements.Erdos143UnitSeparation
