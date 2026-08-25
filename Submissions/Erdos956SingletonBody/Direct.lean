import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
namespace Submissions.Erdos956SingletonBody.Direct
abbrev Point := EuclideanSpace ℝ (Fin 2)
def origin : Point := 0
theorem proof : ({origin} : Set Point).Nonempty ∧ Convex ℝ ({origin} : Set Point) ∧ IsCompact ({origin} : Set Point) := by
  exact ⟨Set.singleton_nonempty _, convex_singleton _, isCompact_singleton⟩
end Submissions.Erdos956SingletonBody.Direct
