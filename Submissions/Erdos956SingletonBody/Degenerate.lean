import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
namespace Submissions.Erdos956SingletonBody.Degenerate
abbrev Point := EuclideanSpace ℝ (Fin 2)
def origin : Point := 0
theorem proof : False → ({origin} : Set Point).Nonempty ∧ Convex ℝ ({origin} : Set Point) ∧ IsCompact ({origin} : Set Point) := False.elim
end Submissions.Erdos956SingletonBody.Degenerate
