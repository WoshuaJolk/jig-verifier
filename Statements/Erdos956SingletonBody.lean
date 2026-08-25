import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
namespace Statements.Erdos956SingletonBody
abbrev Point := EuclideanSpace ℝ (Fin 2)
def origin : Point := 0
abbrev statement : Prop := ({origin} : Set Point).Nonempty ∧ Convex ℝ ({origin} : Set Point) ∧ IsCompact ({origin} : Set Point)
theorem target : statement := sorry
end Statements.Erdos956SingletonBody
