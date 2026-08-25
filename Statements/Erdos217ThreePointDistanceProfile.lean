import Mathlib.Data.Fin.Basic
import Mathlib.Data.Real.Basic

namespace Statements.Erdos217ThreePointDistanceProfile

def P : Fin 3 → ℝ × ℝ
  | ⟨0, _⟩ => (-1, 0)
  | ⟨1, _⟩ => (1, 0)
  | ⟨2, _⟩ => (0, 1)

def sqDist (p q : ℝ × ℝ) : ℝ :=
  (p.1 - q.1) ^ 2 + (p.2 - q.2) ^ 2

def Collinear (p q r : ℝ × ℝ) : Prop :=
  (q.1 - p.1) * (r.2 - p.2) = (q.2 - p.2) * (r.1 - p.1)

/-- Three noncollinear points with two squared distances occurring once
and twice, the first instance of the `1,...,n-1` profile. -/
abbrev statement : Prop :=
  Function.Injective P ∧ ¬Collinear (P 0) (P 1) (P 2) ∧
    sqDist (P 0) (P 1) = 4 ∧
    sqDist (P 0) (P 2) = 2 ∧ sqDist (P 1) (P 2) = 2

theorem target : statement := sorry

end Statements.Erdos217ThreePointDistanceProfile
