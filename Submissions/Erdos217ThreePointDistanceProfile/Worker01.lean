import Mathlib.Tactic

namespace Submissions.Erdos217ThreePointDistanceProfile.Worker01

def P : Fin 3 → ℝ × ℝ
  | ⟨0, _⟩ => (-1, 0)
  | ⟨1, _⟩ => (1, 0)
  | ⟨2, _⟩ => (0, 1)

def sqDist (p q : ℝ × ℝ) : ℝ :=
  (p.1 - q.1) ^ 2 + (p.2 - q.2) ^ 2

def Collinear (p q r : ℝ × ℝ) : Prop :=
  (q.1 - p.1) * (r.2 - p.2) = (q.2 - p.2) * (r.1 - p.1)

theorem proof :
    Function.Injective P ∧ ¬Collinear (P 0) (P 1) (P 2) ∧
      sqDist (P 0) (P 1) = 4 ∧
      sqDist (P 0) (P 2) = 2 ∧ sqDist (P 1) (P 2) = 2 := by
  refine ⟨?_, by norm_num [Collinear, P], by norm_num [sqDist, P],
    by norm_num [sqDist, P], by norm_num [sqDist, P]⟩
  intro i j
  fin_cases i <;> fin_cases j <;> simp [P] <;> norm_num

end Submissions.Erdos217ThreePointDistanceProfile.Worker01
