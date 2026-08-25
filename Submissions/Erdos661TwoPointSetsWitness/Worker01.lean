import Mathlib.Tactic

namespace Submissions.Erdos661TwoPointSetsWitness.Worker01

abbrev Point := ℝ × ℝ

def x : Fin 2 → Point
  | ⟨0, _⟩ => (0, 0)
  | ⟨1, _⟩ => (1, 0)

def y : Fin 2 → Point
  | ⟨0, _⟩ => (0, 1)
  | ⟨1, _⟩ => (1, 1)

theorem proof : Function.Injective x ∧ Function.Injective y := by
  constructor <;> intro i j <;> fin_cases i <;> fin_cases j <;> simp [x, y]

end Submissions.Erdos661TwoPointSetsWitness.Worker01
