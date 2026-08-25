import Mathlib.Tactic

namespace Statements.Erdos661TwoPointSetsWitness

abbrev Point := ℝ × ℝ

def x : Fin 2 → Point
  | ⟨0, _⟩ => (0, 0)
  | ⟨1, _⟩ => (1, 0)

def y : Fin 2 → Point
  | ⟨0, _⟩ => (0, 1)
  | ⟨1, _⟩ => (1, 1)

abbrev statement : Prop :=
  Function.Injective x ∧ Function.Injective y

theorem target : statement := sorry

end Statements.Erdos661TwoPointSetsWitness
