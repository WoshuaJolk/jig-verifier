import Mathlib

namespace Statements.Erdos500TuranDensity

open Filter

abbrev ThreeGraph (n : ℕ) := Finset (Finset (Fin n))

def IsThreeUniform {n : ℕ} (E : ThreeGraph n) : Prop :=
  ∀ e ∈ E, e.card = 3

def IsK4Free {n : ℕ} (E : ThreeGraph n) : Prop :=
  ∀ S : Finset (Fin n), S.card = 4 →
    ∃ T : Finset (Fin n), T ⊆ S ∧ T.card = 3 ∧ T ∉ E

noncomputable def turanNumber (n : ℕ) : ℕ :=
  sSup {m : ℕ | ∃ E : ThreeGraph n,
    IsThreeUniform E ∧ IsK4Free E ∧ E.card = m}

/-- Turán's `(3,4)` conjecture, Erdős problem 500. -/
abbrev statement : Prop :=
  Tendsto
    (fun n => (turanNumber n : ℝ) / Nat.choose n 3)
    atTop (nhds (5 / 9 : ℝ))

theorem target : statement := sorry

end Statements.Erdos500TuranDensity
