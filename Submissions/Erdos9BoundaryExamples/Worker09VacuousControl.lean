import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic

namespace Submissions.Erdos9BoundaryExamples.Worker09VacuousControl

def Exceptional : Set ℕ :=
  {n | Odd n ∧ ¬ ∃ (p k l : ℕ), Nat.Prime p ∧ n = p + 2 ^ k + 2 ^ l}

theorem proof (h : False) :
    1 ∈ Exceptional ∧ 3 ∈ Exceptional ∧ 5 ∉ Exceptional := h.elim

end Submissions.Erdos9BoundaryExamples.Worker09VacuousControl
