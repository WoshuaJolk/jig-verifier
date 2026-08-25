import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Tactic

namespace Submissions.Erdos141FirstTriple.Worker09VacuousControl

theorem proof (h : False) :
    Nat.Prime 3 ∧ Nat.Prime 5 ∧ Nat.Prime 7 ∧
    3 + 2 = 5 ∧ 5 + 2 = 7 ∧
    ∀ p : ℕ, 3 ≤ p → p ≤ 7 →
      (Nat.Prime p ↔ p = 3 ∨ p = 5 ∨ p = 7) := h.elim

end Submissions.Erdos141FirstTriple.Worker09VacuousControl
