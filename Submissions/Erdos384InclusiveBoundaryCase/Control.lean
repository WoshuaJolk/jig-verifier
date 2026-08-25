import Mathlib

namespace Submissions.Erdos384InclusiveBoundaryCase.Control

theorem proof (hfalse : False) :
    ∃ p : ℕ, p.Prime ∧ p ∣ Nat.choose 4 2 ∧ 2 * p ≤ 4 :=
  hfalse.elim

end Submissions.Erdos384InclusiveBoundaryCase.Control
