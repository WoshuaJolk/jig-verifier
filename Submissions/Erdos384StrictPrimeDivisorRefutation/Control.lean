import Mathlib

namespace Submissions.Erdos384StrictPrimeDivisorRefutation.Control

abbrev IsErdos384Exception (n k : ℕ) : Prop :=
  n = 7 ∧ (k = 3 ∨ k = 4)

theorem proof (hfalse : False) :
    ¬ (∀ n k : ℕ, 1 < k → k < n - 1 → ¬ IsErdos384Exception n k →
      ∃ p : ℕ, p.Prime ∧ p ∣ Nat.choose n k ∧ 2 * p < n) :=
  hfalse.elim

end Submissions.Erdos384StrictPrimeDivisorRefutation.Control
