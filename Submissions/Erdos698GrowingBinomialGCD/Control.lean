import Mathlib

namespace Submissions.Erdos698GrowingBinomialGCD.Control

theorem proof (hfalse : False) :
    ∃ h : ℕ → ℕ, Filter.Tendsto h Filter.atTop Filter.atTop ∧
      ∀ n i j : ℕ, 2 ≤ i → i < j → j ≤ n / 2 →
        h n ≤ Nat.gcd (n.choose i) (n.choose j) :=
  hfalse.elim

end Submissions.Erdos698GrowingBinomialGCD.Control
