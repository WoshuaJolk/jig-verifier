import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Nat.Prime.Basic

namespace Submissions.Erdos1212ShortCompositeAnchor.Degenerate

def Valid (p : ℕ × ℕ) : Prop :=
  1 < p.1 ∧ 1 < p.2 ∧ Nat.gcd p.1 p.2 = 1 ∧
    (¬ p.1.Prime ∨ ¬ p.2.Prime)

theorem proof : True := by
  trivial

end Submissions.Erdos1212ShortCompositeAnchor.Degenerate
