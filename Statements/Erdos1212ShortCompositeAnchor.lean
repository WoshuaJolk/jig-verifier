import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Nat.Prime.Basic

/-!
# A composite-anchor reduction for Erdős problem 1212

A short interval immediately above a composite anchor consists entirely of
admissible visible vertices when it ends before the anchor plus every prime
factor of the anchor.
-/

namespace Statements.Erdos1212ShortCompositeAnchor

def Valid (p : ℕ × ℕ) : Prop :=
  1 < p.1 ∧ 1 < p.2 ∧ Nat.gcd p.1 p.2 = 1 ∧
    (¬ p.1.Prime ∨ ¬ p.2.Prime)

abbrev statement : Prop :=
  ∀ {a b c : ℕ},
    (1 < a ∧ ¬ a.Prime) →
      a < b →
        (∀ p, p.Prime → p ∣ a → c < a + p) →
          ∀ s, b ≤ s → s ≤ c → Valid (a, s)

theorem target : statement := sorry

end Statements.Erdos1212ShortCompositeAnchor
