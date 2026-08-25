import Mathlib.Algebra.Ring.Parity
import Mathlib.Data.Nat.Prime.Defs

namespace Submissions.Erdos17NinetySevenNotCluster.Control

def IsClusterPrime (p : ℕ) : Prop :=
  p.Prime ∧ 2 < p ∧
    ∀ n : ℕ, Even n → (n : ℤ) ≤ (p : ℤ) - 3 →
      ∃ q₁ q₂ : ℕ,
        q₁.Prime ∧ q₂.Prime ∧ q₁ ≤ p ∧ q₂ ≤ p ∧
          (n : ℤ) = (q₁ : ℤ) - q₂

abbrev claimedStatement : Prop := ¬IsClusterPrime 97

theorem vacuousHypothesis : False → claimedStatement := False.elim

end Submissions.Erdos17NinetySevenNotCluster.Control
