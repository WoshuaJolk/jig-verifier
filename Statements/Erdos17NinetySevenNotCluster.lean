import Mathlib.Algebra.Ring.Parity
import Mathlib.Data.Nat.Prime.Defs

namespace Statements.Erdos17NinetySevenNotCluster

def IsClusterPrime (p : ℕ) : Prop :=
  p.Prime ∧ 2 < p ∧
    ∀ n : ℕ, Even n → (n : ℤ) ≤ (p : ℤ) - 3 →
      ∃ q₁ q₂ : ℕ,
        q₁.Prime ∧ q₂.Prime ∧ q₁ ≤ p ∧ q₂ ≤ p ∧
          (n : ℤ) = (q₁ : ℤ) - q₂

abbrev statement : Prop :=
  ¬IsClusterPrime 97

theorem target : statement := sorry

end Statements.Erdos17NinetySevenNotCluster
