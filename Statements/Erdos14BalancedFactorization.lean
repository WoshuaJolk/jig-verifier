import Mathlib.Data.Finset.Interval
import Mathlib.Data.Finset.Prod
import Mathlib.Order.Interval.Finset.Nat

namespace Statements.Erdos14BalancedFactorization

def pairFiber (X Y : Finset ℕ) (n : ℕ) : Finset (ℕ × ℕ) :=
  (X ×ˢ Y).filter fun p => p.1 + p.2 = n

def balancedTiles (M : ℕ) (X Y : Finset ℕ) : Prop :=
  X ⊆ Finset.Icc 0 M ∧
  Y ⊆ Finset.Icc 0 (M - 1) ∧
  M ∈ X ∧
  M - 1 ∈ Y ∧
  ∀ n ∈ Finset.range (2 * M), (pairFiber X Y n).card = 1

/-- The exact balanced direct factorization of an interval is rigid. -/
abbrev statement : Prop :=
  ∀ (M : ℕ) (X Y : Finset ℕ), 1 ≤ M →
    balancedTiles M X Y →
    X = {0, M} ∧ Y = Finset.range M

theorem target : statement := sorry

end Statements.Erdos14BalancedFactorization
