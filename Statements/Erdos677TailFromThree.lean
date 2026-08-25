import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Order.Interval.Finset.Nat

namespace Statements.Erdos677TailFromThree

def lcmInterval (n k : ℕ) : ℕ :=
  (Finset.Ioc n (n + k)).lcm id

def Root : Prop :=
  ∀ m n k : ℕ, 0 < k → n + k ≤ m →
    lcmInterval m k ≠ lcmInterval n k

def LengthOneCase : Prop :=
  ∀ m n : ℕ, n + 1 ≤ m →
    lcmInterval m 1 ≠ lcmInterval n 1

def LengthTwoCase : Prop :=
  ∀ m n : ℕ, n + 2 ≤ m →
    lcmInterval m 2 ≠ lcmInterval n 2

def TailFromThree : Prop :=
  ∀ m n k : ℕ, 3 ≤ k → n + k ≤ m →
    lcmInterval m k ≠ lcmInterval n k

/-- The proved length-one and length-two cases leave exactly the tail
of interval lengths beginning at three. -/
abbrev statement : Prop :=
  LengthOneCase → LengthTwoCase → (Root ↔ TailFromThree)

theorem target : statement := sorry

end Statements.Erdos677TailFromThree
