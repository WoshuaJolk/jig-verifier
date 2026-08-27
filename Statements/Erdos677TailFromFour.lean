import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Order.Interval.Finset.Nat

namespace Statements.Erdos677TailFromFour

/-- Least common multiple of `{n+1, ..., n+k}`, as in Erdős problem 677. -/
def lcmInterval (n k : ℕ) : ℕ :=
  (Finset.Ioc n (n + k)).lcm id

def Root : Prop :=
  ∀ m n k : ℕ, 0 < k → n + k ≤ m → lcmInterval m k ≠ lcmInterval n k

def LengthOneCase : Prop :=
  ∀ m n : ℕ, n + 1 ≤ m → lcmInterval m 1 ≠ lcmInterval n 1

def LengthTwoCase : Prop :=
  ∀ m n : ℕ, n + 2 ≤ m → lcmInterval m 2 ≠ lcmInterval n 2

def LengthThreeCase : Prop :=
  ∀ m n : ℕ, n + 3 ≤ m → lcmInterval m 3 ≠ lcmInterval n 3

def TailFromFour : Prop :=
  ∀ m n k : ℕ, 4 ≤ k → n + k ≤ m → lcmInterval m k ≠ lcmInterval n k

/-- With lengths one, two and three settled, the whole of Erdős 677 is exactly
the tail of interval lengths beginning at four. -/
abbrev statement : Prop :=
  LengthOneCase → LengthTwoCase → LengthThreeCase → (Root ↔ TailFromFour)

theorem target : statement := sorry

end Statements.Erdos677TailFromFour
