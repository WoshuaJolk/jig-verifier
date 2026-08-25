import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Order.Interval.Finset.Nat

namespace Submissions.Erdos677TailFromThree.Kernel

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

theorem proof :
    LengthOneCase → LengthTwoCase → (Root ↔ TailFromThree) := by
  intro hOne hTwo
  constructor
  · intro hRoot m n k hk hdisjoint
    exact hRoot m n k (by omega) hdisjoint
  · intro hTail m n k hk hdisjoint
    by_cases hk1 : k = 1
    · subst k
      exact hOne m n hdisjoint
    by_cases hk2 : k = 2
    · subst k
      exact hTwo m n hdisjoint
    exact hTail m n k (by omega) hdisjoint

end Submissions.Erdos677TailFromThree.Kernel
