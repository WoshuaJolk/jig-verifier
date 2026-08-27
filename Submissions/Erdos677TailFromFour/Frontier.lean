import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic

/-!
# The frontier of Erdős 677 after the length-three case

Lengths one, two and three are settled, so the root is equivalent to the tail
`k ≥ 4`.  Both directions are bookkeeping: forward because `4 ≤ k` implies
`0 < k`, backward by splitting `0 < k` into `k = 1, 2, 3` and `4 ≤ k`.
-/

namespace Submissions.Erdos677TailFromFour.Frontier

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

theorem proof :
    LengthOneCase → LengthTwoCase → LengthThreeCase → (Root ↔ TailFromFour) := by
  intro h1 h2 h3
  constructor
  · intro hR m n k hk hnm
    exact hR m n k (by omega) hnm
  · intro hT m n k hk hnm
    match k, hk with
    | 1, _ => exact h1 m n hnm
    | 2, _ => exact h2 m n hnm
    | 3, _ => exact h3 m n hnm
    | (k+4), _ => exact hT m n (k+4) (by omega) hnm

end Submissions.Erdos677TailFromFour.Frontier
