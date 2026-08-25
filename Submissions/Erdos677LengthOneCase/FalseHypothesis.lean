import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Order.Interval.Finset.Nat

namespace Submissions.Erdos677LengthOneCase.FalseHypothesis

def lcmInterval (n k : ℕ) : ℕ :=
  (Finset.Ioc n (n + k)).lcm id

theorem proof :
    False →
      ∀ (m n : ℕ), m ≥ n + 1 → lcmInterval m 1 ≠ lcmInterval n 1 :=
  False.elim

end Submissions.Erdos677LengthOneCase.FalseHypothesis
