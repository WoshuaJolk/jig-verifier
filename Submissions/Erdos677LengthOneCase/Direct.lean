import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Order.Interval.Finset.Nat

namespace Submissions.Erdos677LengthOneCase.Direct

def lcmInterval (n k : ℕ) : ℕ :=
  (Finset.Ioc n (n + k)).lcm id

theorem proof :
    ∀ (m n : ℕ), m ≥ n + 1 → lcmInterval m 1 ≠ lcmInterval n 1 := by
  intro m n hmn
  have hioc (a : ℕ) : Finset.Ioc a (a + 1) = {a + 1} := by
    ext x
    simp
  have hne : m + 1 ≠ n + 1 := by omega
  simpa [lcmInterval, hioc] using hne

end Submissions.Erdos677LengthOneCase.Direct
