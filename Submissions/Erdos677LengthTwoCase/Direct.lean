import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.Linarith

namespace Submissions.Erdos677LengthTwoCase.Direct

def lcmInterval (n k : ℕ) : ℕ :=
  (Finset.Ioc n (n + k)).lcm id

lemma interval_two (n : ℕ) :
    Finset.Ioc n (n + 2) = {n + 1, n + 2} := by
  ext x
  simp
  omega

lemma coprime_consecutive (n : ℕ) : Nat.Coprime (n + 1) (n + 2) := by
  rw [show n + 2 = 1 + (n + 1) by omega]
  simpa [Nat.coprime_add_self_right]

lemma lcmInterval_two (n : ℕ) :
    lcmInterval n 2 = (n + 1) * (n + 2) := by
  rw [lcmInterval, interval_two]
  simp
  exact (coprime_consecutive n).lcm_eq_mul

theorem proof :
    ∀ (m n : ℕ), m ≥ n + 2 →
      lcmInterval m 2 ≠ lcmInterval n 2 := by
  intro m n hmn
  rw [lcmInterval_two, lcmInterval_two]
  nlinarith

end Submissions.Erdos677LengthTwoCase.Direct
