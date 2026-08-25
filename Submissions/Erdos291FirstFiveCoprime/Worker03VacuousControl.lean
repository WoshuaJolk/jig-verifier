import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Interval
import Mathlib.Order.Interval.Finset.Nat

namespace Submissions.Erdos291FirstFiveCoprime.Worker03VacuousControl

def L (n : ℕ) : ℕ :=
  (Finset.Icc 1 n).lcm id

def a (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.Icc 1 n, L n / k

theorem proof (h : False) :
    ∀ n ∈ Finset.Icc 1 5, Nat.gcd (a n) (L n) = 1 :=
  h.elim

end Submissions.Erdos291FirstFiveCoprime.Worker03VacuousControl
