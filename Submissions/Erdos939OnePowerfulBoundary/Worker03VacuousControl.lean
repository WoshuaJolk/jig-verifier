import Mathlib.Data.Nat.Factorization.Basic

open Nat

namespace Submissions.Erdos939OnePowerfulBoundary.Worker03VacuousControl

def IsFull (r n : ℕ) : Prop :=
  ∀ p ∈ n.primeFactors, p ^ r ∣ n

theorem proof (h : False) : ∀ r : ℕ, IsFull r 1 := h.elim

end Submissions.Erdos939OnePowerfulBoundary.Worker03VacuousControl
