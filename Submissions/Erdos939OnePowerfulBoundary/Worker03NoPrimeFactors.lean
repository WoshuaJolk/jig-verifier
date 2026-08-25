import Mathlib.Data.Nat.Factorization.Basic

open Nat

namespace Submissions.Erdos939OnePowerfulBoundary.Worker03NoPrimeFactors

def IsFull (r n : ℕ) : Prop :=
  ∀ p ∈ n.primeFactors, p ^ r ∣ n

theorem proof : ∀ r : ℕ, IsFull r 1 := by
  intro r p hp
  simp at hp

end Submissions.Erdos939OnePowerfulBoundary.Worker03NoPrimeFactors
