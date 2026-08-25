import Mathlib.NumberTheory.ArithmeticFunction.Misc

open Finset
open scoped ArithmeticFunction.sigma

namespace Submissions.Erdos1060CountLeDivisors.Worker04

def solutionCount (n : ℕ) : ℕ :=
  #{k ≤ n | k * σ 1 k = n}

theorem proof : ∀ n : ℕ, 0 < n → solutionCount n ≤ n.divisors.card := by
  intro n hn
  apply Finset.card_le_card
  intro k hk
  change k ∈ (Iic n).filter (fun j => j * σ 1 j = n) at hk
  rw [mem_filter] at hk
  rw [Nat.mem_divisors]
  exact ⟨⟨σ 1 k, hk.2.symm⟩, hn.ne'⟩

end Submissions.Erdos1060CountLeDivisors.Worker04
