import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Nat.PrimeFin

namespace Statements.Erdos889InitialPrimeFactorLowerBound

def v (n k : ℕ) : ℕ :=
  ((n + k).primeFactors.filter fun p ↦
    ∀ i ∈ Finset.range k, ¬p ∣ n + i).card

noncomputable def v₀ (n : ℕ) : ℕ∞ :=
  ⨆ k, (v n k : ℕ∞)

/-- The offset-zero term counts every distinct prime factor of `n`, so it
always supplies this elementary lower bound for the supremum in Problem 889. -/
abbrev statement : Prop :=
  ∀ n : ℕ, v n 0 = n.primeFactors.card ∧
    (n.primeFactors.card : ℕ∞) ≤ v₀ n

theorem target : statement := sorry

end Statements.Erdos889InitialPrimeFactorLowerBound
