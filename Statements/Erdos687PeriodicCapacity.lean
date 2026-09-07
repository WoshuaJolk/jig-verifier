import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Finset.Prod
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset

namespace Statements.Erdos687PeriodicCapacity

open scoped BigOperators

noncomputable def survivors (L z : ℕ) (residue : ℕ → ℕ) : Finset ℕ := by
  classical
  exact (Finset.range (L + 1)).filter (fun m => 0 < m ∧
    ∀ p ∈ (Finset.range (z + 1)).filter Nat.Prime, m % p ≠ residue p % p)

def tailPrimes (X z : ℕ) : Finset ℕ :=
  (Finset.range (X + 1)).filter (fun p => p.Prime ∧ z < p)

/-- Finite loss from adding prime residue classes; no asymptotic lower bound is asserted. -/
abbrev statement : Prop :=
  ∀ (X L z M : ℕ) (A : Finset ℕ) (residue : ℕ → ℕ),
    (∀ p ∈ tailPrimes X z, M.Coprime p) →
    (∀ m ∈ survivors L z residue, m % M ∈ A) →
    (survivors L z residue).card ≤ (survivors L X residue).card +
      A.card * ∑ p ∈ tailPrimes X z, (L / (M * p) + 1)

theorem target : statement := sorry

end Statements.Erdos687PeriodicCapacity
