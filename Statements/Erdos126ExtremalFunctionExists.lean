import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Nat.PrimeFin
import Mathlib.Order.Lattice.Nat

namespace Statements.Erdos126ExtremalFunctionExists

open scoped BigOperators

def IsMaximalAddFactorsCard (f : ℕ → ℕ) : Prop :=
  ∀ n,
    IsGreatest
      {m | ∀ (A : Finset ℕ), A.card = n →
        m ≤ (∏ p ∈ A.offDiag, (p.1 + p.2)).primeFactors.card}
      (f n)

/-- The extremal function quantified over in Erdős problem 126 exists, so the
main conjecture's universal premise is not vacuous. -/
abbrev statement : Prop :=
  ∃ f : ℕ → ℕ, IsMaximalAddFactorsCard f

theorem target : statement := sorry

end Statements.Erdos126ExtremalFunctionExists
