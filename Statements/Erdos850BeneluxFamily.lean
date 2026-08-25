import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.PrimeFin

namespace Statements.Erdos850BeneluxFamily

/-- The classical infinite family satisfying the first two of the three prime-support equalities in Erdős 850. -/
abbrev statement : Prop :=
  ∀ r ≥ 1,
    let x := 2 * (2 ^ r - 1)
    let y := x * (x + 2)
    x ≠ y ∧
      x.primeFactors = y.primeFactors ∧
      (x + 1).primeFactors = (y + 1).primeFactors

theorem target : statement := sorry

end Statements.Erdos850BeneluxFamily
