import Mathlib.Algebra.Group.Pointwise.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.PrimeFin

/- The integer sum-product exponent restricted to elements whose absolute
values have at most two distinct prime factors. The support primes may vary
with the element. This is not the unrestricted integer conjecture. -/
namespace Statements.Erdos52OmegaTwo

open scoped Pointwise

def statement : Prop :=
  ∀ ε : ℝ, 0 < ε → ε < 1 → ∃ C : ℝ, 0 < C ∧ ∀ A : Finset ℤ,
    (∀ a ∈ A, a.natAbs.primeFactors.card ≤ 2) →
    (max (A + A).card (A * A).card : ℝ) ≥ C * (A.card : ℝ) ^ (2 - ε)

end Statements.Erdos52OmegaTwo
