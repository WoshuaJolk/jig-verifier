import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Prime.Basic

namespace Statements.Erdos32PrimeAdditiveComplement

open Filter Set Asymptotics
open scoped Classical

/-- Every sufficiently large natural is a prime plus an element of `A`. -/
def IsAdditiveComplementToPrimes (A : Set ℕ) : Prop :=
  ∀ᶠ n in atTop, ∃ p, p.Prime ∧ ∃ a ∈ A, n = p + a

/-- Erdős problem 32: an additive complement to the primes of
little-oh-log-squared counting growth. -/
abbrev statement : Prop :=
  ∃ A : Set ℕ,
    IsAdditiveComplementToPrimes A ∧
    (fun N => (((Finset.Icc 1 N).filter (· ∈ A)).card : ℝ)) =o[atTop]
      fun N => (Real.log N) ^ 2

theorem target : statement := sorry

end Statements.Erdos32PrimeAdditiveComplement
