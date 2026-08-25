import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Set.Finite.Basic

open Nat Finset

namespace Statements.Erdos939PowerfulSums

/-- `n` is `r`-powerful if every prime divisor occurs to exponent at
least `r`. -/
def IsFull (r n : ℕ) : Prop :=
  ∀ p ∈ n.primeFactors, p ^ r ∣ n

def AdmissibleSums (r : ℕ) : Set (Finset ℕ) :=
  {S | S.card = r - 2 ∧
    (∀ s ∈ S, 0 < s) ∧
    S.gcd id = 1 ∧
    IsFull r (∑ s ∈ S, s) ∧
    ∀ s ∈ S, IsFull r s}

/-- Erdős Problem 939: for every `r ≥ 4`, some `r-2` coprime
`r`-powerful numbers have an `r`-powerful sum. -/
abbrev statement : Prop :=
  ∀ r ≥ 4, (AdmissibleSums r).Nonempty

theorem target : statement := sorry

end Statements.Erdos939PowerfulSums
