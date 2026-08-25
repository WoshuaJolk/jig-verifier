import Mathlib.Algebra.Squarefree.Basic
import Mathlib.RingTheory.Polynomial.Content

namespace Statements.Erdos978PolynomialPowerfreeValues

open Polynomial Set

def Powerfree {M : Type*} [Monoid M] (k : ℕ) (m : M) : Prop :=
  ∀ ⦃x : M⦄, x ^ k ∣ m → IsUnit x

/-- Erdős problem 978(ii): under the necessary absence of a fixed
`(degree-2)`-th-power prime divisor, an irreducible polynomial of non-power-of-two
degree greater than three takes infinitely many `(degree-2)`-power-free values. -/
abbrev statement : Prop :=
  ∀ {f : ℤ[X]}, Irreducible f → f.natDegree > 3 →
    (¬ ∃ l : ℕ, f.natDegree = 2 ^ l) →
    0 < f.leadingCoeff →
    (∀ p : ℕ, p.Prime →
      ∃ n : ℕ, ¬ (p : ℤ) ^ (f.natDegree - 2) ∣ f.eval (n : ℤ)) →
    {n : ℕ | Powerfree (f.natDegree - 2) (f.eval (n : ℤ))}.Infinite

theorem target : statement := sorry

end Statements.Erdos978PolynomialPowerfreeValues
