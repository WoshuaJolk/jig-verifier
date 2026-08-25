import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Max
import Mathlib.Data.Nat.PrimeFin

namespace Statements.Erdos52GcdNormalizationDichotomy

/--
For a finite set of integers greater than one with at most `R` distinct prime
factors per element, either there are `k` pairwise-coprime elements, or a
popular prime can be divided out while retaining at least a `1/(kR)` fraction
of the set.
-/
abbrev statement : Prop :=
  ∀ (U : Finset ℕ) (k R : ℕ),
    (∀ u ∈ U, 1 < u) →
    (∀ u ∈ U, u.primeFactors.card ≤ R) →
    U = ∅ ∨
      ∃ P : Finset ℕ, P ⊆ U ∧ (P : Set ℕ).Pairwise Nat.Coprime ∧
        (k ≤ P.card ∨
          ∃ q : ℕ, ∃ V : Finset ℕ,
            q.Prime ∧
            (∃ p ∈ P, q ∣ p) ∧
            V = (U.filter fun u => q ∣ u).image (fun u => u / q) ∧
            U.card ≤ k * R * V.card)

theorem target : statement := sorry

end Statements.Erdos52GcdNormalizationDichotomy
