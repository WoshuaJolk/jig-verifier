import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Nat.GCD.BigOperators
import Mathlib.Data.Nat.Dist

open scoped BigOperators

namespace Statements.Erdos1MultiModulusLargeSieve

/-- A finite pairwise-coprime large-sieve bound. If every modulus is at least
`Q` and `R < Q^(L+1)`, at most `L` moduli can divide any nonzero difference
bounded by `R`; consequently the sum of modular collision counts has an exact
diagonal term and an `L`-fold off-diagonal term. -/
abbrev statement : Prop :=
  ∀ (P : Finset ℕ) (Q L R : ℕ),
    (P : Set ℕ).Pairwise Nat.Coprime →
    (∀ q ∈ P, Q ≤ q) →
    0 < Q →
    R < Q ^ (L + 1) →
    (∀ d : ℕ, 0 < d → d ≤ R →
      ((P.filter fun q => q ∣ d).prod id ∣ d) ∧
      (P.filter fun q => q ∣ d).card ≤ L) ∧
    ∀ (α : Type) [DecidableEq α] (B : Finset α) (f : α → ℕ),
      Set.InjOn f B →
      (∀ x ∈ B, f x ≤ R) →
      ∑ q ∈ P,
          ((B.product B).filter fun p => f p.1 % q = f p.2 % q).card ≤
        P.card * B.card + L * (B.card * (B.card - 1))

theorem target : statement := sorry

end Statements.Erdos1MultiModulusLargeSieve
