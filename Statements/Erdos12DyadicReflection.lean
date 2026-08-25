import Mathlib.Order.Interval.Finset.Nat

/-!
# A finite dyadic-shell bound for Property P sets

Reflecting `b` in the first multiplicative shell `(a, 2a)` across `3a/2`
gives `3a-b`.  Property P prevents a set from containing both points of any
nontrivial reflected pair, which bounds the shell occupancy by `⌊a/2⌋`.
-/

namespace Statements.Erdos12DyadicReflection

abbrev statement : Prop :=
  ∀ (A : Set ℕ) (B : Finset ℕ),
    (∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A,
      a ∣ b + c → a < b → a < c → b = c) →
    ∀ a ∈ A,
      (∀ b ∈ B, b ∈ A ∧ a < b ∧ b < 2 * a) →
      B.card ≤ a / 2

theorem target : statement := sorry

end Statements.Erdos12DyadicReflection
