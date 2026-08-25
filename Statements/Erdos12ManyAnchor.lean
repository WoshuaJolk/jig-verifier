import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Nat.ModEq

/-!
# Many-anchor packing with an alignment alternative

Each positive anchor gives a canonical residue fingerprint
`min (b % a) (a - b % a)`.  Equal fingerprints with opposite signs violate
Property P.  Thus either the product fingerprint packs the tail, or two
distinct tail elements have the same residue at every anchor.
-/

namespace Statements.Erdos12ManyAnchor

abbrev statement : Prop :=
  ∀ (A : Set ℕ) (S B : Finset ℕ),
    (∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A,
      a ∣ b + c → a < b → a < c → b = c) →
    (∀ a ∈ S, a ∈ A ∧ 0 < a) →
    (∀ b ∈ B, b ∈ A ∧ ∀ a ∈ S, a < b) →
    B.card ≤ ∏ a ∈ S, (a / 2 + 1) ∨
      ∃ x ∈ B, ∃ y ∈ B, x ≠ y ∧ ∀ a ∈ S, x % a = y % a

theorem target : statement := sorry

end Statements.Erdos12ManyAnchor
