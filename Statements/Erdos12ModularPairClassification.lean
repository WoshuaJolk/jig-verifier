import Mathlib.Order.Interval.Finset.Nat

/-!
# Exact modular pair-exclusion classification

The recursive-anchor restriction forbids two distinct residues from being
negatives, rather than forbidding arbitrary sums inside the set.
-/

namespace Statements.Erdos12ModularPairClassification

abbrev statement : Prop :=
  ∀ (m : ℕ) (D : Finset ℕ),
    (∀ x ∈ D, 0 < x ∧ x < m) →
    (∀ x ∈ D, ∀ y ∈ D, x + y = m → x = y) →
    D.card ≤ m / 2 ∧
      (D.card = m / 2 →
        (∀ x, 0 < x → x < m →
          (x ∈ D ∨ m - x ∈ D) ∧
            (x ≠ m - x → ¬ (x ∈ D ∧ m - x ∈ D))) ∧
        (m % 2 = 0 → 0 < m → m / 2 ∈ D)) ∧
      (∀ x, 0 < x → x < m →
        x ∉ D → m - x ∉ D → D.card < m / 2)

theorem target : statement := sorry

end Statements.Erdos12ModularPairClassification
