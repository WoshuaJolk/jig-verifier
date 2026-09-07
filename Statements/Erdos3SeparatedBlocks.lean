import Init

namespace Statements.Erdos3SeparatedBlocks

/-- A geometric component of the known extremal-density/harmonic-mass reduction.
This asserts only preservation of k-AP-freeness, not infinite size or divergent mass. -/
abbrev statement : Prop :=
  ∀ (k : Nat), 3 ≤ k → ∀ (E : Nat → Nat → Prop),
    (∀ j x, E j x → 1 ≤ x ∧ x ≤ 4 ^ j) →
    (∀ j a d, 0 < d → ¬ (∀ n, n < k → E j (a + n * d))) →
    ∀ a d, 0 < d → ¬ (∀ n, n < k →
      ∃ j x, E j x ∧ a + n * d = 4 * 4 ^ j + x)

theorem target : statement := sorry

end Statements.Erdos3SeparatedBlocks
