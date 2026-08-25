import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Data.Real.Basic

/-!
# Reciprocal-mass bound below the common-lcm spacing

The aligned branch of the many-anchor fingerprint dichotomy consists of pairs
congruent modulo every anchor, so their difference is a multiple of the
anchors' least common multiple.  An interval shorter than that spacing contains
no aligned pair.
-/

namespace Statements.Erdos12LcmMass

abbrev statement : Prop :=
  ∀ (A : Set ℕ) (S B : Finset ℕ) (d : ℕ),
    (∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A,
      a ∣ b + c → a < b → a < c → b = c) →
    (∀ a ∈ S, a ∈ A ∧ 0 < a) →
    0 < d →
    (∀ b ∈ B,
      b ∈ A ∧ (∀ a ∈ S, a < b) ∧
        d < b ∧ b < d + S.lcm id) →
    (∑ b ∈ B, (1 : ℝ) / (b : ℝ)) ≤
      ((∏ a ∈ S, (a / 2 + 1) : ℕ) : ℝ) / (d : ℝ)

theorem target : statement := sorry

end Statements.Erdos12LcmMass
