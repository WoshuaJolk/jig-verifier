import Mathlib.Algebra.GCDMonoid.Nat

/-!
# Recursive anchors give complete-fiber exclusions
-/

namespace Statements.Erdos12CompleteFiberCoverage

abbrev statement : Prop :=
  ∀ (A : Set ℕ) (L r q s t : ℕ),
    (∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A,
      a ∣ b + c → a < b → a < c → b = c) →
    0 < L →
    r + L * q ∈ A →
    r + L * s ∈ A →
    r + L * t ∈ A →
    q < s →
    q < t →
    (r + L * q) / Nat.gcd L r ∣ (s - q) + (t - q) →
    s = t

theorem target : statement := sorry

end Statements.Erdos12CompleteFiberCoverage
