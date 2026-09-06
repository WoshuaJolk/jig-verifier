import Mathlib.Tactic
namespace Statements.E287HighSmooth
abbrev statement : Prop :=
  ∀ (A : Finset ℕ) (N M B : ℕ),
    0 < B → 2 ≤ N → 8 * B^2 ≤ N →
    (∀ a ∈ A, N ≤ a) → (∀ a ∈ A, a ≤ M) →
    (∀ x, N ≤ x → x + 1 ≤ M → x ∈ A ∨ x + 1 ∈ A) →
    (∀ a ∈ A, ∀ p : ℕ, p.Prime → p ∣ a → p ≤ B) →
    ∑ a ∈ A, (1 : ℚ) / a ≠ 1
end Statements.E287HighSmooth
