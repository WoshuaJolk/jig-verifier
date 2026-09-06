import Mathlib.Tactic
open Finset
namespace Statements.Erdos30ThreeSmoothingLosses
noncomputable def differences (A : Finset ℤ) : Finset ℤ :=
  A.offDiag.image (fun p => p.1 - p.2)
noncomputable def missingPairs (A B : Finset ℤ) : Finset (ℤ × ℤ) :=
  B.offDiag.filter (fun p => p.2 - p.1 ∉ differences A)
noncomputable def missingEnergy (A B : Finset ℤ) (K : ℤ → ℝ) : ℝ :=
  ∑ p ∈ missingPairs A B, K p.1 * K p.2

abbrev statement : Prop :=
  ∀ (R : ℕ) (A J B : Finset ℤ) (K Q : Fin R → ℤ → ℝ)
    (lam : Fin R → ℝ) (q : ℝ),
    (∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, ∀ d ∈ A,
      a + b = c + d → (a = c ∧ b = d) ∨ (a = d ∧ b = c)) →
    (∀ r s, 0 ≤ K r s) →
    (∀ r s, s ∉ B → K r s = 0) →
    (∀ r, ∑ s ∈ B, K r s = 1) →
    (∀ r, 0 ≤ lam r) → (∑ r, lam r = 1) →
    0 < q → (∑ r, lam r * ∑ n ∈ J, Q r n ^ 2 = q) →
    (∀ x ∈ A, 1 ≤ ∑ r, lam r * ∑ n ∈ J, Q r n * K r (n - x)) →
    let k : ℝ := A.card
    let u : Fin R → ℤ → ℝ := fun r n => ∑ x ∈ A, K r (n - x)
    let D := ∑ r, lam r * missingEnergy A B (K r)
    let V := ∑ r, lam r * ∑ n ∈ J, (u r n - (k / q) * Q r n) ^ 2
    let C := (∑ r, lam r * ∑ n ∈ J, Q r n * u r n) - k
    0 ≤ D ∧ 0 ≤ V ∧ 0 ≤ C ∧
      k ^ 2 + q * (D + V) + 2 * k * C ≤
        q * (1 + (k - 1) * ∑ r, lam r * ∑ s ∈ B, K r s ^ 2)
theorem target : statement := sorry
end Statements.Erdos30ThreeSmoothingLosses
