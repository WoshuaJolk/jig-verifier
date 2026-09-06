import Mathlib.Tactic
namespace Statements.Erdos30SidonFiberBudget
def IsSidon (A : Finset ℕ) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, ∀ d ∈ A,
    a + b = c + d → (a = c ∧ b = d) ∨ (a = d ∧ b = c)

abbrev statement : Prop :=
  ∀ (A : Finset ℕ) (M L : ℕ), 0 < M → IsSidon A →
  (∀ a ∈ A, a < L * M) →
  A.card ≤ (A.image (fun a => a % M)).card + (L - 1)
theorem target : statement := sorry
end Statements.Erdos30SidonFiberBudget
