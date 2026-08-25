import Mathlib.Data.Finset.Interval
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic

namespace Statements.Erdos44SingletonCyclicLift

open Set Finset

def IsSidon {α : Type*} [AddCommMonoid α] (A : Set α) : Prop :=
  ∀ᵉ (i₁ ∈ A) (j₁ ∈ A) (i₂ ∈ A) (j₂ ∈ A),
    i₁ + i₂ = j₁ + j₂ →
      (i₁ = j₁ ∧ i₂ = j₂) ∨ (i₁ = j₂ ∧ i₂ = j₁)

def rot (n r x : ℕ) : ℕ := (x + n - r) % n

def RotSidon (n r : ℕ) (D : Finset ℕ) : Prop :=
  ∀ x ∈ D, ∀ y ∈ D, ∀ u ∈ D, ∀ v ∈ D,
    (rot n r x + rot n r y) % n = (rot n r u + rot n r v) % n →
      (x = u ∧ y = v) ∨ (x = v ∧ y = u)

def RotInjective (n r : ℕ) (D : Finset ℕ) : Prop :=
  ∀ x ∈ D, ∀ y ∈ D, rot n r x = rot n r y → x = y

/-- A cyclic Sidon set rotated to place a long following gap after `r` lifts to
a dense integer Sidon extension of the prescribed singleton `{a}`. -/
abbrev statement : Prop :=
  ∀ (N a n r : ℕ) (D : Finset ℕ), 1 ≤ a → a ≤ N → 0 < n → r < n →
    r ∈ D → RotInjective n r D → RotSidon n r D →
    (∀ x ∈ D, x ≠ r → N < a + rot n r x) →
    N < a + n - 1 →
    ∀ ε : ℝ, 0 < ε →
      (1 - ε) * Real.sqrt ((a + n - 1 : ℕ) : ℝ) ≤ D.card →
        ∃ M > N, ∃ B ⊆ Finset.Icc (N + 1) M,
          IsSidon (({a} ∪ B : Finset ℕ) : Set ℕ) ∧
            (1 - ε) * Real.sqrt M ≤ ({a} ∪ B : Finset ℕ).card

theorem target : statement := by
  sorry

end Statements.Erdos44SingletonCyclicLift
