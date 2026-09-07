import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Choose.Basic

namespace Statements.Erdos1020MatchingBoundary

def Uniform {n : ℕ} (H : Finset (Finset (Fin n))) (r : ℕ) : Prop :=
  ∀ e ∈ H, e.card = r

def MatchingFree {n : ℕ} (H : Finset (Finset (Fin n))) (k : ℕ) : Prop :=
  ¬ ∃ M : Finset (Finset (Fin n)), M ⊆ H ∧ M.card = k ∧
      ∀ e ∈ M, ∀ f ∈ M, e ≠ f → Disjoint e f

abbrev statement : Prop :=
    ∀ (n r k : ℕ), 3 ≤ r → 1 ≤ k → (k ≤ 2 ∨ n < r * k) →
      ∀ H : Finset (Finset (Fin n)), Uniform H r → MatchingFree H k →
        H.card ≤ max ((r * k - 1).choose r)
          (n.choose r - (n - k + 1).choose r)

theorem target : statement := sorry

end Statements.Erdos1020MatchingBoundary
