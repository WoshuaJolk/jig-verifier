import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Choose.Basic

namespace Statements.Erdos1020MatchingRankThree

def Uniform {n : ℕ} (H : Finset (Finset (Fin n))) (r : ℕ) : Prop :=
  ∀ E ∈ H, E.card = r

def MatchingFree {n : ℕ} (H : Finset (Finset (Fin n))) (k : ℕ) : Prop :=
  ¬ ∃ M : Finset (Finset (Fin n)), M ⊆ H ∧ M.card = k ∧
      ∀ E ∈ M, ∀ F ∈ M, E ≠ F → Disjoint E F

/-- The original maximum in rank three, for every ambient size and k≥44.
This auxiliary statement does not replace the unrestricted root. -/
abbrev statement : Prop :=
  ∀ (n r k : ℕ), 3 ≤ r → 1 ≤ k → r = 3 → 44 ≤ k →
    ∀ H : Finset (Finset (Fin n)), Uniform H r → MatchingFree H k →
      H.card ≤ max ((r * k - 1).choose r)
        (n.choose r - (n - k + 1).choose r)

theorem target : statement := sorry

end Statements.Erdos1020MatchingRankThree
