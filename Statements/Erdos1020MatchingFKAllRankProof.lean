import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Choose.Basic

namespace Statements.Erdos1020MatchingFKAllRankProof

def Uniform {n : ℕ} (H : Finset (Finset (Fin n))) (r : ℕ) : Prop :=
  ∀ e ∈ H, e.card = r

def MatchingFree {n : ℕ} (H : Finset (Finset (Fin n))) (k : ℕ) : Prop :=
  ¬ ∃ M : Finset (Finset (Fin n)), M ⊆ H ∧ M.card = k ∧
      ∀ e ∈ M, ∀ f ∈ M, e ≠ f → Disjoint e f

/-- The original maximum in an explicit large-matching, all-rank range.
This auxiliary statement does not replace the unrestricted root. -/
abbrev statement : Prop :=
  ∀ (n r k : ℕ), 3 ≤ r → 1 ≤ k → 1000 * r ≤ k - 1 →
    6 * (k - 1) + 11 * (r - 1) * (k - 1) ≤ 6 * n →
    ∀ H : Finset (Finset (Fin n)), Uniform H r → MatchingFree H k →
      H.card ≤ max ((r * k - 1).choose r)
        (n.choose r - (n - k + 1).choose r)

theorem target : statement := sorry

end Statements.Erdos1020MatchingFKAllRankProof
