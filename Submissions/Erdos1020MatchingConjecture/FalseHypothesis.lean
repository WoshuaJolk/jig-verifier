import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Choose.Basic

namespace Submissions.Erdos1020MatchingConjecture.FalseHypothesis

def Uniform {n : ℕ} (H : Finset (Finset (Fin n))) (r : ℕ) : Prop :=
  ∀ e ∈ H, e.card = r

def MatchingFree {n : ℕ} (H : Finset (Finset (Fin n))) (k : ℕ) : Prop :=
  ¬ ∃ M : Finset (Finset (Fin n)), M ⊆ H ∧ M.card = k ∧
      ∀ e ∈ M, ∀ f ∈ M, e ≠ f → Disjoint e f

theorem proof :
    False →
      ∀ (n r k : ℕ), 3 ≤ r → 1 ≤ k →
        ∀ H : Finset (Finset (Fin n)), Uniform H r → MatchingFree H k →
          H.card ≤ max ((r * k - 1).choose r)
            (n.choose r - (n - k + 1).choose r) :=
  False.elim

end Submissions.Erdos1020MatchingConjecture.FalseHypothesis
