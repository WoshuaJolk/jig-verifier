import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Choose.Basic

namespace Statements.Erdos1020MatchingConjecture

/-- Every edge of `H` has cardinality `r`. -/
def Uniform {n : ℕ} (H : Finset (Finset (Fin n))) (r : ℕ) : Prop :=
  ∀ e ∈ H, e.card = r

/-- `H` contains no matching of `k` pairwise disjoint edges. -/
def MatchingFree {n : ℕ} (H : Finset (Finset (Fin n))) (k : ℕ) : Prop :=
  ¬ ∃ M : Finset (Finset (Fin n)), M ⊆ H ∧ M.card = k ∧
      ∀ e ∈ M, ∀ f ∈ M, e ≠ f → Disjoint e f

/-- Erdős's matching conjecture, in its equivalent upper-bound form. The two
standard constructions attain the maximum on the right. -/
abbrev statement : Prop :=
  ∀ (n r k : ℕ), 3 ≤ r → 1 ≤ k →
    ∀ H : Finset (Finset (Fin n)), Uniform H r → MatchingFree H k →
      H.card ≤ max ((r * k - 1).choose r)
        (n.choose r - (n - k + 1).choose r)

theorem target : statement := sorry

end Statements.Erdos1020MatchingConjecture
