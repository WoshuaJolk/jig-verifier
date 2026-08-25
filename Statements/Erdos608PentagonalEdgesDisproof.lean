import Mathlib

namespace Statements.Erdos608PentagonalEdgesDisproof

/-- An edge lies on a five-cycle with five pairwise-distinct vertices. -/
def OnC5 {V : Type*} (G : SimpleGraph V) (e : Sym2 V) : Prop :=
  ∃ a b c d f : V,
    a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ a ≠ f ∧ b ≠ c ∧ b ≠ d ∧ b ≠ f ∧ c ≠ d ∧ c ≠ f ∧
    d ≠ f ∧
    G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d f ∧ G.Adj f a ∧
    (e = s(a, b) ∨ e = s(b, c) ∨ e = s(c, d) ∨ e = s(d, f) ∨ e = s(f, a))

/-- Edges of `G` that occur in a five-cycle. -/
def pentEdges {V : Type*} (G : SimpleGraph V) : Set (Sym2 V) :=
  {e ∈ G.edgeSet | OnC5 G e}

/-- Intended asymptotic form of Erdős 608: eventually every graph above the
Turán threshold has at least `(2/9)n²` pentagonal edges. -/
def Conjecture : Prop :=
  ∃ n₀ : ℕ, ∀ n, n₀ ≤ n → ∀ G : SimpleGraph (Fin n),
    n ^ 2 < 4 * G.edgeSet.ncard → 2 * n ^ 2 ≤ 9 * (pentEdges G).ncard

/-- The Füredi–Maleki construction disproves the asymptotic conjecture. -/
abbrev statement : Prop := ¬ Conjecture

theorem target : statement := by
  sorry

end Statements.Erdos608PentagonalEdgesDisproof
