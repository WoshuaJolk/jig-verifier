import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Finset.BooleanAlgebra
import Mathlib.Order.Filter.AtTopBot.CountablyGenerated

namespace Statements.Erdos1075DenseHypergraphSubgraph

open Filter

def Uniform {V : Type} [DecidableEq V]
    (r : ℕ) (F : Finset (Finset V)) : Prop :=
  ∀ A ∈ F, A.card = r

def InducedEdgeCount {V : Type} [DecidableEq V]
    (F : Finset (Finset V)) (S : Finset V) : ℕ :=
  (F.filter fun A => A ⊆ S).card

/-- Erdős Problem 1075, with `m(n) → ∞` expressed uniformly: every fixed
lower target K is eventually met by the dense subgraph. -/
abbrev statement : Prop :=
  ∀ r : ℕ, 3 ≤ r →
    ∃ c : ℝ, 1 / (r : ℝ) ^ r < c ∧
      ∀ ε : ℝ, 0 < ε → ∀ K : ℕ,
        ∀ᶠ n : ℕ in atTop,
          ∀ F : Finset (Finset (Fin n)),
            Uniform r F →
            (1 + ε) * ((n : ℝ) / (r : ℝ)) ^ r ≤ (F.card : ℝ) →
            ∃ S : Finset (Fin n), K ≤ S.card ∧
              c * (S.card : ℝ) ^ r ≤
                (InducedEdgeCount F S : ℝ)

theorem target : statement := sorry

end Statements.Erdos1075DenseHypergraphSubgraph
