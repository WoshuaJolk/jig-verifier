import Mathlib.Data.Finset.Card
import Mathlib.Order.Filter.AtTopBot.Basic

namespace Statements.Erdos181HypercubeRamseyLinear

def CubeAdj {n : ℕ} (u v : Fin n → Bool) : Prop :=
  ∃ coordinate, u coordinate ≠ v coordinate ∧
    ∀ i, i ≠ coordinate → u i = v i

def EveryColoringContainsCube (n N : ℕ) : Prop :=
  ∀ color : Fin N → Fin N → Bool,
    (∀ u v, color u v = color v u) →
      ∃ embedding : (Fin n → Bool) → Fin N,
        Function.Injective embedding ∧
          ∃ cubeColor : Bool, ∀ u v, CubeAdj u v →
            color (embedding u) (embedding v) = cubeColor

/-- Burr and Erdős's Problem 181: the two-colour Ramsey number of the
`n`-dimensional hypercube is at most a constant times its `2^n` vertices. -/
abbrev statement : Prop :=
  ∃ C : ℕ, 0 < C ∧ ∀ n, EveryColoringContainsCube n (C * 2 ^ n)

theorem target : statement := sorry

end Statements.Erdos181HypercubeRamseyLinear
