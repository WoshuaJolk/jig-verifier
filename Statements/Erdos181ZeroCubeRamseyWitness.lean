import Mathlib.Data.Fin.Basic

namespace Statements.Erdos181ZeroCubeRamseyWitness

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

/-- The zero-dimensional cube embeds monochromatically in a one-vertex host. -/
abbrev statement : Prop :=
  EveryColoringContainsCube 0 1

theorem target : statement := sorry

end Statements.Erdos181ZeroCubeRamseyWitness
