import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Set.Card
import Mathlib.Topology.Algebra.Ring.Real

/-!
# Erdős problem 1035

Is there a fixed positive density deficit such that every graph on `2^n`
vertices above the corresponding minimum-degree threshold contains a spanning
copy of the `n`-dimensional hypercube?
-/

namespace Statements.Erdos1035DenseSpanningHypercube

def CubeAdjacent {n : ℕ} (u v : Fin n → Bool) : Prop :=
  ∃ i : Fin n, u i ≠ v i ∧
    ∀ j : Fin n, j ≠ i → u j = v j

def ContainsHypercube (n : ℕ) (G : SimpleGraph (Fin (2 ^ n))) : Prop :=
  ∃ φ : (Fin n → Bool) → Fin (2 ^ n), Function.Injective φ ∧
    ∀ u v, CubeAdjacent u v → G.Adj (φ u) (φ v)

abbrev statement : Prop :=
  ∃ c : ℝ, 0 < c ∧
    ∀ (n : ℕ) (G : SimpleGraph (Fin (2 ^ n))),
      (∀ v, (1 - c) * (2 ^ n : ℝ) < (G.neighborSet v).ncard) →
        ContainsHypercube n G

theorem target : statement := sorry

end Statements.Erdos1035DenseSpanningHypercube
