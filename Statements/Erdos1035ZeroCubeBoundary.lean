import Mathlib.Combinatorics.SimpleGraph.Finite

namespace Statements.Erdos1035ZeroCubeBoundary

def CubeAdjacent {n : ℕ} (u v : Fin n → Bool) : Prop :=
  ∃ i : Fin n, u i ≠ v i ∧
    ∀ j : Fin n, j ≠ i → u j = v j

def ContainsHypercube (n : ℕ) (G : SimpleGraph (Fin (2 ^ n))) : Prop :=
  ∃ φ : (Fin n → Bool) → Fin (2 ^ n), Function.Injective φ ∧
    ∀ u v, CubeAdjacent u v → G.Adj (φ u) (φ v)

abbrev statement : Prop :=
  ∀ G : SimpleGraph (Fin (2 ^ 0)), ContainsHypercube 0 G

theorem target : statement := sorry

end Statements.Erdos1035ZeroCubeBoundary
