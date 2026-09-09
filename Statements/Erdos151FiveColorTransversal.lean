import Mathlib.Combinatorics.SimpleGraph.Clique

namespace Statements.Erdos151FiveColorTransversal

open SimpleGraph

def CliqueTransversal {V : Type} [DecidableEq V]
    (G : SimpleGraph V) (T : Finset V) : Prop :=
  ∀ K : Finset V, 2 ≤ K.card →
    Maximal G.IsClique (K : Set V) →
      ∃ v ∈ K, v ∈ T

def GuaranteesTriangleFreeIndependentSet (n h : ℕ) : Prop :=
  ∀ G : SimpleGraph (Fin n), G.CliqueFree 3 →
    ∃ S : Finset (Fin n), h ≤ S.card ∧ G.IsIndepSet (S : Set (Fin n))

/-- The Erdős151 bound for every finite graph admitting a proper five-coloring.
Singleton maximal cliques are excluded, and one transversal works for all h. -/
abbrev statement : Prop :=
  ∀ n : ℕ, ∀ G : SimpleGraph (Fin n),
    (∃ c : Fin n → Fin 5, ∀ u v, G.Adj u v → c u ≠ c v) →
    ∃ T : Finset (Fin n), CliqueTransversal G T ∧
      ∀ h : ℕ, GuaranteesTriangleFreeIndependentSet n h →
        T.card ≤ n - h

end Statements.Erdos151FiveColorTransversal
