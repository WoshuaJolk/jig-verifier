import Mathlib.Combinatorics.SimpleGraph.Clique

namespace Statements.Erdos151UniversalTransversal

open SimpleGraph

def CliqueTransversal {V : Type} [DecidableEq V]
    (G : SimpleGraph V) (T : Finset V) : Prop :=
  ∀ K : Finset V, 2 ≤ K.card →
    Maximal G.IsClique (K : Set V) →
      ∃ v ∈ K, v ∈ T

abbrev statement : Prop :=
  ∀ n : ℕ, ∀ G : SimpleGraph (Fin n),
    CliqueTransversal G Finset.univ

theorem target : statement := sorry

end Statements.Erdos151UniversalTransversal
