import Mathlib.Combinatorics.SimpleGraph.Clique

namespace Statements.Erdos151CliqueTransversal

open SimpleGraph

def CliqueTransversal {V : Type} [DecidableEq V]
    (G : SimpleGraph V) (T : Finset V) : Prop :=
  ∀ K : Finset V, 2 ≤ K.card →
    Maximal G.IsClique (K : Set V) →
      ∃ v ∈ K, v ∈ T

def GuaranteesTriangleFreeIndependentSet (n h : ℕ) : Prop :=
  ∀ G : SimpleGraph (Fin n), G.CliqueFree 3 →
    ∃ S : Finset (Fin n), h ≤ S.card ∧ G.IsIndepSet (S : Set (Fin n))

/-- Erdős Problem 151, with H(n) expanded rather than defined by a
finite maximum: every universally guaranteed triangle-free independent-set
size gives the corresponding clique-transversal upper bound. -/
abbrev statement : Prop :=
  ∀ n : ℕ, ∀ G : SimpleGraph (Fin n),
    ∃ T : Finset (Fin n), CliqueTransversal G T ∧
      ∀ h : ℕ, GuaranteesTriangleFreeIndependentSet n h →
        T.card ≤ n - h

theorem target : statement := sorry

end Statements.Erdos151CliqueTransversal
