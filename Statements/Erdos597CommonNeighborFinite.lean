import Mathlib.Combinatorics.SimpleGraph.Copy
import Mathlib.Data.Set.Card
import Mathlib.SetTheory.Cardinal.Aleph

open Cardinal

namespace Statements.Erdos597CommonNeighborFinite

def HasCountableBiclique {V : Type} (G : SimpleGraph V) : Prop :=
  ∃ L R : Set V,
    Disjoint L R ∧ #L = ℵ₀ ∧ #R = ℵ₀ ∧
      ∀ l ∈ L, ∀ r ∈ R, G.Adj l r

def CommonNeighbors {V : Type} (G : SimpleGraph V) (L : Set V) : Set V :=
  {v | ∀ l ∈ L, G.Adj l v}

/-- Excluding a countably infinite biclique forces every countably infinite
vertex set to have only finitely many common neighbors. -/
abbrev statement : Prop :=
  ∀ (V : Type) (G : SimpleGraph V),
    ¬HasCountableBiclique G →
    ∀ L : Set V, #L = ℵ₀ →
      #(CommonNeighbors G L) < ℵ₀

theorem target : statement := sorry

end Statements.Erdos597CommonNeighborFinite
