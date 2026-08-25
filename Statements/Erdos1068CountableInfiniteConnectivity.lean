import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Combinatorics.SimpleGraph.Walk.Counting
import Mathlib.Data.Set.Card
import Mathlib.SetTheory.Cardinal.Aleph

/-!
# Erdős problem 1068

Does every graph of chromatic cardinal `ℵ₁` contain a countable induced
subgraph that is infinitely vertex-connected?
-/

open Cardinal

namespace Statements.Erdos1068CountableInfiniteConnectivity

namespace SimpleGraph

open Finset List

noncomputable def chromaticCardinal.{u} {V : Type u}
    (G : SimpleGraph V) : Cardinal :=
  sInf {κ : Cardinal |
    ∃ (C : Type u) (_ : Cardinal.mk C = κ), Nonempty (G.Coloring C)}

def InternallyDisjoint {V : Type*} {G : SimpleGraph V}
    {u v x y : V} (p : G.Walk u v) (q : G.Walk x y) : Prop :=
  Disjoint p.support.tail.dropLast q.support.tail.dropLast

def InfinitelyConnected {V : Type*} (G : SimpleGraph V) : Prop :=
  Nontrivial V ∧
    Pairwise fun u v ↦
      ∃ P : Set (G.Walk u v),
        P.Infinite ∧
          (∀ p ∈ P, p.IsPath) ∧
            P.Pairwise InternallyDisjoint

end SimpleGraph

abbrev statement : Prop :=
  ∀ (V : Type) (G : _root_.SimpleGraph V),
    SimpleGraph.chromaticCardinal G = ℵ_ 1 →
      ∃ s : Set V,
        s.Countable ∧ SimpleGraph.InfinitelyConnected (G.induce s)

theorem target : statement := sorry

end Statements.Erdos1068CountableInfiniteConnectivity
