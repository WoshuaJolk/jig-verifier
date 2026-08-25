import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Combinatorics.SimpleGraph.Walk.Counting

namespace Statements.Erdos1068InfiniteImpliesConnected

namespace SimpleGraph

open Finset List

def InternallyDisjoint {V : Type*} {G : _root_.SimpleGraph V}
    {u v x y : V} (p : G.Walk u v) (q : G.Walk x y) : Prop :=
  Disjoint p.support.tail.dropLast q.support.tail.dropLast

def InfinitelyConnected {V : Type*} (G : _root_.SimpleGraph V) : Prop :=
  Nontrivial V ∧
    Pairwise fun u v ↦
      ∃ P : Set (G.Walk u v),
        P.Infinite ∧
          (∀ p ∈ P, p.IsPath) ∧
            P.Pairwise InternallyDisjoint

end SimpleGraph

abbrev statement : Prop :=
  ∀ (V : Type*) (G : _root_.SimpleGraph V),
    SimpleGraph.InfinitelyConnected G → G.Connected

theorem target : statement := sorry

end Statements.Erdos1068InfiniteImpliesConnected
