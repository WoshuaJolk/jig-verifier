import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Combinatorics.SimpleGraph.Walk.Counting

namespace Submissions.Erdos1068InfiniteImpliesConnected.ExtractWalk

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

theorem proof :
    ∀ (V : Type*) (G : _root_.SimpleGraph V),
      SimpleGraph.InfinitelyConnected G → G.Connected := by
  intro V G hG
  letI : Nonempty V := hG.1.to_nonempty
  constructor
  intro u v
  by_cases huv : u = v
  · subst v
    exact _root_.SimpleGraph.Reachable.refl u
  · obtain ⟨P, hP, -, -⟩ := hG.2 huv
    obtain ⟨p, hp⟩ := hP.nonempty
    exact ⟨p⟩

end Submissions.Erdos1068InfiniteImpliesConnected.ExtractWalk
