import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Combinatorics.SimpleGraph.Finite

namespace Statements.J4P399HamiltonianExchange
namespace HamiltonianExchangeTrap
open SimpleGraph

abbrev V := Fin 18
def matching : List (Nat × Nat) :=
  [(0,4),(1,10),(2,7),(3,11),(6,16),(5,14),(8,13),(9,15),(12,17)]
def chord (i : Fin 9) := matching.getD i.val (0,0)
def edges : List (V × V) :=
  [(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),
   (9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(16,17),(17,0),
   (0,4),(1,10),(2,7),(3,11),(6,16),(5,14),(8,13),(9,15),(12,17)]
def G : SimpleGraph V := SimpleGraph.fromRel (fun u v => (u,v) ∈ edges)
instance : DecidableRel G.Adj :=
  inferInstanceAs (DecidableRel (SimpleGraph.fromRel (fun u v => (u,v) ∈ edges)).Adj)

def orderB : List V := [0,4,5,6,7,8,9,10,1,2,3,11,12,13,14,15,16,17]
def mateA : List V := [4,10,7,11,0,14,16,2,13,15,1,3,17,8,5,9,6,12]
def prevA : List V := [17,0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16]
def nextA : List V := [1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,0]
def mateB : List V := [1,0,7,4,3,14,16,2,13,15,11,10,17,8,5,9,6,12]
def prevB : List V := [17,10,1,2,0,4,5,6,7,8,9,3,11,12,13,14,15,16]
def nextB : List V := [4,2,3,11,5,6,7,8,9,10,1,12,13,14,15,16,17,0]

def mate (s : Bool) (v : V) : V := (if s then mateB else mateA).getD v.val 0
def hop (s b : Bool) (v : V) : V :=
  (if s then (if b then nextB else prevB) else (if b then nextA else prevA)).getD v.val 0
/-- Matching edge, perimeter edge, repeated three times. -/
def traversal (s : Bool) (v : V) (i : Fin 8) : List V :=
  let a := mate s v
  let b := hop s (i.val % 2 == 1) a
  let c := mate s b
  let d := hop s (i.val / 2 % 2 == 1) c
  let e := mate s d
  let f := hop s (i.val / 4 == 1) e
  [v,a,b,c,d,e,f]
def listedEdges (p : List V) : List (V × V) := p.zip p.tail
def closing (e : V × V) : Prop := (e.1=0 ∧ e.2=17) ∨ (e.1=17 ∧ e.2=0)
instance (e : V × V) : Decidable (closing e) := by unfold closing; infer_instance
def switchVertices : Finset V := {0,1,3,4,10,11}
def ValidTraversal (s : Bool) (v : V) (i : Fin 8) : Prop :=
  let p := traversal s v i
  p.getLast? = some v ∧ (p.take 6).Nodup ∧
    (listedEdges p).all (fun e => !decide (closing e)) = true
instance (s : Bool) (v : V) (i : Fin 8) : Decidable (ValidTraversal s v i) := by
  unfold ValidTraversal; infer_instance

def switchEdges : List (V × V) := [(0,1),(0,4),(1,10),(3,4),(3,11),(10,11)]
def smallLengths : List Nat := [5,6,7,9,10,11,12,13,14,15]
end HamiltonianExchangeTrap

open HamiltonianExchangeTrap

abbrev statement : Prop :=
  (∀ v : V, G.degree v = 3) ∧
  (∃ v : V, ∃ c : G.Walk v v, c.IsCycle ∧ c.length = 18) ∧
  (∃ v : V, ∃ c : G.Walk v v, c.IsCycle ∧ c.length = 8) ∧
  (∀ s : Bool, ∀ v : V, ∀ i : Fin 8,
    ValidTraversal s v i → ((traversal s v i).take 6).toFinset = switchVertices) ∧
  (∀ s : Bool, ∀ v : V, ∀ i : Fin 4,
    let a := mate s v
    let b := hop s (i.val % 2 == 1) a
    let c := mate s b
    let d := hop s (i.val / 2 == 1) c
    ¬ (d = v ∧ [v,a,b,c].Nodup)) ∧
  (∀ u v : V, u ∈ switchVertices → v ∈ switchVertices →
    (G.Adj u v ↔ (u,v) ∈ switchEdges ∨ (v,u) ∈ switchEdges)) ∧
  (orderB.Nodup ∧ orderB.length = 18 ∧
    (listedEdges (orderB ++ [0])).all (fun e => decide (G.Adj e.1 e.2)) = true) ∧
  (∀ n k : Nat, n ∈ smallLengths → 2 ≤ k → n ≠ 2 ^ k) ∧
  (∀ t d k : Nat, 4 ≤ t → d ≤ 30 → 18 * (2 ^ t) - d ≠ 2 ^ k)

end Statements.J4P399HamiltonianExchange
