import Mathlib.Combinatorics.SimpleGraph.Paths

namespace Statements.J4P399RotationOrbit
namespace RotationOrbitCounterexample

open SimpleGraph

abbrev V := Fin 10

def edges : List (V × V) :=
  [(0,1),(0,4),(0,9),(1,2),(1,6),(2,3),(2,8),(3,4),
   (3,9),(4,5),(5,6),(5,7),(6,7),(7,8),(8,9)]

def G : SimpleGraph V := SimpleGraph.fromRel (fun u v => (u,v) ∈ edges)

instance : DecidableRel G.Adj :=
  inferInstanceAs (DecidableRel (SimpleGraph.fromRel (fun u v => (u,v) ∈ edges)).Adj)

def states : List (List V) :=
  [[7,8,9,0,1,2,3,4,5,6],
   [4,3,2,1,0,9,8,7,5,6],
   [5,4,3,2,1,0,9,8,7,6],
   [1,2,3,4,0,9,8,7,5,6],
   [8,9,0,1,2,3,4,5,7,6],
   [5,7,8,9,0,4,3,2,1,6],
   [1,0,9,8,2,3,4,5,7,6],
   [0,9,8,7,5,4,3,2,1,6],
   [7,5,4,3,2,8,9,0,1,6],
   [2,3,4,5,7,8,9,0,1,6]]

def state (s : Fin 10) : List V := states.getD s.val []
def rotate (p : List V) (i : Fin 10) : List V :=
  (p.take i.val).reverse ++ p.drop i.val
def Legal (p : List V) (i : Fin 10) : Prop :=
  2 ≤ i.val ∧ G.Adj (p.getD 0 0) (p.getD i.val 0)

instance (p : List V) (i : Fin 10) : Decidable (Legal p i) :=
  inferInstanceAs (Decidable (2 ≤ i.val ∧ G.Adj (p.getD 0 0) (p.getD i.val 0)))

end RotationOrbitCounterexample

open RotationOrbitCounterexample

abbrev statement : Prop :=
  (∀ v : V, G.degree v = 3) ∧
  (∀ s : Fin 10, (state s).Nodup ∧ (state s).length = 10 ∧
    (state s).IsChain G.Adj ∧ (state s).getLast? = some 6) ∧
  (∀ s i : Fin 10, Legal (state s) i → ∃ t : Fin 10, rotate (state s) i = state t) ∧
  (∀ s i : Fin 10, Legal (state s) i →
    ¬ ∃ k : Nat, 2 ≤ k ∧ i.val + 1 = 2 ^ k) ∧
  (∀ s i j : Fin 10, Legal (state s) i → Legal (state s) j → i.val < j.val →
    ¬ ∃ k : Nat, 2 ≤ k ∧ j.val - i.val + 2 = 2 ^ k) ∧
  (∃ v : V, ∃ c : G.Walk v v, c.IsCycle ∧ c.length = 4)

end Statements.J4P399RotationOrbit
