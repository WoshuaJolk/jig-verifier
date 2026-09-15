import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Combinatorics.SimpleGraph.Finite

namespace Statements.J5P399NonportGluing
open SimpleGraph

def edges : List (Fin 18 × Fin 18) := [(0,1),(0,2),(0,3),(0,4),(0,12),(1,2),(1,7),(1,13),(1,14),(2,8),(2,9),(2,17),(3,4),(3,5),(4,6),(5,7),(6,7),(8,9),(8,10),(9,11),(10,12),(11,12),(13,14),(13,15),(14,16),(15,17),(16,17)]

def perm (s : Fin 6) (j : Fin 3) : Fin 3 :=
  let row := (([[0,1,2],[0,2,1],[1,0,2],[1,2,0],[2,0,1],[2,1,0]] : List (List (Fin 3)))[s.val]?).getD [0,1,2]
  (row[j.val]?).getD 0

def x (j : Fin 3) : Fin 24 := if j=0 then 3 else if j=1 then 8 else 13
def p (j : Fin 3) : Fin 24 := if j=0 then 5 else if j=1 then 10 else 15
def q (j : Fin 3) : Fin 24 := if j=0 then 6 else if j=1 then 11 else 16
def z (j : Fin 3) : Fin 24 := if j=0 then 7 else if j=1 then 12 else 17
def flip (f : Fin 8) (j : Fin 3) : Bool := f.val / 2^j.val % 2 == 1
def bx (s : Fin 6) (f : Fin 8) (j : Fin 3) : Fin 24 :=
  if flip f j then q (perm s j) else p (perm s j)
def bz (s : Fin 6) (f : Fin 8) (j : Fin 3) : Fin 24 :=
  if flip f j then p (perm s j) else q (perm s j)
def imageB (s : Fin 6) (f : Fin 8) (t : Fin 6) (v : Fin 18) : Fin 24 :=
  (([18,19,20,bx s f 0,21,z (perm s 0),x (perm t 0),bz s f 0,
    bx s f 1,22,z (perm s 1),x (perm t 1),bz s f 1,
    bx s f 2,23,z (perm s 2),x (perm t 2),bz s f 2] : List (Fin 24))[v.val]?).getD 0

def imageA (v : Fin 18) : Fin 24 := ⟨v.val,by omega⟩
def joinedEdges (s : Fin 6) (f : Fin 8) (t : Fin 6) : List (Fin 24 × Fin 24) :=
  edges.map (fun e => (imageA e.1,imageA e.2)) ++
  edges.map (fun e => (imageB s f t e.1,imageB s f t e.2))
def joined (s : Fin 6) (f : Fin 8) (t : Fin 6) : SimpleGraph (Fin 24) :=
  SimpleGraph.fromRel (fun u v => (u,v) ∈ joinedEdges s f t)
instance (s : Fin 6) (f : Fin 8) (t : Fin 6) : DecidableRel (joined s f t).Adj := by
  unfold joined; infer_instance

abbrev statement : Prop :=
  ∀ (s : Fin 6) (f : Fin 8) (t : Fin 6),
    ∃ v, ∃ w : (joined s f t).Walk v v,
      w.IsCycle ∧ (w.length=4 ∨ w.length=8)

end Statements.J5P399NonportGluing
