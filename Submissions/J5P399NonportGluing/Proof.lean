import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Combinatorics.SimpleGraph.Finite

/- Positive certificates for the B18 nonport-gluing reduction.
The family reduction and independent-set classification remain paper arguments.
All288 explicitly parameterized residual quotients have actual4/8 cycles.
No unrestricted minimum-degree-three theorem is asserted. -/
namespace Submissions.J5P399NonportGluing.Proof
open SimpleGraph

def edges : List (Fin 18 × Fin 18) := [(0,1),(0,2),(0,3),(0,4),(0,12),(1,2),(1,7),(1,13),(1,14),(2,8),(2,9),(2,17),(3,4),(3,5),(4,6),(5,7),(6,7),(8,9),(8,10),(9,11),(10,12),(11,12),(13,14),(13,15),(14,16),(15,17),(16,17)]
def base : SimpleGraph (Fin 18) := SimpleGraph.fromRel (fun u v => (u,v) ∈ edges)
instance : DecidableRel base.Adj := by unfold base; infer_instance

def port (i : Fin 6) : Fin 18 := ([5,6,10,11,15,16][i.val]?).getD 0
def selected (i : Fin 6) : Fin 18 := ([3,7,8,12,13,17][i.val]?).getD 0
def sevenTable : List (Fin 6 × Fin 6 × List (Fin 18)) := [
  (0,1,[5,3,4,0,2,1,7,6]),
  (0,2,[5,3,0,1,2,9,8,10]),
  (0,3,[5,3,0,1,2,8,9,11]),
  (0,4,[5,3,0,1,14,16,17,15]),
  (0,5,[5,3,0,1,13,15,17,16]),
  (1,2,[6,4,0,1,2,9,8,10]),
  (1,3,[6,4,0,1,2,8,9,11]),
  (1,4,[6,4,0,1,14,16,17,15]),
  (1,5,[6,4,0,1,13,15,17,16]),
  (2,3,[10,8,9,2,1,0,12,11]),
  (2,4,[10,8,2,0,1,14,13,15]),
  (2,5,[10,8,2,0,1,13,14,16]),
  (3,4,[11,9,2,0,1,14,13,15]),
  (3,5,[11,9,2,0,1,13,14,16]),
  (4,5,[15,13,14,1,0,2,17,16])
]
def sixTable : List (Fin 6 × Fin 6 × Fin 6 × List (Fin 18)) := [
  (0,1,0,[5,7,1,2,0,4,6]),
  (0,1,2,[5,3,0,2,1,7,6]),
  (0,1,3,[5,3,0,2,1,7,6]),
  (0,1,4,[5,3,0,2,1,7,6]),
  (0,1,5,[5,3,0,2,1,7,6]),
  (0,2,0,[5,7,1,0,2,8,10]),
  (0,2,1,[5,3,0,1,2,8,10]),
  (0,2,2,[5,7,1,2,0,12,10]),
  (0,2,3,[5,3,0,1,2,8,10]),
  (0,2,4,[5,3,0,1,2,8,10]),
  (0,2,5,[5,3,0,1,2,8,10]),
  (0,3,0,[5,7,1,0,2,9,11]),
  (0,3,1,[5,3,0,1,2,9,11]),
  (0,3,2,[5,3,0,1,2,9,11]),
  (0,3,3,[5,3,0,1,2,9,11]),
  (0,3,4,[5,3,0,1,2,9,11]),
  (0,3,5,[5,3,0,1,2,9,11]),
  (0,4,0,[5,7,1,0,2,17,15]),
  (0,4,1,[5,3,0,1,2,17,15]),
  (0,4,2,[5,3,0,1,2,17,15]),
  (0,4,3,[5,3,0,1,2,17,15]),
  (0,4,4,[5,3,0,1,2,17,15]),
  (0,4,5,[5,3,0,1,14,13,15]),
  (0,5,0,[5,7,1,0,2,17,16]),
  (0,5,1,[5,3,0,1,2,17,16]),
  (0,5,2,[5,3,0,1,2,17,16]),
  (0,5,3,[5,3,0,1,2,17,16]),
  (0,5,4,[5,3,0,1,2,17,16]),
  (0,5,5,[5,3,0,1,13,14,16]),
  (1,2,0,[6,4,0,1,2,8,10]),
  (1,2,1,[6,4,0,1,2,8,10]),
  (1,2,2,[6,7,1,2,0,12,10]),
  (1,2,3,[6,4,0,1,2,8,10]),
  (1,2,4,[6,4,0,1,2,8,10]),
  (1,2,5,[6,4,0,1,2,8,10]),
  (1,3,0,[6,4,0,1,2,9,11]),
  (1,3,1,[6,4,0,1,2,9,11]),
  (1,3,2,[6,4,0,1,2,9,11]),
  (1,3,3,[6,4,0,1,2,9,11]),
  (1,3,4,[6,4,0,1,2,9,11]),
  (1,3,5,[6,4,0,1,2,9,11]),
  (1,4,0,[6,4,0,1,2,17,15]),
  (1,4,1,[6,4,0,1,2,17,15]),
  (1,4,2,[6,4,0,1,2,17,15]),
  (1,4,3,[6,4,0,1,2,17,15]),
  (1,4,4,[6,4,0,1,2,17,15]),
  (1,4,5,[6,4,0,1,14,13,15]),
  (1,5,0,[6,4,0,1,2,17,16]),
  (1,5,1,[6,4,0,1,2,17,16]),
  (1,5,2,[6,4,0,1,2,17,16]),
  (1,5,3,[6,4,0,1,2,17,16]),
  (1,5,4,[6,4,0,1,2,17,16]),
  (1,5,5,[6,4,0,1,13,14,16]),
  (2,3,0,[10,8,2,1,0,12,11]),
  (2,3,1,[10,8,2,1,0,12,11]),
  (2,3,2,[10,12,0,1,2,9,11]),
  (2,3,4,[10,8,2,1,0,12,11]),
  (2,3,5,[10,8,2,1,0,12,11]),
  (2,4,0,[10,8,2,0,1,13,15]),
  (2,4,1,[10,8,2,0,1,13,15]),
  (2,4,2,[10,12,0,1,2,17,15]),
  (2,4,3,[10,8,2,0,1,13,15]),
  (2,4,4,[10,12,0,1,2,17,15]),
  (2,4,5,[10,8,2,0,1,13,15]),
  (2,5,0,[10,8,2,0,1,14,16]),
  (2,5,1,[10,8,2,0,1,14,16]),
  (2,5,2,[10,12,0,1,2,17,16]),
  (2,5,3,[10,8,2,0,1,14,16]),
  (2,5,4,[10,8,2,0,1,14,16]),
  (2,5,5,[10,8,2,0,1,14,16]),
  (3,4,0,[11,9,2,0,1,13,15]),
  (3,4,1,[11,9,2,0,1,13,15]),
  (3,4,2,[11,9,2,0,1,13,15]),
  (3,4,3,[11,9,2,0,1,13,15]),
  (3,4,4,[11,12,0,1,2,17,15]),
  (3,4,5,[11,9,2,0,1,13,15]),
  (3,5,0,[11,9,2,0,1,14,16]),
  (3,5,1,[11,9,2,0,1,14,16]),
  (3,5,2,[11,9,2,0,1,14,16]),
  (3,5,3,[11,9,2,0,1,14,16]),
  (3,5,4,[11,9,2,0,1,14,16]),
  (3,5,5,[11,9,2,0,1,14,16]),
  (4,5,0,[15,13,1,0,2,17,16]),
  (4,5,1,[15,13,1,0,2,17,16]),
  (4,5,2,[15,13,1,0,2,17,16]),
  (4,5,3,[15,13,1,0,2,17,16]),
  (4,5,4,[15,17,2,0,1,14,16])
]

def seven (i j : Fin 6) : List (Fin 18) :=
  ((sevenTable.find? fun r => r.1==i && r.2.1==j).map fun r => r.2.2).getD []
def six (i j k : Fin 6) : List (Fin 18) :=
  ((sixTable.find? fun r => r.1==i && r.2.1==j && r.2.2.1==k).map fun r => r.2.2.2).getD []
def PathValid (i j : Fin 6) (n : Nat) (xs : List (Fin 18)) : Prop :=
  xs.head?=some (port i) ∧ xs.getLast?=some (port j) ∧
  xs.Nodup ∧ xs.IsChain base.Adj ∧ xs.length=n+1
instance (i j : Fin 6) (n : Nat) (xs : List (Fin 18)) : Decidable (PathValid i j n xs) := by
  unfold PathValid; infer_instance
def Exceptional (i j k : Fin 6) : Prop :=
  (i=0 ∧ j=1 ∧ k=1) ∨ (i=2 ∧ j=3 ∧ k=3) ∨ (i=4 ∧ j=5 ∧ k=5)
instance (i j k : Fin 6) : Decidable (Exceptional i j k) := by
  unfold Exceptional; infer_instance

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem local_certificates :
  (∀ i j : Fin 6, i<j → PathValid i j 7 (seven i j)) ∧
  (∀ i j k : Fin 6, i<j → ¬ Exceptional i j k →
    PathValid i j 6 (six i j k) ∧ selected k ∉ six i j k) := by decide

theorem path_from_certificate (i j : Fin 6) (n : Nat) (xs : List (Fin 18))
    (h : PathValid i j n xs) :
    ∃ w : base.Walk (port i) (port j), w.IsPath ∧ w.length=n ∧ w.support=xs := by
  rcases h with ⟨hh,ht,hnd,hchain,hlen⟩
  have hne : xs ≠ [] := by intro hz; simp [hz] at hh
  have hhead : xs.head hne=port i := (List.head_eq_iff_head?_eq_some _).mpr hh
  have hlast : xs.getLast hne=port j := (List.getLast_eq_iff_getLast?_eq_some _).mpr ht
  let w : base.Walk (port i) (port j) := (Walk.ofSupport xs hne hchain).copy hhead hlast
  refine ⟨w, ?_, ?_, ?_⟩
  · apply Walk.IsPath.mk'; simpa [w] using hnd
  · simp only [w,Walk.length_copy,Walk.length_ofSupport]; omega
  · simp [w]

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

def cycles : Array (List (Fin 24)) := #[
  [0,3,6,4],
  [0,3,6,4],
  [0,3,11,12],
  [0,1,2,8,6,7,5,3],
  [0,3,11,12],
  [1,7,6,13],
  [1,13,16,14],
  [2,8,16,17],
  [0,3,11,12],
  [3,5,19,23],
  [0,3,11,12],
  [1,7,5,13],
  [0,3,6,4],
  [0,3,6,4],
  [0,3,10,12],
  [8,10,18,21],
  [0,3,10,12],
  [1,7,6,13],
  [1,13,16,14],
  [2,8,16,17],
  [0,3,10,12],
  [3,5,19,23],
  [0,3,10,12],
  [1,7,5,13],
  [0,3,6,4],
  [0,3,6,4],
  [0,3,11,12],
  [13,15,20,22],
  [0,3,11,12],
  [1,7,6,13],
  [2,8,11,9],
  [2,8,15,17],
  [0,3,11,12],
  [3,5,19,23],
  [0,3,11,12],
  [1,7,5,13],
  [0,3,6,4],
  [0,3,6,4],
  [0,3,10,12],
  [8,10,18,21],
  [0,3,10,12],
  [1,7,6,13],
  [3,4,6,21],
  [2,8,15,17],
  [0,3,10,12],
  [3,5,19,23],
  [0,3,10,12],
  [1,7,5,13],
  [0,3,6,4],
  [0,3,6,4],
  [3,5,18,16],
  [0,3,11,12],
  [1,7,6,13],
  [0,3,11,12],
  [2,8,16,17],
  [1,13,16,14],
  [5,8,10,19],
  [0,3,11,12],
  [1,7,5,13],
  [0,3,11,12],
  [0,3,6,4],
  [0,3,6,4],
  [3,5,18,15],
  [0,3,11,12],
  [1,7,6,13],
  [0,3,11,12],
  [2,8,15,17],
  [2,8,11,9],
  [5,8,10,19],
  [0,3,11,12],
  [1,7,5,13],
  [0,3,11,12],
  [0,3,6,4],
  [0,3,6,4],
  [3,5,18,16],
  [0,3,10,12],
  [1,7,6,13],
  [0,3,10,12],
  [2,8,16,17],
  [1,13,16,14],
  [10,13,15,20],
  [0,3,10,12],
  [1,7,5,13],
  [0,3,10,12],
  [0,3,6,4],
  [0,3,6,4],
  [3,5,18,15],
  [0,3,10,12],
  [1,7,6,13],
  [0,3,10,12],
  [2,8,15,17],
  [3,4,6,21],
  [0,1,2,8,5,7,6,4],
  [0,3,10,12],
  [1,7,5,13],
  [0,3,10,12],
  [0,3,11,12],
  [0,3,11,12],
  [0,3,6,4],
  [1,7,6,13],
  [0,3,6,4],
  [3,5,20,16],
  [0,3,10,12],
  [0,3,10,12],
  [0,3,6,4],
  [1,7,6,13],
  [0,3,6,4],
  [3,5,20,16],
  [0,3,11,12],
  [0,3,11,12],
  [1,13,16,14],
  [1,7,5,13],
  [2,8,16,17],
  [5,8,10,18],
  [0,3,10,12],
  [0,3,10,12],
  [1,13,16,14],
  [1,7,5,13],
  [2,8,16,17],
  [10,13,15,19],
  [0,3,11,12],
  [0,3,11,12],
  [0,3,6,4],
  [1,7,6,13],
  [0,3,6,4],
  [3,5,20,15],
  [0,3,10,12],
  [0,3,10,12],
  [0,3,6,4],
  [1,7,6,13],
  [0,3,6,4],
  [3,5,20,15],
  [0,3,11,12],
  [0,3,11,12],
  [2,8,11,9],
  [1,7,5,13],
  [2,8,15,17],
  [5,8,10,18],
  [0,3,10,12],
  [0,3,10,12],
  [3,4,6,22],
  [1,7,5,13],
  [2,8,15,17],
  [0,1,2,8,5,7,6,4],
  [0,3,11,12],
  [0,3,11,12],
  [1,7,6,13],
  [0,3,6,4],
  [0,1,2,8,6,7,5,3],
  [0,3,6,4],
  [0,3,10,12],
  [0,3,10,12],
  [1,7,6,13],
  [0,3,6,4],
  [8,10,19,23],
  [0,3,6,4],
  [0,3,11,12],
  [0,3,11,12],
  [1,7,6,13],
  [0,3,6,4],
  [13,15,18,21],
  [0,3,6,4],
  [0,3,10,12],
  [0,3,10,12],
  [1,7,6,13],
  [0,3,6,4],
  [8,10,19,23],
  [0,3,6,4],
  [0,3,11,12],
  [0,3,11,12],
  [1,7,5,13],
  [1,13,16,14],
  [3,5,20,22],
  [2,8,16,17],
  [0,3,10,12],
  [0,3,10,12],
  [1,7,5,13],
  [1,13,16,14],
  [3,5,20,22],
  [2,8,16,17],
  [0,3,11,12],
  [0,3,11,12],
  [1,7,5,13],
  [2,8,11,9],
  [3,5,20,22],
  [2,8,15,17],
  [0,3,10,12],
  [0,3,10,12],
  [1,7,5,13],
  [3,4,6,23],
  [3,5,20,22],
  [2,8,15,17],
  [0,1,2,8,6,7,5,3],
  [1,7,6,13],
  [0,3,6,4],
  [0,3,11,12],
  [0,3,6,4],
  [0,3,11,12],
  [13,15,19,23],
  [1,7,6,13],
  [0,3,6,4],
  [0,3,11,12],
  [0,3,6,4],
  [0,3,11,12],
  [3,5,18,21],
  [1,7,5,13],
  [2,8,16,17],
  [0,3,11,12],
  [1,13,16,14],
  [0,3,11,12],
  [3,5,18,21],
  [1,7,5,13],
  [2,8,15,17],
  [0,3,11,12],
  [2,8,11,9],
  [0,3,11,12],
  [8,10,20,22],
  [1,7,6,13],
  [0,3,6,4],
  [0,3,10,12],
  [0,3,6,4],
  [0,3,10,12],
  [8,10,20,22],
  [1,7,6,13],
  [0,3,6,4],
  [0,3,10,12],
  [0,3,6,4],
  [0,3,10,12],
  [3,5,18,21],
  [1,7,5,13],
  [2,8,16,17],
  [0,3,10,12],
  [1,13,16,14],
  [0,3,10,12],
  [3,5,18,21],
  [1,7,5,13],
  [2,8,15,17],
  [0,3,10,12],
  [3,4,6,22],
  [0,3,10,12],
  [1,7,6,13],
  [3,5,19,16],
  [0,3,11,12],
  [0,3,6,4],
  [0,3,11,12],
  [0,3,6,4],
  [1,7,6,13],
  [3,5,19,15],
  [0,3,11,12],
  [0,3,6,4],
  [0,3,11,12],
  [0,3,6,4],
  [1,7,6,13],
  [3,5,19,16],
  [0,3,10,12],
  [0,3,6,4],
  [0,3,10,12],
  [0,3,6,4],
  [1,7,6,13],
  [3,5,19,15],
  [0,3,10,12],
  [0,3,6,4],
  [0,3,10,12],
  [0,3,6,4],
  [1,7,5,13],
  [5,8,10,20],
  [0,3,11,12],
  [2,8,16,17],
  [0,3,11,12],
  [1,13,16,14],
  [1,7,5,13],
  [5,8,10,20],
  [0,3,11,12],
  [2,8,15,17],
  [0,3,11,12],
  [2,8,11,9],
  [1,7,5,13],
  [10,13,15,18],
  [0,3,10,12],
  [2,8,16,17],
  [0,3,10,12],
  [1,13,16,14],
  [1,7,5,13],
  [0,1,2,8,5,7,6,4],
  [0,3,10,12],
  [2,8,15,17],
  [0,3,10,12],
  [3,4,6,23]
]
def cycle (s : Fin 6) (f : Fin 8) (t : Fin 6) : List (Fin 24) :=
  (cycles[s.val*48+f.val*6+t.val]?).getD []
def ValidCycle (s : Fin 6) (f : Fin 8) (t : Fin 6) : Prop :=
  let xs := cycle s f t
  xs.Nodup ∧ xs.IsChain (joined s f t).Adj ∧ (xs.length=4 ∨ xs.length=8) ∧
    (joined s f t).Adj (xs.getLast?.getD 0) (xs.head?.getD 0)
instance (s : Fin 6) (f : Fin 8) (t : Fin 6) : Decidable (ValidCycle s f t) := by
  unfold ValidCycle; infer_instance

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem residual_certificates : ∀ s : Fin 6, ∀ f : Fin 8, ∀ t : Fin 6,
  ValidCycle s f t := by decide

theorem residual_actual_cycles (s : Fin 6) (f : Fin 8) (t : Fin 6) :
    ∃ v, ∃ w : (joined s f t).Walk v v,
      w.IsCycle ∧ (w.length=4 ∨ w.length=8) := by
  rcases residual_certificates s f t with ⟨hnd,hchain,hlen,hclose⟩
  let xs := cycle s f t
  have hne : xs ≠ [] := by
    intro hz
    have hz' : cycle s f t=[] := hz
    simp [hz'] at hlen
  let a := xs.head hne
  let b := xs.getLast hne
  let w : (joined s f t).Walk a b := Walk.ofSupport xs hne hchain
  have hw : w.IsPath := by apply Walk.IsPath.mk'; simpa [w,xs] using hnd
  have hl : w.length=3 ∨ w.length=7 := by
    simp only [w,Walk.length_ofSupport]
    change xs.length=4 ∨ xs.length=8 at hlen
    omega
  have he : (joined s f t).Adj b a := by
    change (joined s f t).Adj (xs.getLast?.getD 0) (xs.head?.getD 0) at hclose
    rw [List.getLast?_eq_some_getLast hne,List.head?_eq_some_head hne] at hclose
    simpa [a,b] using hclose
  have hn : s(b,a) ∉ w.edges := by
    intro hz
    have hz' : s(a,b) ∈ w.edges := by rw [Sym2.eq_swap]; exact hz
    have hh := hw.length_eq_one_of_mem_edges hz'
    omega
  have hc := (Walk.cons_isCycle_iff w he).mpr ⟨hw,hn⟩
  refine ⟨b,Walk.cons he w,hc,?_⟩
  simp only [Walk.length_cons]
  omega

theorem solves :
  ∀ (s : Fin 6) (f : Fin 8) (t : Fin 6),
    ∃ v, ∃ w : (joined s f t).Walk v v,
      w.IsCycle ∧ (w.length=4 ∨ w.length=8) :=
  residual_actual_cycles

end Submissions.J5P399NonportGluing.Proof
