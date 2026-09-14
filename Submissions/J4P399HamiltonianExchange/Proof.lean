import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Combinatorics.SimpleGraph.Finite

namespace Submissions.J4P399HamiltonianExchange.Proof

/-! Local three-exchange obstruction: actual finite graph and walks,
finite alternating-traversal and length-profile checks. Generic graph
classification and unbounded reconfiguration theorem remain paper results. -/
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

theorem cubic : ∀ v : V, G.degree v=3 := by decide

def basePath : G.Walk (0 : V) 17 :=
  .cons (show G.Adj (0 : V) 1 by decide)
    (.cons (show G.Adj (1 : V) 2 by decide)
      (.cons (show G.Adj (2 : V) 3 by decide)
        (.cons (show G.Adj (3 : V) 4 by decide)
          (.cons (show G.Adj (4 : V) 5 by decide)
            (.cons (show G.Adj (5 : V) 6 by decide)
              (.cons (show G.Adj (6 : V) 7 by decide)
                (.cons (show G.Adj (7 : V) 8 by decide)
                  (.cons (show G.Adj (8 : V) 9 by decide)
                    (.cons (show G.Adj (9 : V) 10 by decide)
                      (.cons (show G.Adj (10 : V) 11 by decide)
                        (.cons (show G.Adj (11 : V) 12 by decide)
                          (.cons (show G.Adj (12 : V) 13 by decide)
                            (.cons (show G.Adj (13 : V) 14 by decide)
                              (.cons (show G.Adj (14 : V) 15 by decide)
                                (.cons (show G.Adj (15 : V) 16 by decide)
                                  (.cons (show G.Adj (16 : V) 17 by decide)
                                    .nil))))))))))))))))
theorem basePath_isPath : basePath.IsPath := by
  unfold basePath
  rw [Walk.isPath_def]
  decide
theorem basePath_length : basePath.length=17 := rfl

def perimeter : G.Walk (17 : V) 17 :=
  .cons (show G.Adj (17 : V) 0 by decide) basePath
theorem perimeter_isCycle : perimeter.IsCycle := by
  unfold perimeter basePath
  rw [Walk.cons_isCycle_iff]
  constructor
  · rw [Walk.isPath_def]
    decide
  · decide
theorem perimeter_length : perimeter.length=18 := rfl

def eight : G.Walk (1 : V) 1 :=
  .cons (show G.Adj (1 : V) 2 by decide)
    (.cons (show G.Adj (2 : V) 7 by decide)
      (.cons (show G.Adj (7 : V) 8 by decide)
        (.cons (show G.Adj (8 : V) 13 by decide)
          (.cons (show G.Adj (13 : V) 12 by decide)
            (.cons (show G.Adj (12 : V) 11 by decide)
              (.cons (show G.Adj (11 : V) 10 by decide)
                (.cons (show G.Adj (10 : V) 1 by decide) .nil)))))))
theorem eight_isCycle : eight.IsCycle := by
  unfold eight
  rw [Walk.cons_isCycle_iff]
  constructor
  · rw [Walk.isPath_def]
    decide
  · decide
theorem eight_length : eight.length=8 := rfl


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

theorem traversal_vertices : ∀ s : Bool, ∀ v : V, ∀ i : Fin 8,
    ValidTraversal s v i → ((traversal s v i).take 6).toFinset = switchVertices := by decide

theorem local_neighbors : ∀ s : Bool, ∀ v : V,
    G.Adj v (mate s v) ∧ G.Adj v (hop s false v) ∧ G.Adj v (hop s true v) ∧
    mate s v ≠ hop s false v ∧ mate s v ≠ hop s true v ∧
    hop s false v ≠ hop s true v := by decide

theorem no_alternating_square : ∀ s : Bool, ∀ v : V, ∀ i : Fin 4,
    let a := mate s v
    let b := hop s (i.val % 2 == 1) a
    let c := mate s b
    let d := hop s (i.val / 2 == 1) c
    ¬ (d=v ∧ [v,a,b,c].Nodup) := by decide

def switchEdges : List (V × V) := [(0,1),(0,4),(1,10),(3,4),(3,11),(10,11)]
theorem induced_switch : ∀ u v : V, u ∈ switchVertices → v ∈ switchVertices →
    (G.Adj u v ↔ (u,v) ∈ switchEdges ∨ (v,u) ∈ switchEdges) := by decide

theorem second_perimeter_list : orderB.Nodup ∧ orderB.length=18 ∧
    (listedEdges (orderB++[0])).all (fun e => decide (G.Adj e.1 e.2))=true := by decide

def smallLengths : List Nat := [5,6,7,9,10,11,12,13,14,15]
inductive LengthClass where
  | small : Nat → LengthClass
  | long : Nat → LengthClass
  deriving DecidableEq
def Valid : LengthClass → Prop
  | .small n => n ∈ smallLengths
  | .long d => d ≤ 30
instance (v : LengthClass) : Decidable (Valid v) := by
  cases v <;> unfold Valid <;> infer_instance
def evaluate (N : Nat) : LengthClass → Nat
  | .small n => n
  | .long d => N-d
def profile0 : List (Nat × Nat) := [(0,4),(1,10),(2,7),(3,11),(5,14),(6,16),(8,13),(9,15),(12,17)]
def profile1 : List (Nat × Nat) := [(0,8),(1,10),(2,14),(3,16),(4,9),(5,13),(6,15),(7,11),(12,17)]
def chordAt (s : Bool) (i : Fin 9) := (if s then profile1 else profile0).getD i.val (0,0)
def singles (s : Bool) (i : Fin 9) : List LengthClass :=
  let e := chordAt s i
  [.small (e.2-e.1+1),.long (e.2-e.1-1)]
def orderedPairValues (e f : Nat × Nat) : List LengthClass :=
  if e.2 < f.1 then [.long ((e.2-e.1)+(f.2-f.1)-2)]
  else if e.2 < f.2 then
    [.small ((f.1-e.1)+(f.2-e.2)+2),.long ((f.1-e.1)+(f.2-e.2)-2)]
  else [.small ((f.1-e.1)+(e.2-f.2)+2)]
def pairs (s : Bool) (i j : Fin 9) : List LengthClass :=
  let e := chordAt s i; let f := chordAt s j
  if e.1 < f.1 then orderedPairValues e f else orderedPairValues f e

theorem finite_length_classes :
    (∀ s : Bool, ∀ i : Fin 9, (singles s i).all (fun v => decide (Valid v))=true) ∧
    (∀ s : Bool, ∀ i j : Fin 9, i ≠ j → (pairs s i j).all (fun v => decide (Valid v))=true) ∧
    (∀ s t : Bool, ∀ i j : Fin 9,
      ((chordAt s i).2-(chordAt s i).1)+((chordAt t j).2-(chordAt t j).1)-2 ≤ 30) := by decide
theorem small_no_power (n k : Nat) (hn : n ∈ smallLengths) (hk : 2 ≤ k) : n ≠ 2^k := by
  have hb : n ≤ 18 ∧ n ≠ 4 ∧ n ≠ 8 ∧ n ≠ 16 := by
    simp [smallLengths] at hn
    omega
  by_cases hlarge : 5 ≤ k
  · have h := Nat.pow_le_pow_right (by decide : 0<2) hlarge
    change 32 ≤ 2^k at h
    omega
  · have hcases : k=2 ∨ k=3 ∨ k=4 := by omega
    rcases hcases with rfl | rfl | rfl <;> simp_all

theorem no_power_between (t n k : Nat) (hlo : 2^t < n)
    (hhi : n < 2^(t+1)) : n ≠ 2^k := by
  by_cases hkt : k ≤ t
  · have h := Nat.pow_le_pow_right (by decide : 0<2) hkt
    omega
  · have h := Nat.pow_le_pow_right (by decide : 0<2) (show t+1 ≤ k by omega)
    omega

/-- All long classes lie strictly between the same consecutive powers;
the class with d=0 includes the Hamiltonian cycle itself. -/
theorem long_no_power (t d k : Nat) (ht : 4 ≤ t) (hd : d ≤ 30) :
    18*(2^t)-d ≠ 2^k := by
  have h := Nat.pow_le_pow_right (by decide : 0<2) ht
  change 16 ≤ 2^t at h
  apply no_power_between (t+4) (18*(2^t)-d) k
  · simp only [pow_add]
    change 2^t*16 < 18*(2^t)-d
    omega
  · have heq : t+4+1=t+5 := by omega
    rw [heq,pow_add]
    change 18*(2^t)-d < 2^t*32
    omega

theorem valid_class_no_power (t k : Nat) (v : LengthClass)
    (ht : 4 ≤ t) (hk : 2 ≤ k) (hv : Valid v) :
    evaluate (18*(2^t)) v ≠ 2^k := by
  cases v with
  | small n => exact small_no_power n k hv hk
  | long d => exact long_no_power t d k ht hv


end HamiltonianExchangeTrap

open HamiltonianExchangeTrap

theorem proof :
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
  (∀ t d k : Nat, 4 ≤ t → d ≤ 30 → 18 * (2 ^ t) - d ≠ 2 ^ k) := by
  exact ⟨cubic, ⟨17, perimeter, perimeter_isCycle, perimeter_length⟩,
    ⟨1, eight, eight_isCycle, eight_length⟩, traversal_vertices,
    no_alternating_square, induced_switch, second_perimeter_list,
    small_no_power, long_no_power⟩

end Submissions.J4P399HamiltonianExchange.Proof
