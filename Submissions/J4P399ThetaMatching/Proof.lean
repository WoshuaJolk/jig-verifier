import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Combinatorics.SimpleGraph.Finite

namespace Submissions.J4P399ThetaMatching.Proof

/-! An exact obstruction to deriving a contradiction from matching-subset
coverage and original power-cycle absence alone. The source is theta(2,3,3),
with five degree-two vertices. It is not a counterexample to the full goal.
The map graph retains unused labels as isolated vertices; all cycle witnesses
are explicitly in the contraction image. No graph-level minimum-degree-three
claim or global reduction is asserted. -/
namespace ThetaMatchingSaturation
open SimpleGraph

def edge (i : Fin 8) : Fin 7 × Fin 7 :=
  match i.val with
  | 0 => (0,2) | 1 => (0,3) | 2 => (0,5) | 3 => (1,2)
  | 4 => (1,4) | 5 => (1,6) | 6 => (3,4) | _ => (5,6)
def source : SimpleGraph (Fin 7) :=
  .fromRel (fun u v => ∃ i : Fin 8, edge i=(u,v))
instance : DecidableRel source.Adj := by unfold source; infer_instance

def selected (s : Fin 256) (i : Fin 8) : Prop := s.val / 2^i.val % 2=1
instance (s : Fin 256) (i : Fin 8) : Decidable (selected s i) := by
  unfold selected; infer_instance
def Matching (s : Fin 256) : Prop := ∀ i j : Fin 8,
  i ≠ j → selected s i → selected s j →
  (edge i).1 ≠ (edge j).1 ∧ (edge i).1 ≠ (edge j).2 ∧
  (edge i).2 ≠ (edge j).1 ∧ (edge i).2 ≠ (edge j).2
instance (s : Fin 256) : Decidable (Matching s) := by unfold Matching; infer_instance

def collapse (s : Fin 256) (v : Fin 7) : Fin 7 :=
  match v.val with
  | 0 => 0 | 1 => 1
  | 2 => if selected s 0 then 0 else if selected s 3 then 1 else 2
  | 3 => if selected s 1 then 0 else 3
  | 4 => if selected s 4 then 1 else if selected s 6 then 3 else 4
  | 5 => if selected s 2 then 0 else 5
  | _ => if selected s 5 then 1 else if selected s 7 then 5 else 6
def quotient (s : Fin 256) : SimpleGraph (Fin 7) := source.map (collapse s)
instance (s : Fin 256) : DecidableRel (quotient s).Adj := by
  intro a b
  change Decidable (a ≠ b ∧ ∃ u v : Fin 7,
    source.Adj u v ∧ collapse s u=a ∧ collapse s v=b)
  infer_instance

def witness (s : Fin 256) : Fin 7 × Fin 7 × Fin 7 × Fin 7 :=
  match s.val with
  | 1 => (0,1,4,3)
  | 2 => (0,2,1,4)
  | 4 => (0,2,1,6)
  | 8 => (0,1,4,3)
  | 10 => (0,1,6,5)
  | 12 => (0,1,4,3)
  | 16 => (0,2,1,3)
  | 17 => (0,1,6,5)
  | 18 => (0,1,6,5)
  | 20 => (0,2,1,3)
  | 32 => (0,2,1,5)
  | 33 => (0,1,4,3)
  | 34 => (0,2,1,4)
  | 36 => (0,1,4,3)
  | 64 => (0,2,1,3)
  | 65 => (0,1,6,5)
  | 68 => (0,2,1,3)
  | 72 => (0,1,6,5)
  | 76 => (0,3,1,6)
  | 96 => (0,2,1,3)
  | 97 => (0,3,1,5)
  | 100 => (0,2,1,3)
  | 128 => (0,2,1,5)
  | 129 => (0,1,4,3)
  | 130 => (0,2,1,4)
  | 136 => (0,1,4,3)
  | 138 => (0,4,1,5)
  | 144 => (0,2,1,3)
  | 145 => (0,3,1,5)
  | 146 => (0,2,1,5)
  | 192 => (0,2,1,3)
  | 193 => (0,3,1,5)
  | 200 => (0,3,1,5)
  | _ => (0,0,0,0)

def Valid (s : Fin 256) (t : Fin 7 × Fin 7 × Fin 7 × Fin 7) : Prop :=
  let a:=t.1; let b:=t.2.1; let c:=t.2.2.1; let d:=t.2.2.2
  [b,c,d,a].Nodup ∧ (quotient s).Adj a b ∧ (quotient s).Adj b c ∧
  (quotient s).Adj c d ∧ (quotient s).Adj d a ∧
  ∀ x ∈ [a,b,c,d], ∃ u : Fin 7, collapse s u=x
instance (s : Fin 256) (t : Fin 7 × Fin 7 × Fin 7 × Fin 7) :
    Decidable (Valid s t) := by unfold Valid; infer_instance

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem exact_fibres : ∀ s : Fin 256, Matching s → ∀ u v : Fin 7,
    collapse s u=collapse s v ↔ u=v ∨ ∃ i : Fin 8, selected s i ∧
      ((edge i=(u,v)) ∨ (edge i=(v,u))) := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem all_matching_certificates : ∀ s : Fin 256, Matching s → s.val ≠ 0 →
    Valid s (witness s) := by decide

set_option maxRecDepth 100000 in
theorem selection_nonempty : ∀ s : Fin 256,
    s.val ≠ 0 ↔ ∃ i : Fin 8, selected s i := by decide

theorem matching_count :
    (Finset.univ.filter (fun s : Fin 256 => Matching s ∧ s.val ≠ 0)).card=33 := by
  decide

theorem exact_degrees : ∀ v : Fin 7,
    source.degree v = if v=0 ∨ v=1 then 3 else 2 := by decide

theorem no_triangle : ∀ a b c : Fin 7,
    source.Adj a b → source.Adj b c → source.Adj c a → False := by decide

theorem no_four_configuration : ∀ a b c d : Fin 7,
    a ≠ c → b ≠ d → source.Adj a b → source.Adj b c →
    source.Adj c d → source.Adj d a → False := by decide

theorem source_no_four (v : Fin 7) (p : source.Walk v v)
    (hp : p.IsCycle) : p.length ≠ 4 := by
  intro hl
  have h02 : p.getVert 0 ≠ p.getVert 2 := by
    intro he
    have := hp.getVert_injOn' (by simp [hl]) (by simp [hl]) he
    omega
  have h13 : p.getVert 1 ≠ p.getVert 3 := by
    intro he
    have := hp.getVert_injOn' (by simp [hl]) (by simp [hl]) he
    omega
  have h30 : source.Adj (p.getVert 3) (p.getVert 0) := by
    have ht := p.adj_getVert_succ (i:=3) (by omega)
    simpa [←hl] using ht
  exact no_four_configuration _ _ _ _ h02 h13
    (p.adj_getVert_succ (i:=0) (by omega))
    (p.adj_getVert_succ (i:=1) (by omega))
    (p.adj_getVert_succ (i:=2) (by omega)) h30

theorem source_no_power (v : Fin 7) (p : source.Walk v v) (hp : p.IsCycle)
    (k : ℕ) (hk : 2 ≤ k) : p.length ≠ 2^k := by
  intro he
  have ht : p.length-1 < 7 := by
    simpa [Walk.length_tail] using hp.isPath_tail.length_lt
  have hlow := hp.three_le_length
  have hklt : k < 3 := by
    by_contra hn
    have hb : (2:ℕ)^3 ≤ 2^k := Nat.pow_le_pow_right (by decide) (by omega)
    change 8 ≤ 2^k at hb
    omega
  have hk2 : k=2 := by omega
  apply source_no_four v p hp
  simpa [hk2] using he

theorem every_matching_has_actual_four (s : Fin 256) (hm : Matching s)
    (hn : s.val ≠ 0) :
    ∃ v : Fin 7, ∃ p : (quotient s).Walk v v, p.IsCycle ∧ p.length=4 := by
  rcases hw : witness s with ⟨a,b,c,d⟩
  have h := all_matching_certificates s hm hn
  rw [hw] at h
  obtain ⟨hd,hab,hbc,hcd,hda,_⟩ := h
  let p : (quotient s).Walk a a := .cons hab (.cons hbc (.cons hcd (.cons hda .nil)))
  refine ⟨a,p,?_,by simp [p]⟩
  apply Walk.isCycle_iff_isPath_tail_and_le_length.mpr
  constructor
  · apply Walk.IsPath.mk'
    simpa [p] using hd
  · simp [p]

end ThetaMatchingSaturation

open ThetaMatchingSaturation

theorem proof :
  (∀ v : Fin 7, source.degree v = if v = 0 ∨ v = 1 then 3 else 2) ∧
  (∀ v (p : source.Walk v v), p.IsCycle → ∀ k : Nat, 2 ≤ k → p.length ≠ 2 ^ k) ∧
  (∀ s : Fin 256, Matching s → ∀ u v : Fin 7,
    collapse s u = collapse s v ↔ u = v ∨ ∃ i : Fin 8, selected s i ∧
      (edge i = (u,v) ∨ edge i = (v,u))) ∧
  (∀ s : Fin 256, Matching s → s.val ≠ 0 →
    ∃ v : Fin 7, ∃ p : (quotient s).Walk v v, p.IsCycle ∧ p.length = 4) := by
  exact ⟨exact_degrees, source_no_power, exact_fibres, every_matching_has_actual_four⟩

end Submissions.J4P399ThetaMatching.Proof
