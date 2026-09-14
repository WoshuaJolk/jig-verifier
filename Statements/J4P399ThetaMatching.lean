import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Combinatorics.SimpleGraph.Finite

namespace Statements.J4P399ThetaMatching
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

end ThetaMatchingSaturation

open ThetaMatchingSaturation

abbrev statement : Prop :=
  (∀ v : Fin 7, source.degree v = if v = 0 ∨ v = 1 then 3 else 2) ∧
  (∀ v (p : source.Walk v v), p.IsCycle → ∀ k : Nat, 2 ≤ k → p.length ≠ 2 ^ k) ∧
  (∀ s : Fin 256, Matching s → ∀ u v : Fin 7,
    collapse s u = collapse s v ↔ u = v ∨ ∃ i : Fin 8, selected s i ∧
      (edge i = (u,v) ∨ edge i = (v,u))) ∧
  (∀ s : Fin 256, Matching s → s.val ≠ 0 →
    ∃ v : Fin 7, ∃ p : (quotient s).Walk v v, p.IsCycle ∧ p.length = 4)

end Statements.J4P399ThetaMatching
