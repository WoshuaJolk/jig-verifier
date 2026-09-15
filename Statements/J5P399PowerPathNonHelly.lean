import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Combinatorics.SimpleGraph.Finite

namespace Statements.J5P399PowerPathNonHelly

open SimpleGraph

def neighbors (v : Fin 20) : List (Fin 20) :=
  match v.val with
  | 0 => [5,7,9]
  | 1 => [11,12,13]
  | 2 => [6,11,14,18]
  | 3 => [8,12,15,16]
  | 4 => [10,13,17,19]
  | 5 => [0,6]
  | 6 => [2,5]
  | 7 => [0,8]
  | 8 => [3,7]
  | 9 => [0,10]
  | 10 => [4,9]
  | 11 => [1,2]
  | 12 => [1,3]
  | 13 => [1,4]
  | 14 => [2,15]
  | 15 => [3,14]
  | 16 => [3,17]
  | 17 => [4,16]
  | 18 => [2,19]
  | _ => [4,18]

def graph : SimpleGraph (Fin 20) := SimpleGraph.fromRel (fun u v => v ∈ neighbors u)
instance : DecidableRel graph.Adj := fun _ _ =>
  inferInstanceAs (Decidable (_ ≠ _ ∧ (_ ∈ neighbors _ ∨ _ ∈ neighbors _)))


abbrev statement : Prop :=
  graph.degree 0=3 ∧ graph.degree 1=3 ∧ graph.degree 5=2 ∧
    (∀ u (p : graph.Walk u u), p.IsCycle → ∀ k : Nat, 2≤k → p.length≠2^k) ∧
    (∃ ps : Fin 6 → graph.Walk 0 1,
      (∀ i, (ps i).IsPath ∧ (ps i).length=8) ∧
      (∀ i j, i≠j → ∃ x : Fin 20,
        x≠0 ∧ x≠1 ∧ x∈(ps i).support ∧ x∈(ps j).support) ∧
      (¬ ∃ x : Fin 20, x≠0 ∧ x≠1 ∧ ∀ i, x∈(ps i).support))

end Statements.J5P399PowerPathNonHelly
