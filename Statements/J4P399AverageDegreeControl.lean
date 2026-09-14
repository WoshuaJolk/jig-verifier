import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Combinatorics.SimpleGraph.Finite

namespace Statements.J4P399AverageDegreeControl
namespace AverageDegreeControl
open SimpleGraph
def neighbors (v : Fin 18) : List (Fin 18) :=
  match v.val with
  | 0 => [1,2,3,4,12]
  | 1 => [0,2,7,13,14]
  | 2 => [0,1,8,9,17]
  | 3 => [0,4,5]
  | 4 => [0,3,6]
  | 5 => [3,7]
  | 6 => [4,7]
  | 7 => [1,5,6]
  | 8 => [2,9,10]
  | 9 => [2,8,11]
  | 10 => [8,12]
  | 11 => [9,12]
  | 12 => [0,10,11]
  | 13 => [1,14,15]
  | 14 => [1,13,16]
  | 15 => [13,17]
  | 16 => [14,17]
  | _ => [2,15,16]

def graph : SimpleGraph (Fin 18) := SimpleGraph.fromRel (fun u v => v ∈ neighbors u)
instance : DecidableRel graph.Adj := fun _ _ =>
  inferInstanceAs (Decidable (_ ≠ _ ∧ (_ ∈ neighbors _ ∨ _ ∈ neighbors _)))

end AverageDegreeControl

open AverageDegreeControl

abbrev statement : Prop :=
  2 * graph.edgeFinset.card = 3 * Fintype.card (Fin 18) ∧
  (∀ v : Fin 18, 2 ≤ graph.degree v) ∧ graph.degree 5 = 2 ∧
  (∀ u (p : graph.Walk u u), p.IsCycle → ∀ k : Nat, 2 ≤ k → p.length ≠ 2 ^ k)

end Statements.J4P399AverageDegreeControl
