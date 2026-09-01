import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Star.Basic
import Mathlib.LinearAlgebra.LinearIndependent.Basic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph

namespace Statements.TightSpanningOrthRep3Petersen10

/-- Symmetric edge relation of the Petersen graph. -/
def edge (i j : Fin 10) : Prop :=
  (min i.val j.val, max i.val j.val) ∈
    [(0,1),(0,4),(0,5),(1,2),(1,6),(2,3),(2,7),(3,4),(3,8),(4,9),(5,7),(5,8),(6,8),(6,9),(7,9)]

instance edgeDecidable (i j : Fin 10) : Decidable (edge i j) := by
  unfold edge
  infer_instance

def graph : SimpleGraph (Fin 10) := SimpleGraph.fromRel edge

def pair (x y : Fin 3 → ℂ) : ℂ := ∑ r, star (x r) * y r

def Rank3of4 (v : Fin 10 → Fin 3 → ℂ) (i j k l : Fin 10) : Prop :=
  LinearIndependent ℂ ![v i, v j, v k] ∨
  LinearIndependent ℂ ![v i, v j, v l] ∨
  LinearIndependent ℂ ![v i, v k, v l] ∨
  LinearIndependent ℂ ![v j, v k, v l]

/-- The petersen graph, realized as the exact Hermitian orthogonality
graph of 10 nonzero vectors in C^3: connected, cubic, tight (every two vectors
independent) and 4-spanning (no four in a common plane) - the m = 10 instance of
the k = 3 row of the seed hypothesis (`SeedSufficesForMixedMinUPB`), with the
graph prescribed. -/
abbrev statement : Prop :=
  ∃ v : Fin 10 → Fin 3 → ℂ,
    (∀ i, v i ≠ 0) ∧
    (∀ i j, pair (v i) (v j) = 0 ↔ edge i j) ∧
    (∀ i, ((Finset.univ : Finset (Fin 10)).filter (edge i)).card = 3) ∧
    graph.Connected ∧
    (∀ i j : Fin 10, i < j → LinearIndependent ℂ ![v i, v j]) ∧
    (∀ i j k l : Fin 10, i < j → j < k → k < l → Rank3of4 v i j k l)

theorem target : statement := sorry

end Statements.TightSpanningOrthRep3Petersen10
