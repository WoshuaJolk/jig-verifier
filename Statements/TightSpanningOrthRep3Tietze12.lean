import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Star.Basic
import Mathlib.LinearAlgebra.LinearIndependent.Basic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph

namespace Statements.TightSpanningOrthRep3Tietze12

/-- Symmetric edge relation of the Tietze graph (Petersen with one vertex expanded to a triangle). -/
def edge (i j : Fin 12) : Prop :=
  (min i.val j.val, max i.val j.val) ∈
    [(0,1),(0,10),(0,11),(1,2),(1,6),(2,3),(2,7),(3,4),(3,8),(4,9),(4,10),(5,7),(5,8),(5,11),(6,8),(6,9),(7,9),(10,11)]

instance edgeDecidable (i j : Fin 12) : Decidable (edge i j) := by
  unfold edge
  infer_instance

def graph : SimpleGraph (Fin 12) := SimpleGraph.fromRel edge

def pair (x y : Fin 3 → ℂ) : ℂ := ∑ r, star (x r) * y r

def Rank3of4 (v : Fin 12 → Fin 3 → ℂ) (i j k l : Fin 12) : Prop :=
  LinearIndependent ℂ ![v i, v j, v k] ∨
  LinearIndependent ℂ ![v i, v j, v l] ∨
  LinearIndependent ℂ ![v i, v k, v l] ∨
  LinearIndependent ℂ ![v j, v k, v l]

/-- The tietze graph (petersen with one vertex expanded to a triangle), realized as the exact Hermitian orthogonality
graph of 12 nonzero vectors in C^3: connected, cubic, tight (every two vectors
independent) and 4-spanning (no four in a common plane) - the m = 12 instance of
the k = 3 row of the seed hypothesis (`SeedSufficesForMixedMinUPB`), with the
graph prescribed. -/
abbrev statement : Prop :=
  ∃ v : Fin 12 → Fin 3 → ℂ,
    (∀ i, v i ≠ 0) ∧
    (∀ i j, pair (v i) (v j) = 0 ↔ edge i j) ∧
    (∀ i, ((Finset.univ : Finset (Fin 12)).filter (edge i)).card = 3) ∧
    graph.Connected ∧
    (∀ i j : Fin 12, i < j → LinearIndependent ℂ ![v i, v j]) ∧
    (∀ i j k l : Fin 12, i < j → j < k → k < l → Rank3of4 v i j k l)

theorem target : statement := sorry

end Statements.TightSpanningOrthRep3Tietze12
