import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Star.Basic
import Mathlib.LinearAlgebra.LinearIndependent.Basic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph

namespace Statements.TightSpanningOrthRep3Cubic20

/-- Symmetric edge relation of an explicit connected C4-free cubic graph on 20 vertices. -/
def edge (i j : Fin 20) : Prop :=
  (min i.val j.val, max i.val j.val) ∈
    [(0,5),(0,8),(0,19),(1,2),(1,3),(1,14),(2,4),(2,11),(3,9),(3,12),(4,7),(4,11),(5,17),(5,19),(6,13),(6,16),(6,18),(7,9),(7,10),(8,10),(8,12),(9,13),(10,18),(11,15),(12,16),(13,19),(14,16),(14,17),(15,17),(15,18)]

instance edgeDecidable (i j : Fin 20) : Decidable (edge i j) := by
  unfold edge
  infer_instance

def graph : SimpleGraph (Fin 20) := SimpleGraph.fromRel edge

def pair (x y : Fin 3 → ℂ) : ℂ := ∑ r, star (x r) * y r

def Rank3of4 (v : Fin 20 → Fin 3 → ℂ) (i j k l : Fin 20) : Prop :=
  LinearIndependent ℂ ![v i, v j, v k] ∨
  LinearIndependent ℂ ![v i, v j, v l] ∨
  LinearIndependent ℂ ![v i, v k, v l] ∨
  LinearIndependent ℂ ![v j, v k, v l]

/-- An explicit connected c4-free cubic graph on 20 vertices, realized as the exact Hermitian orthogonality
graph of 20 nonzero vectors in C^3: connected, cubic, tight (every two vectors
independent) and 4-spanning (no four in a common plane) - the m = 20 instance of
the k = 3 row of the seed hypothesis (`SeedSufficesForMixedMinUPB`), with the
graph prescribed. -/
abbrev statement : Prop :=
  ∃ v : Fin 20 → Fin 3 → ℂ,
    (∀ i, v i ≠ 0) ∧
    (∀ i j, pair (v i) (v j) = 0 ↔ edge i j) ∧
    (∀ i, ((Finset.univ : Finset (Fin 20)).filter (edge i)).card = 3) ∧
    graph.Connected ∧
    (∀ i j : Fin 20, i < j → LinearIndependent ℂ ![v i, v j]) ∧
    (∀ i j k l : Fin 20, i < j → j < k → k < l → Rank3of4 v i j k l)

theorem target : statement := sorry

end Statements.TightSpanningOrthRep3Cubic20
