import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Star.Basic
import Mathlib.LinearAlgebra.LinearIndependent.Basic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph

namespace Statements.TightSpanningOrthRep3Cubic18

/-- Symmetric edge relation of an explicit connected C4-free cubic graph on 18 vertices. -/
def edge (i j : Fin 18) : Prop :=
  (min i.val j.val, max i.val j.val) ∈
    [(0,4),(0,6),(0,9),(1,2),(1,3),(1,16),(2,11),(2,16),(3,5),(3,15),(4,15),(4,16),(5,10),(5,13),(6,7),(6,14),(7,8),(7,12),(8,9),(8,17),(9,13),(10,14),(10,17),(11,12),(11,14),(12,13),(15,17)]

instance edgeDecidable (i j : Fin 18) : Decidable (edge i j) := by
  unfold edge
  infer_instance

def graph : SimpleGraph (Fin 18) := SimpleGraph.fromRel edge

def pair (x y : Fin 3 → ℂ) : ℂ := ∑ r, star (x r) * y r

def Rank3of4 (v : Fin 18 → Fin 3 → ℂ) (i j k l : Fin 18) : Prop :=
  LinearIndependent ℂ ![v i, v j, v k] ∨
  LinearIndependent ℂ ![v i, v j, v l] ∨
  LinearIndependent ℂ ![v i, v k, v l] ∨
  LinearIndependent ℂ ![v j, v k, v l]

/-- An explicit connected c4-free cubic graph on 18 vertices, realized as the exact Hermitian orthogonality
graph of 18 nonzero vectors in C^3: connected, cubic, tight (every two vectors
independent) and 4-spanning (no four in a common plane) - the m = 18 instance of
the k = 3 row of the seed hypothesis (`SeedSufficesForMixedMinUPB`), with the
graph prescribed. -/
abbrev statement : Prop :=
  ∃ v : Fin 18 → Fin 3 → ℂ,
    (∀ i, v i ≠ 0) ∧
    (∀ i j, pair (v i) (v j) = 0 ↔ edge i j) ∧
    (∀ i, ((Finset.univ : Finset (Fin 18)).filter (edge i)).card = 3) ∧
    graph.Connected ∧
    (∀ i j : Fin 18, i < j → LinearIndependent ℂ ![v i, v j]) ∧
    (∀ i j k l : Fin 18, i < j → j < k → k < l → Rank3of4 v i j k l)

theorem target : statement := sorry

end Statements.TightSpanningOrthRep3Cubic18
