import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Star.Basic
import Mathlib.LinearAlgebra.LinearIndependent.Basic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph

namespace Statements.TightSpanningOrthRep3Cubic14

/-- Symmetric edge relation of an explicit connected C4-free cubic graph on 14 vertices. -/
def edge (i j : Fin 14) : Prop :=
  (min i.val j.val, max i.val j.val) ∈
    [(0,4),(0,8),(0,12),(1,5),(1,6),(1,9),(2,3),(2,9),(2,11),(3,7),(3,8),(4,6),(4,11),(5,12),(5,13),(6,7),(7,10),(8,12),(9,10),(10,13),(11,13)]

instance edgeDecidable (i j : Fin 14) : Decidable (edge i j) := by
  unfold edge
  infer_instance

def graph : SimpleGraph (Fin 14) := SimpleGraph.fromRel edge

def pair (x y : Fin 3 → ℂ) : ℂ := ∑ r, star (x r) * y r

def Rank3of4 (v : Fin 14 → Fin 3 → ℂ) (i j k l : Fin 14) : Prop :=
  LinearIndependent ℂ ![v i, v j, v k] ∨
  LinearIndependent ℂ ![v i, v j, v l] ∨
  LinearIndependent ℂ ![v i, v k, v l] ∨
  LinearIndependent ℂ ![v j, v k, v l]

/-- An explicit connected c4-free cubic graph on 14 vertices, realized as the exact Hermitian orthogonality
graph of 14 nonzero vectors in C^3: connected, cubic, tight (every two vectors
independent) and 4-spanning (no four in a common plane) - the m = 14 instance of
the k = 3 row of the seed hypothesis (`SeedSufficesForMixedMinUPB`), with the
graph prescribed. -/
abbrev statement : Prop :=
  ∃ v : Fin 14 → Fin 3 → ℂ,
    (∀ i, v i ≠ 0) ∧
    (∀ i j, pair (v i) (v j) = 0 ↔ edge i j) ∧
    (∀ i, ((Finset.univ : Finset (Fin 14)).filter (edge i)).card = 3) ∧
    graph.Connected ∧
    (∀ i j : Fin 14, i < j → LinearIndependent ℂ ![v i, v j]) ∧
    (∀ i j k l : Fin 14, i < j → j < k → k < l → Rank3of4 v i j k l)

theorem target : statement := sorry

end Statements.TightSpanningOrthRep3Cubic14
