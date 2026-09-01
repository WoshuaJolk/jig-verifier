import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Star.Basic
import Mathlib.LinearAlgebra.LinearIndependent.Basic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph

namespace Statements.TightSpanningOrthRep3Cubic22

/-- Symmetric edge relation of an explicit connected C4-free cubic graph on 22 vertices. -/
def edge (i j : Fin 22) : Prop :=
  (min i.val j.val, max i.val j.val) ∈
    [(0,5),(0,17),(0,18),(1,12),(1,16),(1,18),(2,3),(2,13),(2,15),(3,14),(3,15),(4,5),(4,6),(4,7),(5,13),(6,18),(6,19),(7,10),(7,11),(8,12),(8,15),(8,21),(9,17),(9,20),(9,21),(10,13),(10,20),(11,16),(11,17),(12,14),(14,19),(16,21),(19,20)]

instance edgeDecidable (i j : Fin 22) : Decidable (edge i j) := by
  unfold edge
  infer_instance

def graph : SimpleGraph (Fin 22) := SimpleGraph.fromRel edge

def pair (x y : Fin 3 → ℂ) : ℂ := ∑ r, star (x r) * y r

def Rank3of4 (v : Fin 22 → Fin 3 → ℂ) (i j k l : Fin 22) : Prop :=
  LinearIndependent ℂ ![v i, v j, v k] ∨
  LinearIndependent ℂ ![v i, v j, v l] ∨
  LinearIndependent ℂ ![v i, v k, v l] ∨
  LinearIndependent ℂ ![v j, v k, v l]

/-- An explicit connected c4-free cubic graph on 22 vertices, realized as the exact Hermitian orthogonality
graph of 22 nonzero vectors in C^3: connected, cubic, tight (every two vectors
independent) and 4-spanning (no four in a common plane) - the m = 22 instance of
the k = 3 row of the seed hypothesis (`SeedSufficesForMixedMinUPB`), with the
graph prescribed. -/
abbrev statement : Prop :=
  ∃ v : Fin 22 → Fin 3 → ℂ,
    (∀ i, v i ≠ 0) ∧
    (∀ i j, pair (v i) (v j) = 0 ↔ edge i j) ∧
    (∀ i, ((Finset.univ : Finset (Fin 22)).filter (edge i)).card = 3) ∧
    graph.Connected ∧
    (∀ i j : Fin 22, i < j → LinearIndependent ℂ ![v i, v j]) ∧
    (∀ i j k l : Fin 22, i < j → j < k → k < l → Rank3of4 v i j k l)

theorem target : statement := sorry

end Statements.TightSpanningOrthRep3Cubic22
