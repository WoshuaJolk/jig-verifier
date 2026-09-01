import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Star.Basic
import Mathlib.LinearAlgebra.LinearIndependent.Basic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph

namespace Statements.TightSpanningOrthRep3Cubic16

/-- Symmetric edge relation of an explicit connected C4-free cubic graph on 16 vertices. -/
def edge (i j : Fin 16) : Prop :=
  (min i.val j.val, max i.val j.val) ∈
    [(0,1),(0,11),(0,12),(1,3),(1,9),(2,7),(2,8),(2,12),(3,6),(3,15),(4,6),(4,9),(4,10),(5,8),(5,11),(5,13),(6,7),(7,11),(8,10),(9,13),(10,14),(12,15),(13,14),(14,15)]

instance edgeDecidable (i j : Fin 16) : Decidable (edge i j) := by
  unfold edge
  infer_instance

def graph : SimpleGraph (Fin 16) := SimpleGraph.fromRel edge

def pair (x y : Fin 3 → ℂ) : ℂ := ∑ r, star (x r) * y r

def Rank3of4 (v : Fin 16 → Fin 3 → ℂ) (i j k l : Fin 16) : Prop :=
  LinearIndependent ℂ ![v i, v j, v k] ∨
  LinearIndependent ℂ ![v i, v j, v l] ∨
  LinearIndependent ℂ ![v i, v k, v l] ∨
  LinearIndependent ℂ ![v j, v k, v l]

/-- An explicit connected c4-free cubic graph on 16 vertices, realized as the exact Hermitian orthogonality
graph of 16 nonzero vectors in C^3: connected, cubic, tight (every two vectors
independent) and 4-spanning (no four in a common plane) - the m = 16 instance of
the k = 3 row of the seed hypothesis (`SeedSufficesForMixedMinUPB`), with the
graph prescribed. -/
abbrev statement : Prop :=
  ∃ v : Fin 16 → Fin 3 → ℂ,
    (∀ i, v i ≠ 0) ∧
    (∀ i j, pair (v i) (v j) = 0 ↔ edge i j) ∧
    (∀ i, ((Finset.univ : Finset (Fin 16)).filter (edge i)).card = 3) ∧
    graph.Connected ∧
    (∀ i j : Fin 16, i < j → LinearIndependent ℂ ![v i, v j]) ∧
    (∀ i j k l : Fin 16, i < j → j < k → k < l → Rank3of4 v i j k l)

theorem target : statement := sorry

end Statements.TightSpanningOrthRep3Cubic16
