import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Star.Basic
import Mathlib.LinearAlgebra.LinearIndependent.Basic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph

/-!
# ThreeBasisSeedK4M12

The missing connected seed in dimension four and order twelve.  The graph is
three four-cliques plus a perfect matching split two edges between each pair of
cliques.  Thus it is connected and 4-regular.  The claimed representation is
tight (every triple is independent) and five-spanning.
-/

namespace Statements.ThreeBasisSeedK4M12

def pair (x y : Fin 4 → ℂ) : ℂ := ∑ r, star (x r) * y r

def crossMatch (i j : Fin 12) : Prop :=
  (i.val = 0 ∧ j.val = 4) ∨ (i.val = 4 ∧ j.val = 0) ∨
  (i.val = 1 ∧ j.val = 5) ∨ (i.val = 5 ∧ j.val = 1) ∨
  (i.val = 2 ∧ j.val = 10) ∨ (i.val = 10 ∧ j.val = 2) ∨
  (i.val = 3 ∧ j.val = 11) ∨ (i.val = 11 ∧ j.val = 3) ∨
  (i.val = 6 ∧ j.val = 8) ∨ (i.val = 8 ∧ j.val = 6) ∨
  (i.val = 7 ∧ j.val = 9) ∨ (i.val = 9 ∧ j.val = 7)

def edge (i j : Fin 12) : Prop :=
  i ≠ j ∧ (i.val / 4 = j.val / 4 ∨ crossMatch i j)

instance crossMatchDecidable (i j : Fin 12) : Decidable (crossMatch i j) := by
  unfold crossMatch
  infer_instance

instance edgeDecidable (i j : Fin 12) : Decidable (edge i j) := by
  unfold edge
  infer_instance

def graph : SimpleGraph (Fin 12) := SimpleGraph.fromRel edge

def Rank4of5 (v : Fin 12 → Fin 4 → ℂ) (i j k l t : Fin 12) : Prop :=
  LinearIndependent ℂ ![v i, v j, v k, v l] ∨
  LinearIndependent ℂ ![v i, v j, v k, v t] ∨
  LinearIndependent ℂ ![v i, v j, v l, v t] ∨
  LinearIndependent ℂ ![v i, v k, v l, v t] ∨
  LinearIndependent ℂ ![v j, v k, v l, v t]

abbrev statement : Prop :=
  ∃ v : Fin 12 → Fin 4 → ℂ,
    (∀ i, v i ≠ 0) ∧
    (∀ i j, pair (v i) (v j) = 0 ↔ edge i j) ∧
    (∀ i, ((Finset.univ : Finset (Fin 12)).filter (edge i)).card = 4) ∧
    graph.Connected ∧
    (∀ i j k : Fin 12, i < j → j < k →
      LinearIndependent ℂ ![v i, v j, v k]) ∧
    (∀ i j k l t : Fin 12, i < j → j < k → k < l → l < t →
      Rank4of5 v i j k l t)

theorem target : statement := sorry

end Statements.ThreeBasisSeedK4M12
