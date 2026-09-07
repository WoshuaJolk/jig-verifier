import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Star.Basic
import Mathlib.LinearAlgebra.LinearIndependent.Basic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-! All even seed orders in complex dimension four. This is a strict
subcase of the corrected seed-supply route, not the mixed-dimensional root. -/
namespace Statements.QuarticSeedEvenOrders

def pair (v w : Fin 4 → ℂ) : ℂ := ∑ j, star (v j) * w j

def orthGraph {m : ℕ} (v : Fin m → Fin 4 → ℂ) : SimpleGraph (Fin m) :=
  SimpleGraph.fromRel fun i j => pair (v i) (v j) = 0

/-- Exact quartic seed obligations. -/
def Seed (m : ℕ) : Prop :=
  ∃ v : Fin m → Fin 4 → ℂ, ∃ N : Fin m → Finset (Fin m),
    (∀ i, v i ≠ 0) ∧
    (∀ i j, pair (v i) (v j) = 0 ↔ j ∈ N i) ∧
    (∀ i, (N i).card = 4) ∧
    (orthGraph v).Connected ∧
    (∀ S : Finset (Fin m), S.card ≤ 3 →
      LinearIndependent ℂ fun i : (S : Set (Fin m)) => v i) ∧
    (∀ S : Finset (Fin m), S.card = 5 → ∀ a : Fin 4 → ℂ, a ≠ 0 →
      ∃ i ∈ S, pair a (v i) ≠ 0)


abbrev statement : Prop := ∀ m : ℕ, 10 ≤ m → m % 2 = 0 → Seed m

theorem target : statement := sorry

end Statements.QuarticSeedEvenOrders
