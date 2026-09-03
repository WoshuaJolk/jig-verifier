import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Hasse
import Mathlib.Data.List.Chain

namespace Statements.Erdos583PathGraphDecomposition

def IsPath {V : Type} (G : SimpleGraph V) (p : List V) : Prop :=
  p.Nodup ∧ p.Chain' G.Adj

def PathUses {V : Type} (p : List V) (a b : V) : Prop :=
  ∃ l r : List V,
    p = l ++ a :: b :: r ∨ p = l ++ b :: a :: r

def IsPathDecomposition {V : Type} [DecidableEq V]
    (G : SimpleGraph V) (paths : Finset (List V)) : Prop :=
  (∀ p ∈ paths, IsPath G p) ∧
  ∀ ⦃a b : V⦄, G.Adj a b →
    ∃! p : List V, p ∈ paths ∧ PathUses p a b

/-- Every standard path graph `pathGraph (n+1)` on `Fin (n+1)` (Mathlib's Hasse
diagram of the successor order) is connected and admits a decomposition into
its single Hamiltonian path, meeting Gallai's ceiling with room to spare. -/
abbrev statement : Prop :=
  ∀ n : ℕ, (SimpleGraph.pathGraph (n + 1)).Connected →
    ∃ paths : Finset (List (Fin (n + 1))),
      paths.card ≤ ((n + 1) + 1) / 2 ∧
      IsPathDecomposition (SimpleGraph.pathGraph (n + 1)) paths

theorem target : statement := sorry

end Statements.Erdos583PathGraphDecomposition
