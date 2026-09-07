import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Paths

namespace Statements.ErdosGyarfasOrder32

def HasCycleLength (G : SimpleGraph (Fin 32)) (l : ℕ) : Prop :=
  ∃ (v : Fin 32) (c : G.Walk v v), c.IsCycle ∧ c.length = l

/-- Every simple graph of order 32 and minimum degree at least three has a
cycle of one of the four possible power-of-two lengths. -/
abbrev statement : Prop :=
  ∀ G : SimpleGraph (Fin 32),
    (∀ v : Fin 32, 3 ≤ @SimpleGraph.degree _ G v (Fintype.ofFinite _)) →
    HasCycleLength G 4 ∨ HasCycleLength G 8 ∨
      HasCycleLength G 16 ∨ HasCycleLength G 32

theorem target : statement := by
  sorry

end Statements.ErdosGyarfasOrder32
