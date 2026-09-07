import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Paths

namespace Statements.ErdosGyarfasCubicOrder32

def HasCycleLength (G : SimpleGraph (Fin 32)) (l : ℕ) : Prop :=
  ∃ (v : Fin 32) (c : G.Walk v v), c.IsCycle ∧ c.length = l

abbrev statement : Prop :=
  ∀ G : SimpleGraph (Fin 32),
    (∀ v : Fin 32, @SimpleGraph.degree _ G v (Fintype.ofFinite _) = 3) →
    HasCycleLength G 4 ∨ HasCycleLength G 8 ∨
      HasCycleLength G 16 ∨ HasCycleLength G 32

theorem target : statement := sorry

end Statements.ErdosGyarfasCubicOrder32
