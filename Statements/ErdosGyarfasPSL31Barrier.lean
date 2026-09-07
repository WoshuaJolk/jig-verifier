import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Paths

namespace Statements.ErdosGyarfasPSL31Barrier

def HasCycleLength {n : ℕ} (G : SimpleGraph (Fin n)) (l : ℕ) : Prop :=
  ∃ (v : Fin n) (c : G.Walk v v), c.IsCycle ∧ c.length = l

abbrev statement : Prop :=
  ∃ G : SimpleGraph (Fin 14880),
    (∀ v : Fin 14880, G.degree v = 3) ∧
    ¬ HasCycleLength G 4 ∧
    ¬ HasCycleLength G 8 ∧
    ¬ HasCycleLength G 16 ∧
    ¬ HasCycleLength G 32 ∧
    HasCycleLength G 64

theorem target : statement := sorry

end Statements.ErdosGyarfasPSL31Barrier
