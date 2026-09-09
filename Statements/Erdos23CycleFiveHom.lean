import Mathlib.Combinatorics.SimpleGraph.Bipartite

open SimpleGraph

namespace Statements.Erdos23CycleFiveHom

open scoped Classical in
/-- The sharp Erdős bound for every finite graph admitting a homomorphism to C5. -/
abbrev statement : Prop :=
∀ (n : ℕ) (V : Type) [Fintype V], Fintype.card V = 5 * n →
      ∀ G : SimpleGraph V,
        (∃ c : V → Fin 5, ∀ v w, G.Adj v w → c v + 1 = c w ∨ c w + 1 = c v) →
        ∃ H : SimpleGraph V,
          H ≤ G ∧ H.IsBipartite ∧ (G.edgeFinset \ H.edgeFinset).card ≤ n ^ 2

theorem target : statement := sorry

end Statements.Erdos23CycleFiveHom
