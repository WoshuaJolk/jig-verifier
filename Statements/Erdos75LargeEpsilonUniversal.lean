import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Combinatorics.SimpleGraph.Subgraph
import Mathlib.Data.Set.Card

namespace Statements.Erdos75LargeEpsilonUniversal

/-- The `ε > 1` range of Erdős 75 is automatic for every graph: eventually,
a singleton independent set exceeds `n^(1-ε)`. -/
abbrev statement : Prop :=
  ∀ (V : Type) (G : SimpleGraph V) (ε : ℝ), 1 < ε →
    ∀ᶠ (n : ℕ) in Filter.atTop, ∀ (H : G.Subgraph),
      H.verts.ncard = n →
      ∃ I : Finset V,
        (I : Set V) ⊆ H.verts ∧
        G.IsIndepSet (I : Set V) ∧
        (I.card : ℝ) > (n : ℝ) ^ (1 - ε)

theorem target : statement := sorry

end Statements.Erdos75LargeEpsilonUniversal
