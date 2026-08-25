import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Combinatorics.SimpleGraph.Subgraph
import Mathlib.Data.Set.Card
import Mathlib.SetTheory.Cardinal.Aleph

open Cardinal

namespace Statements.Erdos75AlephOneIndependentSets

/-- Cardinal-valued chromatic number, copied from Formal Conjectures because
Jig's pinned Mathlib predates that library declaration. -/
noncomputable def chromaticCardinal {V : Type} (G : SimpleGraph V) : Cardinal.{0} :=
  sInf {κ : Cardinal.{0} |
    ∃ (C : Type) (_ : Cardinal.mk C = κ), Nonempty (G.Coloring C)}

/-- Erdős Problem 75: an `ℵ₁`-chromatic graph on `ℵ₁` vertices whose
large finite subgraphs have independent sets of size `> n^(1-ε)`. -/
abbrev statement : Prop :=
  ∃ (V : Type) (G : SimpleGraph V),
    chromaticCardinal G = aleph.{0} 1 ∧
    #V = aleph.{0} 1 ∧
    ∀ ε > (0 : ℝ),
      ∀ᶠ (n : ℕ) in Filter.atTop, ∀ (H : G.Subgraph),
        H.verts.ncard = n →
        ∃ I : Finset V,
          (I : Set V) ⊆ H.verts ∧
          G.IsIndepSet (I : Set V) ∧
          (I.card : ℝ) > (n : ℝ) ^ (1 - ε)

theorem target : statement := sorry

end Statements.Erdos75AlephOneIndependentSets
