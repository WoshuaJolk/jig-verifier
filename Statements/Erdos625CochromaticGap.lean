import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Probability.Combinatorics.BinomialRandomGraph.Defs
import Mathlib.Topology.Instances.ENNReal.Lemmas

namespace Statements.Erdos625CochromaticGap

open Filter MeasureTheory

/-- A partition into at most k clique-or-independent parts, allowing empty fibers. -/
def CoColorable {n : ℕ} (G : SimpleGraph (Fin n)) (k : ℕ) : Prop :=
  ∃ color : Fin n → Fin k, ∀ c : Fin k,
    G.IsClique {v | color v = c} ∨ G.IsIndepSet {v | color v = c}

noncomputable def halfProbability : unitInterval :=
  ⟨(1 : ℝ) / 2, by constructor <;> norm_num⟩

/-- A co-coloring saves at least C parts relative to an optimal proper coloring. -/
def gapEvent (C n : ℕ) : Set (SimpleGraph (Fin n)) :=
  {G | ∃ k : ℕ, CoColorable G k ∧ k + C ≤ ENat.toNat G.chromaticNumber}

/-- The original full-sequence divergence question, in probability. -/
abbrev statement : Prop :=
  ∀ C : ℕ, Tendsto
    (fun n : ℕ => SimpleGraph.binomialRandom (Fin n) halfProbability (gapEvent C n))
    atTop (nhds (1 : ENNReal))

theorem target : statement := sorry

end Statements.Erdos625CochromaticGap
