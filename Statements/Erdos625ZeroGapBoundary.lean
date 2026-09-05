import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Probability.Combinatorics.BinomialRandomGraph.Defs
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Tactic.NormNum

namespace Statements.Erdos625ZeroGapBoundary

open Filter MeasureTheory

def CoColorable {n : ℕ} (G : SimpleGraph (Fin n)) (k : ℕ) : Prop :=
  ∃ color : Fin n → Fin k,
    ∀ c, G.IsClique {v | color v = c} ∨ G.IsIndepSet {v | color v = c}

noncomputable def halfProbability : unitInterval :=
  ⟨(1 : ℝ) / 2, by constructor <;> norm_num⟩

def gapEvent (C n : ℕ) : Set (SimpleGraph (Fin n)) :=
  {G | ∃ k : ℕ, CoColorable G k ∧ k + C ≤ ENat.toNat G.chromaticNumber}

abbrev statement : Prop :=
  ∀ n : ℕ, SimpleGraph.binomialRandom (Fin n) halfProbability (gapEvent 0 n) = 1

theorem target : statement := sorry

end Statements.Erdos625ZeroGapBoundary
