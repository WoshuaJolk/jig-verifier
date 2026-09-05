import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Probability.Combinatorics.BinomialRandomGraph.Defs
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Tactic.NormNum

namespace Submissions.Erdos625ZeroGapBoundary.Declan

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

theorem gapEvent_zero (n : ℕ) : gapEvent 0 n = Set.univ := by
  apply Set.eq_univ_of_forall
  intro G
  obtain ⟨c⟩ := G.colorable_chromaticNumber_of_fintype
  refine ⟨ENat.toNat G.chromaticNumber, ⟨c, ?_⟩, by simp⟩
  intro i
  exact Or.inr (c.isIndepSet_colorClass i)

theorem proof : statement := by
  intro n
  rw [gapEvent_zero]
  simp

#print axioms proof
end Submissions.Erdos625ZeroGapBoundary.Declan

