import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Topology.Algebra.Ring.Real

namespace Submissions.Erdos627OneVertexCalibration.FalsePremise

noncomputable def ratio {n : ℕ} (G : SimpleGraph (Fin n)) : ℝ :=
  (ENat.toNat G.chromaticNumber : ℝ) / G.cliqueNum

theorem proof :
    False → ratio (⊤ : SimpleGraph (Fin 1)) = 1 := by
  intro h
  exact h.elim

end Submissions.Erdos627OneVertexCalibration.FalsePremise
