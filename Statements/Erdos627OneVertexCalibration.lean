import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Topology.Algebra.Ring.Real

namespace Statements.Erdos627OneVertexCalibration

noncomputable def ratio {n : ℕ} (G : SimpleGraph (Fin n)) : ℝ :=
  (ENat.toNat G.chromaticNumber : ℝ) / G.cliqueNum

abbrev statement : Prop :=
  ratio (⊤ : SimpleGraph (Fin 1)) = 1

theorem target : statement := sorry

end Statements.Erdos627OneVertexCalibration
