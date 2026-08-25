import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.Topology.Algebra.Ring.Real

open Filter
open scoped Topology

/-!
# Erdős problem 627

Let `f(n)` be the maximum of `χ(G) / ω(G)` over all graphs on `n`
vertices. Does `f(n) / (n / (log₂ n)^2)` have a limit?
-/

namespace Statements.Erdos627ChromaticCliqueRatioLimit

noncomputable def ratio {n : ℕ} (G : SimpleGraph (Fin n)) : ℝ :=
  (ENat.toNat G.chromaticNumber : ℝ) / G.cliqueNum

noncomputable def f (n : ℕ) : ℝ :=
  sSup {x : ℝ | ∃ G : SimpleGraph (Fin n), x = ratio G}

noncomputable def normalized (n : ℕ) : ℝ :=
  f n / ((n : ℝ) / (Real.logb 2 n) ^ 2)

abbrev statement : Prop :=
  ∃ L : ℝ, Tendsto normalized atTop (𝓝 L)

theorem target : statement := sorry

end Statements.Erdos627ChromaticCliqueRatioLimit
