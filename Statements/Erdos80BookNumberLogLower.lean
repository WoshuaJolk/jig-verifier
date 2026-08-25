import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Order.Lattice.Nat

namespace Statements.Erdos80BookNumberLogLower

open Filter Finset SimpleGraph
open scoped Topology

notation f " ≫ " g =>
  Asymptotics.IsBigO Filter.atTop (g : ℕ → ℝ) (f : ℕ → ℝ)

open scoped Classical in
/-- The triangles of `G` containing the edge `uv`. -/
noncomputable def trianglesContaining {α : Type*} [Fintype α]
    (G : SimpleGraph α) (uv : Sym2 α) : Finset (Finset α) :=
  (G.cliqueFinset 3).filter (fun t ↦ uv.toFinset ⊆ t)

variable {α : Type*} [Fintype α] [DecidableEq α]
    (G : SimpleGraph α) [DecidableRel G.Adj]

noncomputable def bookNumber : ℕ :=
  G.edgeFinset.sup fun e => #(trianglesContaining G e)

def EveryEdgeInTriangle : Prop :=
  ∀ e ∈ G.edgeFinset, (trianglesContaining G e).Nonempty

def Admissible (c : ℝ) {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] : Prop :=
  c * (n : ℝ) ^ 2 ≤ #G.edgeFinset ∧ EveryEdgeInTriangle G

open Classical in
noncomputable def f (c : ℝ) (n : ℕ) : ℕ :=
  sInf {m | ∃ G : SimpleGraph (Fin n), Admissible c G ∧ bookNumber G = m}

/-- The open logarithmic lower-bound question in Erdős problem 80. -/
abbrev statement : Prop :=
  ∀ c : ℝ, 0 < c → c < 1 / 2 →
    (fun n : ℕ ↦ (f c n : ℝ)) ≫ (fun n : ℕ ↦ Real.log n)

theorem target : statement := sorry

end Statements.Erdos80BookNumberLogLower
