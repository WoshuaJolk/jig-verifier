import Mathlib.Combinatorics.SimpleGraph.Clique

namespace Statements.Erdos80PositiveBook

open Finset SimpleGraph

open scoped Classical in
noncomputable def trianglesContaining {α : Type*} [Fintype α]
    (G : SimpleGraph α) (uv : Sym2 α) : Finset (Finset α) :=
  (G.cliqueFinset 3).filter (fun t ↦ uv.toFinset ⊆ t)

variable {α : Type*} [Fintype α] [DecidableEq α]
    (G : SimpleGraph α) [DecidableRel G.Adj]

noncomputable def bookNumber : ℕ :=
  G.edgeFinset.sup fun e => #(trianglesContaining G e)

def EveryEdgeInTriangle : Prop :=
  ∀ e ∈ G.edgeFinset, (trianglesContaining G e).Nonempty

/-- A nonempty graph whose every edge lies in a triangle has a positive book. -/
abbrev statement : Prop :=
  ∀ {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
    EveryEdgeInTriangle G → G.edgeFinset.Nonempty → 0 < bookNumber G

theorem target : statement := sorry

end Statements.Erdos80PositiveBook
