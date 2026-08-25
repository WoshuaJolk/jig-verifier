import Mathlib.Combinatorics.SimpleGraph.Clique

namespace Submissions.Erdos80PositiveBook.Direct

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

lemma bookNumber_eq_zero_iff :
    bookNumber G = 0 ↔
      ∀ e ∈ G.edgeFinset, trianglesContaining G e = ∅ := by
  simp [bookNumber, Finset.card_eq_zero]

theorem proof :
    ∀ {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      EveryEdgeInTriangle G → G.edgeFinset.Nonempty → 0 < bookNumber G := by
  intro n G _ htri hedges
  rw [Nat.pos_iff_ne_zero]
  intro hz
  obtain ⟨e, he⟩ := hedges
  exact (htri e he).ne_empty ((bookNumber_eq_zero_iff G).mp hz e he)

end Submissions.Erdos80PositiveBook.Direct
