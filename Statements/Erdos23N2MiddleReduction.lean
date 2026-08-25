import Mathlib.Combinatorics.SimpleGraph.Bipartite
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Finite

open SimpleGraph

namespace Statements.Erdos23N2MiddleReduction

open scoped Classical in
def BipartizesWithinFour {V : Type} [Fintype V] (G : SimpleGraph V) : Prop :=
  ∃ H : SimpleGraph V,
    H ≤ G ∧ H.IsBipartite ∧
      (G.edgeFinset \ H.edgeFinset).card ≤ 4

open scoped Classical in
def AtMostNine : Prop :=
  ∀ (V : Type) [Fintype V], Fintype.card V = 10 →
    ∀ G : SimpleGraph V, G.CliqueFree 3 →
      G.edgeFinset.card ≤ 9 → BipartizesWithinFour G

open scoped Classical in
def ExactlySixteen : Prop :=
  ∀ (V : Type) [Fintype V], Fintype.card V = 10 →
    ∀ G : SimpleGraph V, G.CliqueFree 3 →
      G.edgeFinset.card = 16 → BipartizesWithinFour G

open scoped Classical in
def ExactlySeventeen : Prop :=
  ∀ (V : Type) [Fintype V], Fintype.card V = 10 →
    ∀ G : SimpleGraph V, G.CliqueFree 3 →
      G.edgeFinset.card = 17 → BipartizesWithinFour G

open scoped Classical in
def AtLeastEighteen : Prop :=
  ∀ (V : Type) [Fintype V], Fintype.card V = 10 →
    ∀ G : SimpleGraph V, G.CliqueFree 3 →
      18 ≤ G.edgeFinset.card → BipartizesWithinFour G

open scoped Classical in
def MiddleRange : Prop :=
  ∀ (V : Type) [Fintype V], Fintype.card V = 10 →
    ∀ G : SimpleGraph V, G.CliqueFree 3 →
      10 ≤ G.edgeFinset.card → G.edgeFinset.card ≤ 15 →
        BipartizesWithinFour G

open scoped Classical in
def AllTenVertices : Prop :=
  ∀ (V : Type) [Fintype V], Fintype.card V = 10 →
    ∀ G : SimpleGraph V, G.CliqueFree 3 →
      BipartizesWithinFour G

/-- The four already verified outer edge ranges reduce the complete ten-vertex
case of Erdős 23 exactly to the six middle edge counts 10 through 15. -/
abbrev statement : Prop :=
  AtMostNine → ExactlySixteen → ExactlySeventeen → AtLeastEighteen →
    (AllTenVertices ↔ MiddleRange)

theorem target : statement := sorry

end Statements.Erdos23N2MiddleReduction
