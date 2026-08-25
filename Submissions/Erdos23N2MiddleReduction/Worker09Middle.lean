import Mathlib.Combinatorics.SimpleGraph.Bipartite
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Tactic

open SimpleGraph

namespace Submissions.Erdos23N2MiddleReduction.Worker09Middle

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

open scoped Classical in
theorem proof :
    AtMostNine → ExactlySixteen → ExactlySeventeen → AtLeastEighteen →
      (AllTenVertices ↔ MiddleRange) := by
  intro hsmall h16 h17 hdense
  constructor
  · intro hall V _ hcard G htri _ _
    exact hall V hcard G htri
  · intro hmiddle V _ hcard G htri
    by_cases hsmall' : G.edgeFinset.card ≤ 9
    · exact hsmall V hcard G htri hsmall'
    by_cases hmiddle' : G.edgeFinset.card ≤ 15
    · exact hmiddle V hcard G htri (by omega) hmiddle'
    by_cases h16' : G.edgeFinset.card = 16
    · exact h16 V hcard G htri h16'
    by_cases h17' : G.edgeFinset.card = 17
    · exact h17 V hcard G htri h17'
    · exact hdense V hcard G htri (by omega)

end Submissions.Erdos23N2MiddleReduction.Worker09Middle
