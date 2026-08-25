import Mathlib.Data.Set.Card
import Mathlib.SetTheory.Cardinal.Continuum

open Cardinal Ordinal
open scoped Cardinal

namespace Statements.Erdos70LinkHittingBarrier

abbrev Vertex := Bool × ℕ

/-- A constant family of complete bipartite red link graphs. -/
def redLink (_pivot x y : Vertex) : Prop := x.1 ≠ y.1

def twoBlock (A B : Set ℕ) : Set Vertex :=
  {x | (x.1 = false ∧ x.2 ∈ A) ∨ (x.1 = true ∧ x.2 ∈ B)}

def linkRedEdge (pivot : Vertex) (s : Set Vertex) : Prop :=
  ∃ x ∈ s, ∃ y ∈ s, x ≠ y ∧ redLink pivot x y

def pairwiseOn (s : Set Vertex) (r : Vertex → Vertex → Prop) : Prop :=
  ∀ ⦃x⦄, x ∈ s → ∀ ⦃y⦄, y ∈ s → x ≠ y → r x y

/-- Link hitting alone cannot drive the desired fusion. On an explicit
`ω·2`-ordered vertex set there is a family of links which hits every canonical
two-block thinning, has neither a blue two-block thinning nor even a red
triangle, and fails exactly the cross-pivot coherence forced by a symmetric
triple colouring. -/
abbrev statement : Prop :=
  Ordinal.type (Prod.Lex (· < · : Bool → Bool → Prop)
    (· < · : ℕ → ℕ → Prop)) = ω * 2 ∧
  (∀ pivot A B, A.Infinite → B.Infinite →
    linkRedEdge pivot (twoBlock A B)) ∧
  (∀ pivot A B, A.Infinite → B.Infinite →
    ¬ pairwiseOn (twoBlock A B) (fun x y ↦ ¬ redLink pivot x y)) ∧
  (∀ pivot x y z, x ≠ y → y ≠ z → x ≠ z →
    ¬ (redLink pivot x y ∧ redLink pivot x z ∧ redLink pivot y z)) ∧
  (∃ x y z, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧
    ¬ (redLink x y z ↔ redLink y x z))

theorem target : statement := sorry

end Statements.Erdos70LinkHittingBarrier
