import Mathlib.Data.Finset.Card

namespace Statements.Erdos701ChvatalStar

/-- A finite family is hereditary when it contains every subset of each member. -/
def Hereditary {X : Type} [DecidableEq X] (F : Finset (Finset X)) : Prop :=
  ∀ A ∈ F, ∀ B : Finset X, B ⊆ A → B ∈ F

/-- A family is intersecting when any two members meet. In particular, the
empty set cannot be a member of an intersecting family. -/
def Intersecting {X : Type} [DecidableEq X] (A : Finset (Finset X)) : Prop :=
  ∀ S ∈ A, ∀ T ∈ A, (S ∩ T).Nonempty

/-- Chvátal's conjecture: every finite hereditary family has a largest
intersecting subfamily no larger than one of its stars. -/
abbrev statement : Prop :=
  ∀ {X : Type} [Fintype X] [DecidableEq X] [Nonempty X],
    ∀ F : Finset (Finset X), Hereditary F →
      ∃ x : X, ∀ A : Finset (Finset X), A ⊆ F → Intersecting A →
        A.card ≤ (F.filter fun S => x ∈ S).card

theorem target : statement := sorry

end Statements.Erdos701ChvatalStar
