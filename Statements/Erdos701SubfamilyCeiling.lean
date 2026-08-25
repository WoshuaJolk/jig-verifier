import Mathlib.Data.Finset.Card

namespace Statements.Erdos701SubfamilyCeiling

/-- Every finite subfamily has cardinality at most that of its ambient family. -/
abbrev statement : Prop :=
  ∀ {X : Type} [DecidableEq X] (F A : Finset (Finset X)),
    A ⊆ F → A.card ≤ F.card

theorem target : statement := sorry

end Statements.Erdos701SubfamilyCeiling
