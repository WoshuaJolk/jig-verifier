import Mathlib.SetTheory.Cardinal.Continuum

open Cardinal Ordinal
open scoped Cardinal

namespace Statements.Erdos70FiniteLinkObstruction

def symmetric3 {α : Type*} (r : α → α → α → Prop) : Prop :=
  ∀ x y z, x ≠ y → y ≠ z → x ≠ z →
    (r x y z ↔ r y x z) ∧ (r x y z ↔ r x z y)

def pivotCover {α : Type*} (isRed : α → α → α → Prop) : Prop :=
  ∀ x a b c,
    x ≠ a → x ≠ b → x ≠ c → a ≠ b → a ≠ c → b ≠ c →
    ¬ isRed x a b → ¬ isRed x a c → ¬ isRed x b c →
    isRed a b c

/-- The forbidden triangle patterns in a complete-bipartite graph: exactly
one edge or all three edges. -/
def forbiddenColors (p q r : Prop) : Prop :=
  (p ∧ ¬ q ∧ ¬ r) ∨ (¬ p ∧ q ∧ ¬ r) ∨
  (¬ p ∧ ¬ q ∧ r) ∨ (p ∧ q ∧ r)

def linkForbidden {α : Type*} (isRed : α → α → α → Prop)
    (x a b c : α) : Prop :=
  forbiddenColors (isRed x a b) (isRed x a c) (isRed x b c)

/-- A three-edge graph is a complete-bipartite cut exactly when it avoids
`forbiddenColors`. Moreover, under cross-pivot coherence and `pivotCover`,
every four distinct vertices exhibit a forbidden link triangle at one of
their four pivots. -/
abbrev statement : Prop :=
  (∀ p q r : Prop,
    (∃ u v w : Bool,
      (p ↔ u ≠ v) ∧ (q ↔ u ≠ w) ∧ (r ↔ v ≠ w)) ↔
      ¬ forbiddenColors p q r) ∧
  ∀ (isRed : (𝔠 : Cardinal.{0}).ord.ToType → (𝔠 : Cardinal.{0}).ord.ToType →
      (𝔠 : Cardinal.{0}).ord.ToType → Prop),
    symmetric3 isRed → pivotCover isRed →
    ∀ x a b c, x ≠ a → x ≠ b → x ≠ c →
      a ≠ b → a ≠ c → b ≠ c →
      linkForbidden isRed x a b c ∨
      linkForbidden isRed a x b c ∨
      linkForbidden isRed b x a c ∨
      linkForbidden isRed c x a b

theorem target : statement := sorry

end Statements.Erdos70FiniteLinkObstruction
