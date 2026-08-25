import Mathlib.Data.Set.Card
import Mathlib.SetTheory.Cardinal.Continuum

open Cardinal Ordinal
open scoped Cardinal

namespace Statements.Erdos70PolarizedOverlapPattern

abbrev Vertex := Bool × ℕ

def bluePattern (x y z : Vertex) : Prop :=
  (x.1 = false ∧ y.1 = true ∧ z.1 = true) ∨
  (y.1 = false ∧ x.1 = true ∧ z.1 = true) ∨
  (z.1 = false ∧ x.1 = true ∧ y.1 = true)

/-- Blue exactly on triples with one first-block and two second-block points. -/
def isRed (x y z : Vertex) : Prop := ¬ bluePattern x y z

def symmetric3 {α : Type*} (r : α → α → α → Prop) : Prop :=
  ∀ x y z, x ≠ y → y ≠ z → x ≠ z →
    (r x y z ↔ r y x z) ∧ (r x y z ↔ r x z y)

def pivotCover {α : Type*} (r : α → α → α → Prop) : Prop :=
  ∀ x a b c,
    x ≠ a → x ≠ b → x ≠ c → a ≠ b → a ≠ c → b ≠ c →
    ¬ r x a b → ¬ r x a c → ¬ r x b c → r a b c

def forbiddenColors (p q r : Prop) : Prop :=
  (p ∧ ¬ q ∧ ¬ r) ∨ (¬ p ∧ q ∧ ¬ r) ∨
  (¬ p ∧ ¬ q ∧ r) ∨ (p ∧ q ∧ r)

def linkForbidden (x a b c : Vertex) : Prop :=
  forbiddenColors (isRed x a b) (isRed x a c) (isRed x b c)

def twoBlock (A B : Set ℕ) : Set Vertex :=
  {x | (x.1 = false ∧ x.2 ∈ A) ∨ (x.1 = true ∧ x.2 ∈ B)}

def triplewise {α : Type*} (s : Set α) (r : α → α → α → Prop) : Prop :=
  ∀ ⦃x⦄, x ∈ s → ∀ ⦃y⦄, y ∈ s → ∀ ⦃z⦄, z ∈ s →
    x ≠ y → y ≠ z → x ≠ z → r x y z

/-- Polarized stabilization plus overlap compatibility alone does not force a
red `ω·2`: this coherent `pivotCover` colouring has a constant 2+2 pattern.
On every 2+2 set exactly the second-block pivots have the one-red forbidden
link triangle, this remains true on all overlapping 2+2 sets, and every
infinite two-block thinning still contains a blue triple. -/
abbrev statement : Prop :=
  Ordinal.type (Prod.Lex (· < · : Bool → Bool → Prop)
    (· < · : ℕ → ℕ → Prop)) = ω * 2 ∧
  symmetric3 isRed ∧ pivotCover isRed ∧
  (∀ a₁ a₂ b₁ b₂ : ℕ, a₁ ≠ a₂ → b₁ ≠ b₂ →
    isRed (false, a₁) (false, a₂) (true, b₁) ∧
    isRed (false, a₁) (false, a₂) (true, b₂) ∧
    ¬ isRed (false, a₁) (true, b₁) (true, b₂) ∧
    ¬ isRed (false, a₂) (true, b₁) (true, b₂) ∧
    ¬ linkForbidden (false, a₁) (false, a₂) (true, b₁) (true, b₂) ∧
    ¬ linkForbidden (false, a₂) (false, a₁) (true, b₁) (true, b₂) ∧
    linkForbidden (true, b₁) (false, a₁) (false, a₂) (true, b₂) ∧
    linkForbidden (true, b₂) (false, a₁) (false, a₂) (true, b₁)) ∧
  (∀ A B : Set ℕ, A.Infinite → B.Infinite →
    ¬ triplewise (twoBlock A B) isRed)

theorem target : statement := sorry

end Statements.Erdos70PolarizedOverlapPattern
