import Mathlib.Data.Set.Card
import Mathlib.SetTheory.Cardinal.Continuum

open Cardinal Ordinal
open scoped Cardinal

namespace Statements.Erdos70ContinuumTripleRamsey

/-- A ternary relation holds on all ordered triples of distinct elements of `s`. -/
def triplewise {α : Type*} (s : Set α) (r : α → α → α → Prop) : Prop :=
  ∀ ⦃x⦄, x ∈ s → ∀ ⦃y⦄, y ∈ s → ∀ ⦃z⦄, z ∈ s →
    x ≠ y → y ≠ z → x ≠ z → r x y z

/-- `ramsey3 α β c` is the two-colour partition relation `α → (β, c)₂³`, represented by a permutation-invariant predicate on ordered triples of distinct elements. -/
def ramsey3 (α β : Ordinal.{0}) (c : Cardinal.{0}) : Prop :=
  ∀ (isRed : α.ToType → α.ToType → α.ToType → Prop),
    (∀ x y z, x ≠ y → y ≠ z → x ≠ z →
      (isRed x y z ↔ isRed y x z) ∧
      (isRed x y z ↔ isRed x z y)) →
    (∃ s : Set α.ToType, typeLT s = β ∧ triplewise s isRed) ∨
    (∃ s : Set α.ToType, #s = c ∧
      triplewise s (fun x y z ↦ ¬ isRed x y z))

/-- Erdős Problem 70: the continuum has the indicated triple partition relation for every countable ordinal and every finite blue target. -/
abbrev statement : Prop :=
  ∀ (β : Ordinal.{0}) (n : ℕ),
    β.card ≤ ℵ₀ → 2 ≤ n →
      ramsey3 (𝔠).ord β n

theorem target : statement := sorry

end Statements.Erdos70ContinuumTripleRamsey
