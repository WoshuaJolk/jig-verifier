import Mathlib.Algebra.Group.Pointwise.Finset.Basic
import Mathlib.Data.Nat.Prime.Basic

open scoped Pointwise

namespace Statements.Erdos52MixedCubeGrowth

private def scale (q : ℕ) (S : Finset ℕ) : Finset ℕ :=
  S.image fun x => q * x

/--
Lossless sibling aggregation for one prime-valuation coordinate.  If both
layers are `q`-free, the products with valuation zero, one, and two are
disjoint and their cardinalities add exactly.
-/
abbrev statement : Prop :=
  ∀ (q : ℕ) (A₀ A₁ : Finset ℕ), q.Prime →
    (∀ x ∈ A₀, ¬q ∣ x) →
    (∀ x ∈ A₁, ¬q ∣ x) →
    let A := A₀ ∪ scale q A₁
    (A * A).card =
      (A₀ * A₀).card + (A₀ * A₁).card + (A₁ * A₁).card

theorem target : statement := sorry

end Statements.Erdos52MixedCubeGrowth
