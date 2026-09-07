import Mathlib.Algebra.Group.Pointwise.Finset.Basic
open scoped Pointwise
namespace Statements.Erdos52IntegerSolymosi
abbrev statement : Prop :=
  ∀ (A : Finset ℤ) (k : ℕ), A.card < 2 ^ k →
    A.card ^ 4 ≤ 648 * k * (A + A).card ^ 2 * (A * A).card
theorem target : statement := sorry
end Statements.Erdos52IntegerSolymosi
