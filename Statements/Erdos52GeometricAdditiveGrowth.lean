import Mathlib.Algebra.Group.Pointwise.Finset.Basic
import Mathlib.Data.Finset.Prod

open scoped Pointwise

namespace Statements.Erdos52GeometricAdditiveGrowth

/--
Every finite subset of an integral geometric progression of ratio at least two
has unique unordered pair sums and therefore the exact quadratic sumset size.
-/
abbrev statement : Prop :=
  ∀ (q : ℕ) (E : Finset ℕ), 2 ≤ q →
    let A : Finset ℤ := E.image fun n : ℕ => (q ^ n : ℤ)
    (A + A).card = E.card + E.card.choose 2

theorem target : statement := sorry

end Statements.Erdos52GeometricAdditiveGrowth
