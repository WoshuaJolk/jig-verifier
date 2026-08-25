import Mathlib.Algebra.Group.Pointwise.Finset.Basic

open scoped Pointwise

namespace Submissions.Erdos52SingletonZero.Worker04Degenerate

theorem proof :
    False → max (({0} : Finset ℤ) + {0}).card (({0} : Finset ℤ) * {0}).card = 1 := by
  exact False.elim

end Submissions.Erdos52SingletonZero.Worker04Degenerate
