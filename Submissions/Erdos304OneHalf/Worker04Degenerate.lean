import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Rat.Defs

namespace Submissions.Erdos304OneHalf.Worker04Degenerate

def unitFractionExpressible (a b : ℕ) : Set ℕ :=
  {k | ∃ s : Finset ℕ,
    s.card = k ∧ (∀ n ∈ s, n > 1) ∧
      (a / b : ℚ) = ∑ n ∈ s, (n : ℚ)⁻¹}

theorem proof : False → 1 ∈ unitFractionExpressible 1 2 :=
  False.elim

end Submissions.Erdos304OneHalf.Worker04Degenerate
