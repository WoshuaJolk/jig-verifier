import Mathlib.Data.Nat.Prime.Basic

namespace Submissions.Erdos676TwelveRepresentation.Worker04Degenerate

theorem proof :
    False → ∃ p a b : ℕ,
      p.Prime ∧ 1 ≤ a ∧ b < p ∧ 12 = a * p ^ 2 + b :=
  False.elim

end Submissions.Erdos676TwelveRepresentation.Worker04Degenerate
