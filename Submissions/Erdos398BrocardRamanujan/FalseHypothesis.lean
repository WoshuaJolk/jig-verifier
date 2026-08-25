import Mathlib.Data.Nat.Factorial.Basic

namespace Submissions.Erdos398BrocardRamanujan.FalseHypothesis

/-- The Brocard--Ramanujan conjecture: the only natural `n` for which
`n! + 1` is a square are `4`, `5`, and `7`. -/
abbrev statement : Prop :=
  {n : ℕ | ∃ m : ℕ, Nat.factorial n + 1 = m ^ 2} = {4, 5, 7}

theorem proof : False → statement := False.elim

end Submissions.Erdos398BrocardRamanujan.FalseHypothesis
