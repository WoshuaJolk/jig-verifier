import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Squarefree

open Filter

namespace Statements.Erdos969SquarefreeErrorQuarter

/-- The number of squarefree positive integers at most `n`. -/
def squarefreeCount (n : ℕ) : ℕ :=
  ((Finset.range (n + 1)).filter Squarefree).card

/-- Erdős Problem 969, with the conjectured quarter-power order expressed as
the still-open upper half: the squarefree counting error is
`O_ε(n^(1/4+ε))` for every positive `ε`. -/
abbrev statement : Prop :=
  ∀ ε > (0 : ℝ),
    (fun n : ℕ =>
      |(squarefreeCount n : ℝ) - (6 / Real.pi ^ 2) * n|) =O[atTop]
      (fun n : ℕ => (n : ℝ) ^ ((1 : ℝ) / 4 + ε))

theorem target : statement := sorry

end Statements.Erdos969SquarefreeErrorQuarter
