import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Nth
import Mathlib.Data.Nat.Squarefree
import Mathlib.Order.Filter.AtTopBot.CountablyGenerated

open Filter

namespace Statements.Erdos208SquarefreeGapEpsilon

/-- The increasing sequence of squarefree natural numbers. -/
noncomputable def squarefreeNumber (n : ℕ) : ℕ :=
  Nat.nth Squarefree n

/-- Part (i) of Erdős Problem 208. -/
abbrev statement : Prop :=
  ∀ ε > (0 : ℝ),
    (fun n : ℕ => (squarefreeNumber (n + 1) : ℝ) - squarefreeNumber n) =O[atTop]
      (fun n : ℕ => (squarefreeNumber n : ℝ) ^ ε)

theorem target : statement := sorry

end Statements.Erdos208SquarefreeGapEpsilon
