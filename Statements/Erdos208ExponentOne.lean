import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Nth
import Mathlib.Data.Nat.Squarefree
import Mathlib.NumberTheory.Bertrand
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Order.Filter.AtTopBot.CountablyGenerated

open Filter

namespace Statements.Erdos208ExponentOne

noncomputable def squarefreeNumber (n : ℕ) : ℕ :=
  Nat.nth Squarefree n

/-- Consecutive squarefree gaps are big-O of the squarefree numbers themselves. -/
abbrev statement : Prop :=
  (fun n : ℕ => (squarefreeNumber (n + 1) : ℝ) - squarefreeNumber n) =O[atTop]
    (fun n : ℕ => (squarefreeNumber n : ℝ) ^ (1 : ℝ))

theorem target : statement := sorry

end Statements.Erdos208ExponentOne
