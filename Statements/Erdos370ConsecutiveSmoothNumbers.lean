import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.PrimeFin

namespace Statements.Erdos370ConsecutiveSmoothNumbers

/-- The Formal Conjectures convention for the largest prime factor. -/
abbrev maxPrimeFac (n : ℕ) : ℕ :=
  if n = 1 then 1 else n.primeFactorsList.getLastI

/-- Erdős Problem 370: consecutive unusually smooth integers occur infinitely often. -/
abbrev statement : Prop :=
  {n : ℕ | (maxPrimeFac n : ℝ) < √n ∧
    (maxPrimeFac (n + 1) : ℝ) < √(n + 1)}.Infinite

theorem target : statement := sorry

end Statements.Erdos370ConsecutiveSmoothNumbers
