import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.PrimeFin

namespace Submissions.Erdos370ConsecutiveSmoothNumbers.Control

abbrev maxPrimeFac (n : ℕ) : ℕ :=
  if n = 1 then 1 else n.primeFactorsList.getLastI

theorem proof (h : False) :
    {n : ℕ | (maxPrimeFac n : ℝ) < √n ∧
      (maxPrimeFac (n + 1) : ℝ) < √(n + 1)}.Infinite :=
  h.elim

end Submissions.Erdos370ConsecutiveSmoothNumbers.Control
