import Mathlib.NumberTheory.ArithmeticFunction.Misc

namespace Submissions.Erdos410SigmaOrbitGrowth.Control

open ArithmeticFunction

abbrev claimedStatement : Prop :=
  ∀ n > 1,
    StrictMono (fun k : ℕ => (sigma 1)^[k] n) ∧
      ∀ k : ℕ, n + k ≤ (sigma 1)^[k] n

theorem vacuousHypothesis : False → claimedStatement := False.elim

end Submissions.Erdos410SigmaOrbitGrowth.Control
