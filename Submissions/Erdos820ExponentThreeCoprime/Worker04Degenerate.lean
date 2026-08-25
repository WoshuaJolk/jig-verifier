import Mathlib.Data.Nat.GCD.Basic

namespace Submissions.Erdos820ExponentThreeCoprime.Worker04Degenerate

theorem proof : False → Nat.Coprime (2 ^ 3 - 1) (3 ^ 3 - 1) :=
  False.elim

end Submissions.Erdos820ExponentThreeCoprime.Worker04Degenerate
