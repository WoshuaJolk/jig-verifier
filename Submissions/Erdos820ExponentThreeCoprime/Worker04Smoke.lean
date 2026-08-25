import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Tactic

namespace Submissions.Erdos820ExponentThreeCoprime.Worker04Smoke

theorem proof : Nat.Coprime (2 ^ 3 - 1) (3 ^ 3 - 1) := by
  norm_num

end Submissions.Erdos820ExponentThreeCoprime.Worker04Smoke
