import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Nat.ModEq
import Mathlib.Tactic

namespace Submissions.Erdos1072SevenEarlyWitness.Worker04Smoke

theorem proof : (3 : ℕ).factorial + 1 ≡ 0 [MOD 7] := by
  norm_num [Nat.ModEq]

end Submissions.Erdos1072SevenEarlyWitness.Worker04Smoke
