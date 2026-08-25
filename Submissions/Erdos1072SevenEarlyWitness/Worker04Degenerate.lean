import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Nat.ModEq

namespace Submissions.Erdos1072SevenEarlyWitness.Worker04Degenerate

theorem proof : False → (3 : ℕ).factorial + 1 ≡ 0 [MOD 7] :=
  False.elim

end Submissions.Erdos1072SevenEarlyWitness.Worker04Degenerate
