import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic

namespace Submissions.Erdos700ThirtyCandidate.Worker04Smoke

theorem proof : Nat.gcd 30 ((30 : ℕ).choose 5) = 6 := by
  norm_num [Nat.choose]

end Submissions.Erdos700ThirtyCandidate.Worker04Smoke
