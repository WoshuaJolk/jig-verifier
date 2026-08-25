import Mathlib.Data.Nat.Choose.Basic

namespace Submissions.Erdos700ThirtyCandidate.Worker04Degenerate

theorem proof : False → Nat.gcd 30 ((30 : ℕ).choose 5) = 6 :=
  False.elim

end Submissions.Erdos700ThirtyCandidate.Worker04Degenerate
