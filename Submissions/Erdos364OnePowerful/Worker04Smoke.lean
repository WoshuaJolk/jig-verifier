import Mathlib.Data.Nat.PrimeFin
import Mathlib.Tactic

namespace Submissions.Erdos364OnePowerful.Worker04Smoke

def Full (k n : ℕ) : Prop :=
  ∀ p ∈ n.primeFactors, p ^ k ∣ n

abbrev Powerful (n : ℕ) : Prop :=
  Full 2 n

theorem proof : Powerful 1 := by
  simp [Powerful, Full]

end Submissions.Erdos364OnePowerful.Worker04Smoke
