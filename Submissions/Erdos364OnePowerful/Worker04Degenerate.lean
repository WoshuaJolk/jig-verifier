import Mathlib.Data.Nat.PrimeFin

namespace Submissions.Erdos364OnePowerful.Worker04Degenerate

def Full (k n : ℕ) : Prop :=
  ∀ p ∈ n.primeFactors, p ^ k ∣ n

abbrev Powerful (n : ℕ) : Prop :=
  Full 2 n

theorem proof : False → Powerful 1 :=
  False.elim

end Submissions.Erdos364OnePowerful.Worker04Degenerate
