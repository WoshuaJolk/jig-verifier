import Mathlib.Data.Nat.PrimeFin

namespace Statements.Erdos364OnePowerful

def Full (k n : ℕ) : Prop :=
  ∀ p ∈ n.primeFactors, p ^ k ∣ n

abbrev Powerful (n : ℕ) : Prop :=
  Full 2 n

/-- One is powerful, vacuously. -/
abbrev statement : Prop :=
  Powerful 1

theorem target : statement := sorry

end Statements.Erdos364OnePowerful
