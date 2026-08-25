import Mathlib.Data.Nat.PrimeFin

namespace Statements.Erdos364TripleResiduesMod36

def Full (k n : ℕ) : Prop :=
  ∀ p ∈ n.primeFactors, p ^ k ∣ n

abbrev Powerful (n : ℕ) : Prop :=
  Full 2 n

/-- Beckon's congruence restriction for any hypothetical powerful triple. -/
abbrev statement : Prop :=
  ∀ n : ℕ, Powerful n → Powerful (n + 1) → Powerful (n + 2) →
    n % 36 = 7 ∨ n % 36 = 27 ∨ n % 36 = 35

theorem target : statement := sorry

end Statements.Erdos364TripleResiduesMod36
