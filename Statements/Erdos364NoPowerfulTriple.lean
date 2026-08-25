import Mathlib.Data.Nat.PrimeFin

namespace Statements.Erdos364NoPowerfulTriple

def Full (k n : ℕ) : Prop :=
  ∀ p ∈ n.primeFactors, p ^ k ∣ n

abbrev Powerful (n : ℕ) : Prop :=
  Full 2 n

/-- Erdős Problem 364. -/
abbrev statement : Prop :=
  ¬ ∃ n : ℕ, Powerful n ∧ Powerful (n + 1) ∧ Powerful (n + 2)

theorem target : statement := sorry

end Statements.Erdos364NoPowerfulTriple
