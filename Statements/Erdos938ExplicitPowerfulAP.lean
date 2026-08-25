import Mathlib.Data.Nat.PrimeFin

namespace Statements.Erdos938ExplicitPowerfulAP

def Nat.Full (k n : ℕ) : Prop :=
  ∀ p ∈ n.primeFactors, p ^ k ∣ n

abbrev Nat.Powerful : ℕ → Prop := Nat.Full 2

/-- The first tabulated progression in current Problem 938 literature is
a genuine three-term progression of powerful numbers. -/
abbrev statement : Prop :=
  Nat.Powerful 1728 ∧ Nat.Powerful 1764 ∧ Nat.Powerful 1800 ∧
    1728 + 1800 = 2 * 1764

theorem target : statement := sorry

end Statements.Erdos938ExplicitPowerfulAP
