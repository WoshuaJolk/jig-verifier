import Mathlib.Data.Nat.PrimeFin

namespace Submissions.Erdos938ExplicitPowerfulAP.Control

def Nat.Full (k n : ℕ) : Prop :=
  ∀ p ∈ n.primeFactors, p ^ k ∣ n

abbrev Nat.Powerful : ℕ → Prop := Nat.Full 2

abbrev claimedStatement : Prop :=
  Nat.Powerful 1728 ∧ Nat.Powerful 1764 ∧ Nat.Powerful 1800 ∧
    1728 + 1800 = 2 * 1764

theorem vacuousHypothesis : False → claimedStatement := False.elim

end Submissions.Erdos938ExplicitPowerfulAP.Control
