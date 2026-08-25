import Mathlib.Data.Nat.PrimeFin
import Mathlib.Tactic

namespace Submissions.Erdos938ExplicitPowerfulAP.Direct

def Nat.Full (k n : ℕ) : Prop :=
  ∀ p ∈ n.primeFactors, p ^ k ∣ n

abbrev Nat.Powerful : ℕ → Prop := Nat.Full 2

theorem proof :
    Nat.Powerful 1728 ∧ Nat.Powerful 1764 ∧ Nat.Powerful 1800 ∧
      1728 + 1800 = 2 * 1764 := by
  norm_num [Nat.Powerful, Nat.Full, Nat.primeFactors,
    Nat.primeFactorsList]

end Submissions.Erdos938ExplicitPowerfulAP.Direct
