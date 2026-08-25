import Mathlib

namespace Submissions.Erdos884Disproof.Control

noncomputable abbrev sumDivisorInvPairwiseDifference (n : ℕ) : ℝ :=
  ∑ j : Fin n.divisors.card, ∑ i : Fin j,
    (1 : ℚ) / (Nat.nth (· ∣ n) j - Nat.nth (· ∣ n) i)

noncomputable abbrev sumDivisorInvConsecutiveDifference (n : ℕ) : ℝ :=
  ∑ i : Fin (n.divisors.card - 1),
    (1 : ℚ) / (Nat.nth (· ∣ n) (i + 1) - Nat.nth (· ∣ n) i)

/-- Must-fail control: the desired conclusion is supplied through `False`. -/
theorem proof (h : False) :
    ¬ (sumDivisorInvPairwiseDifference =O[Filter.atTop]
      (1 + sumDivisorInvConsecutiveDifference)) :=
  h.elim

end Submissions.Erdos884Disproof.Control
