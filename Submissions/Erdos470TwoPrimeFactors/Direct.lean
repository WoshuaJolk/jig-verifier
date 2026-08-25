import Mathlib.NumberTheory.FactorisationProperties
import Mathlib.Tactic

namespace Submissions.Erdos470TwoPrimeFactors.Direct

theorem proof : ∀ n : ℕ, Odd n → n.Weird → 2 ≤ n.primeFactors.card := by
  intro n _ hweird
  have hn0 : n ≠ 0 := hweird.pos.ne'
  have hn1 : n ≠ 1 := by
    intro hn
    subst n
    have : ¬(1 : ℕ).Weird := by decide
    exact this hweird
  have hn2 : 2 ≤ n := by omega
  have hnpp : ¬IsPrimePow n := by
    intro hpp
    have hdef := hpp.deficient
    unfold Nat.Deficient at hdef
    unfold Nat.Weird Nat.Abundant at hweird
    omega
  have hnontrivial : n.primeFactors.Nontrivial :=
    (Nat.not_isPrimePow_iff_nontrivial_of_two_le hn2).mp hnpp
  exact (Finset.one_lt_card_iff_nontrivial.mpr hnontrivial)

end Submissions.Erdos470TwoPrimeFactors.Direct
