import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Set.Finite.Lattice
import Mathlib.Order.Filter.AtTopBot.Defs
import Mathlib.Tactic

namespace Submissions.Erdos32ComplementInfinite.BoundedComplement

open Filter Set

def IsAdditiveComplementToPrimes (A : Set ℕ) : Prop :=
  ∀ᶠ n in atTop, ∃ p, p.Prime ∧ ∃ a ∈ A, n = p + a

/-- A bounded set cannot be an additive complement to the primes. -/
private theorem bounded_not_complement :
    ∀ A : Set ℕ, ∀ M : ℕ, A ⊆ Set.Iic M →
      ¬ IsAdditiveComplementToPrimes A := by
  intro A M hAM hA
  rw [IsAdditiveComplementToPrimes, Filter.eventually_atTop] at hA
  obtain ⟨N, hN⟩ := hA
  let m := max (M + 2) N
  let n := m.factorial + M + 2
  have hm2 : 2 ≤ m := by
    dsimp [m]
    omega
  have hmN : N ≤ m := by
    dsimp [m]
    omega
  have hmfac : m ≤ m.factorial :=
    Nat.le_of_dvd (Nat.factorial_pos m)
      (Nat.dvd_factorial (by omega) (le_refl m))
  have hnN : N ≤ n := by
    dsimp [n]
    omega
  obtain ⟨p, hp, a, haA, hn⟩ := hN n hnN
  have haM : a ≤ M := hAM haA
  let d := M + 2 - a
  have hd2 : 2 ≤ d := by
    dsimp [d]
    omega
  have hdm : d ≤ m := by
    dsimp [d, m]
    omega
  have hdp : d ∣ p := by
    have hdfac : d ∣ m.factorial := Nat.dvd_factorial (by omega) hdm
    have hp_eq : p = m.factorial + d := by
      dsimp [n] at hn
      dsimp [d]
      omega
    rw [hp_eq]
    exact dvd_add hdfac (dvd_refl d)
  have hd_eq : d = 1 ∨ d = p := hp.eq_one_or_self_of_dvd d hdp
  rcases hd_eq with hd1 | hdp_eq
  · omega
  · have hmfac_pos : 0 < m.factorial := Nat.factorial_pos m
    have hp_eq : p = m.factorial + d := by
      dsimp [n] at hn
      dsimp [d]
      omega
    omega

/-- Every additive complement to the primes is infinite. -/
theorem proof :
    ∀ A : Set ℕ, IsAdditiveComplementToPrimes A → A.Infinite := by
  intro A hA hAfin
  obtain ⟨M, hM⟩ := hAfin.bddAbove
  exact bounded_not_complement A M (fun _ ha => hM ha) hA

end Submissions.Erdos32ComplementInfinite.BoundedComplement
