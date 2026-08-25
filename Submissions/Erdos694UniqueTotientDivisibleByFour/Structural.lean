import Mathlib.Data.Nat.Totient
import Mathlib.Tactic

namespace Submissions.Erdos694UniqueTotientDivisibleByFour.Structural

theorem proof :
    ∀ n > 0, (∃! m : ℕ, Nat.totient m = n) →
      ∃ m : ℕ, Nat.totient m = n ∧ 4 ∣ m := by
  intro n hn hunique
  obtain ⟨m, hm, honly⟩ := hunique
  have hmpos : 0 < m := by
    rw [← Nat.totient_pos, hm]
    exact hn
  have hmeven : Even m := by
    by_contra h
    have hmodd : Odd m := Nat.not_even_iff_odd.mp h
    have hsame : Nat.totient (2 * m) = n := by
      rw [Nat.totient_two_mul_of_odd hmodd, hm]
    have := honly (2 * m) hsame
    omega
  refine ⟨m, hm, ?_⟩
  obtain ⟨k, rfl⟩ := (even_iff_two_dvd.mp hmeven)
  by_contra hfour
  have hknot : ¬ Even k := by
    intro hk
    obtain ⟨j, rfl⟩ := hk
    exact hfour ⟨j, by omega⟩
  have hkodd : Odd k := Nat.not_even_iff_odd.mp hknot
  have hsame : Nat.totient k = n := by
    rw [← Nat.totient_two_mul_of_odd hkodd, hm]
  have := honly k hsame
  omega

end Submissions.Erdos694UniqueTotientDivisibleByFour.Structural
