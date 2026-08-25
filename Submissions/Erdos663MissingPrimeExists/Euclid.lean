import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.Prime.Infinite
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic

open scoped BigOperators

namespace Submissions.Erdos663MissingPrimeExists.Euclid

def blockProduct (n k : ℕ) : ℕ :=
  ∏ i ∈ Finset.Icc 1 k, (n + i)

theorem proof :
    ∀ n k : ℕ, ∃ p : ℕ, p.Prime ∧ ¬p ∣ blockProduct n k := by
  intro n k
  have hpos : 0 < blockProduct n k := by
    unfold blockProduct
    apply Finset.prod_pos
    intro i hi
    simp only [Finset.mem_Icc] at hi
    omega
  obtain ⟨p, hpge, hp⟩ :=
    Nat.exists_infinite_primes (blockProduct n k + 1)
  refine ⟨p, hp, ?_⟩
  intro hdvd
  have hple : p ≤ blockProduct n k := Nat.le_of_dvd hpos hdvd
  omega

end Submissions.Erdos663MissingPrimeExists.Euclid
