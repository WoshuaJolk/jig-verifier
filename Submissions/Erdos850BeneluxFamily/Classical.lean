import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.PrimeFin
import Mathlib.Tactic

namespace Submissions.Erdos850BeneluxFamily.Classical

theorem proof :
    ∀ r ≥ 1,
      let x := 2 * (2 ^ r - 1)
      let y := x * (x + 2)
      x ≠ y ∧
        x.primeFactors = y.primeFactors ∧
        (x + 1).primeFactors = (y + 1).primeFactors := by
  intro r hr
  dsimp only
  let x := 2 * (2 ^ r - 1)
  have hpow : 2 ≤ 2 ^ r := by
    simpa using Nat.pow_le_pow_right (by omega : 0 < 2) hr
  have hx : 0 < x := by
    dsimp [x]
    omega
  have hx2 : x + 2 = 2 ^ (r + 1) := by
    dsimp [x]
    rw [pow_succ]
    omega
  have hsupport_x2 : (x + 2).primeFactors ⊆ x.primeFactors := by
    intro p hp
    rw [hx2, Nat.primeFactors_pow 2 (by omega),
      Nat.prime_two.primeFactors] at hp
    have hp2 : p = 2 := by simpa using hp
    subst p
    rw [Nat.mem_primeFactors]
    exact ⟨Nat.prime_two, by
      dsimp [x]
      exact dvd_mul_right 2 (2 ^ r - 1), hx.ne'⟩
  constructor
  · exact ne_of_lt (lt_mul_of_one_lt_right hx (by omega))
  constructor
  · rw [Nat.primeFactors_mul hx.ne' (by positivity)]
    exact (Finset.union_eq_left.mpr hsupport_x2).symm
  · have hy : x * (x + 2) + 1 = (x + 1) ^ 2 := by ring
    rw [hy, Nat.primeFactors_pow (x + 1) (by norm_num)]

end Submissions.Erdos850BeneluxFamily.Classical
