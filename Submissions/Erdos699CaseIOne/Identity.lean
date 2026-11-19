import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic

namespace Submissions.Erdos699CaseIOne.Identity

/-- From `(m+1)·C(m,k) = C(m+1,k+1)·(k+1)`: if `C(m+1,k+1)` were coprime to `m+1` it would
divide the strictly smaller `C(m,k)`. -/
theorem proof :
    ∀ n j : ℕ, 1 < j → j ≤ n / 2 →
      ∃ p : ℕ, p.Prime ∧ 1 ≤ p ∧ p ∣ Nat.gcd (n.choose 1) (n.choose j) := by
  intro n j hj hjn
  have hne : Nat.gcd (n.choose 1) (n.choose j) ≠ 1 := by
    intro h
    rw [Nat.choose_one_right] at h
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
    have hid := Nat.add_one_mul_choose_eq m k
    have hdvd : (m + 1).choose (k + 1) ∣ (m + 1) * m.choose k := ⟨k + 1, hid⟩
    have hcop : Nat.Coprime ((m + 1).choose (k + 1)) (m + 1) := Nat.coprime_comm.mp h
    have hd2 : (m + 1).choose (k + 1) ∣ m.choose k := hcop.dvd_of_dvd_mul_left hdvd
    have hpos : 0 < m.choose k := Nat.choose_pos (by omega)
    have hle := Nat.le_of_dvd hpos hd2
    have hrec : (m + 1).choose (k + 1) = m.choose k + m.choose (k + 1) :=
      Nat.choose_succ_succ m k
    have hpos2 : 0 < m.choose (k + 1) := Nat.choose_pos (by omega)
    omega
  obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hne
  exact ⟨p, hp, hp.one_le, hpd⟩

end Submissions.Erdos699CaseIOne.Identity
