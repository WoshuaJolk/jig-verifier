import Mathlib

namespace Submissions.Erdos942TwoPowerfulConcreteWindow.Direct

def Powerful (m : ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → p ∣ m → p ^ 2 ∣ m

lemma powerful_construction (d D r : ℕ) (hdD : d ∣ D) :
    Powerful (d * D ^ 2 * r ^ 2) := by
  intro p hp hpdvd
  simp only [mul_assoc, hp.dvd_mul] at hpdvd
  rcases hpdvd with hpd | hpD | hpr
  · rw [show d * D ^ 2 * r ^ 2 = r ^ 2 * (D ^ 2 * d) by ac_rfl]
    exact dvd_mul_of_dvd_right
      (dvd_mul_of_dvd_left
        (pow_dvd_pow_of_dvd (dvd_trans hpd hdD) 2) d) (r ^ 2)
  · rw [show d * D ^ 2 * r ^ 2 = r ^ 2 * (D ^ 2 * d) by ac_rfl]
    exact dvd_mul_of_dvd_right
      (dvd_mul_of_dvd_left
        (pow_dvd_pow_of_dvd (hp.dvd_of_dvd_pow hpD) 2) d) (r ^ 2)
  · simpa [mul_assoc, mul_comm, mul_left_comm] using
      dvd_mul_of_dvd_right
        (dvd_mul_of_dvd_right
          (pow_dvd_pow_of_dvd (hp.dvd_of_dvd_pow hpr) 2) (D ^ 2)) d

theorem proof :
    ∃ m₁ m₂ : ℕ,
      m₁ ≠ m₂ ∧ Powerful m₁ ∧ Powerful m₂ ∧
      2909 ^ 2 < m₁ ∧ m₁ < 2910 ^ 2 ∧
      2909 ^ 2 < m₂ ∧ m₂ < 2910 ^ 2 := by
  refine ⟨3 * 6 ^ 2 * 280 ^ 2, 6 * 6 ^ 2 * 198 ^ 2, by norm_num,
    powerful_construction 3 6 280 (by norm_num),
    powerful_construction 6 6 198 (by norm_num), by norm_num,
    by norm_num, by norm_num, by norm_num⟩

end Submissions.Erdos942TwoPowerfulConcreteWindow.Direct
