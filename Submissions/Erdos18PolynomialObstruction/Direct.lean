import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.NumberTheory.Divisors
import Mathlib.Tactic

namespace Submissions.Erdos18PolynomialObstruction.Direct

theorem obstructionCertificate :
    ∀ k m : ℕ, 0 < m → ¬(m ∣ k.factorial) →
      ∃ p Q : ℕ,
        p.Prime ∧
        Q = p ^ (k.factorial.factorization p + 1) ∧
        k < Q ∧
        Q ∣ m ∧
        Q ≤ m := by
  intro k m hm hmdvd
  have hexcess :
      ∃ p : ℕ, p.Prime ∧
        k.factorial.factorization p < m.factorization p := by
    by_contra h
    push Not at h
    apply hmdvd
    apply (Nat.factorization_prime_le_iff_dvd hm.ne'
      (Nat.factorial_ne_zero k)).mp
    intro p hp
    exact h p hp
  obtain ⟨p, hp, hplt⟩ := hexcess
  let Q := p ^ (k.factorial.factorization p + 1)
  have hQdvd : Q ∣ m := by
    apply hp.pow_dvd_iff_le_factorization hm.ne' |>.mpr
    omega
  have hQpos : 0 < Q := by
    dsimp [Q]
    exact pow_pos hp.pos _
  have hQle : Q ≤ m := Nat.le_of_dvd hm hQdvd
  have hQnot : ¬(Q ∣ k.factorial) := by
    intro h
    have := (hp.pow_dvd_iff_le_factorization
      (Nat.factorial_ne_zero k)).mp h
    omega
  have hkQ : k < Q := by
    by_contra h
    have hQfact : Q ∣ k.factorial :=
      Nat.dvd_factorial hQpos (by omega)
    exact hQnot hQfact
  exact ⟨p, Q, hp, rfl, hkQ, hQdvd, hQle⟩

theorem obstructionUniqueInShortWindow :
    ∀ Q A h s t : ℕ,
      h < Q →
      0 < s →
      s < t →
      t ≤ h →
      h < A →
      ¬(Q ∣ A - s ∧ Q ∣ A - t) := by
  intro Q A h s t hQ hs hst hth hhA
  rintro ⟨hQs, hQt⟩
  have hsum : A - s = (A - t) + (t - s) := by omega
  have hQdiff : Q ∣ t - s := by
    apply (Nat.dvd_add_iff_right hQt).2
    rw [← hsum]
    exact hQs
  have hdiffpos : 0 < t - s := by omega
  have hQle : Q ≤ t - s := Nat.le_of_dvd hdiffpos hQdiff
  omega

theorem cubicCertificate :
    ∀ k m : ℕ, 0 < m → m ≤ k ^ 3 → ¬(m ∣ k.factorial) →
      ∃ p Q : ℕ,
        p.Prime ∧
        Q = p ^ (k.factorial.factorization p + 1) ∧
        k < Q ∧
        Q ∣ m ∧
        Q ≤ k ^ 3 := by
  intro k m hm hmcubic hmdvd
  obtain ⟨p, Q, hp, hQ, hkQ, hQdvd, hQle⟩ :=
    obstructionCertificate k m hm hmdvd
  exact ⟨p, Q, hp, hQ, hkQ, hQdvd, hQle.trans hmcubic⟩

theorem sevenCubicGap :
    ∀ m : ℕ, 181 ≤ m → m < 7 * 6 * 5 →
      ¬(m ∣ Nat.factorial 7) := by
  intro m hlo hhi
  interval_cases m <;> norm_num [Nat.factorial]

theorem proof :
    (∀ k m : ℕ, 0 < m → ¬(m ∣ k.factorial) →
      ∃ p Q : ℕ,
        p.Prime ∧
        Q = p ^ (k.factorial.factorization p + 1) ∧
        k < Q ∧
        Q ∣ m ∧
        Q ≤ m) ∧
    (∀ Q A h s t : ℕ,
      h < Q →
      0 < s →
      s < t →
      t ≤ h →
      h < A →
      ¬(Q ∣ A - s ∧ Q ∣ A - t)) ∧
    (∀ k m : ℕ, 0 < m → m ≤ k ^ 3 → ¬(m ∣ k.factorial) →
      ∃ p Q : ℕ,
        p.Prime ∧
        Q = p ^ (k.factorial.factorization p + 1) ∧
        k < Q ∧
        Q ∣ m ∧
        Q ≤ k ^ 3) ∧
    (∀ m : ℕ, 181 ≤ m → m < 7 * 6 * 5 →
      ¬(m ∣ Nat.factorial 7)) :=
  ⟨obstructionCertificate, obstructionUniqueInShortWindow,
    cubicCertificate, sevenCubicGap⟩

end Submissions.Erdos18PolynomialObstruction.Direct
