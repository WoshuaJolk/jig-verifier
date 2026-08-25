import Mathlib

namespace Submissions.Erdos14LargeEpsilon.Direct

open Asymptotics Filter

def uniquePairSums (A : Set ℕ) : Set ℕ :=
  {n | ∃ p : ℕ × ℕ, p.1 ∈ A ∧ p.2 ∈ A ∧ p.1 + p.2 = n ∧
    ∀ a₁ ∈ A, ∀ a₂ ∈ A, a₁ + a₂ = n →
      (a₁ = p.1 ∧ a₂ = p.2) ∨ (a₁ = p.2 ∧ a₂ = p.1)}

noncomputable def exceptionCount (A : Set ℕ) (N : ℕ) : ℝ :=
  ((Set.Icc 1 N) \ uniquePairSums A).ncard

noncomputable def almostSquareRoot (ε : ℝ) (N : ℕ) : ℝ :=
  Real.rpow N (1 / 2 - ε)

lemma unique_representations {A : Set ℕ} {n a b c d : ℕ}
    (hn : n ∈ uniquePairSums A)
    (ha : a ∈ A) (hb : b ∈ A) (hab : a + b = n)
    (hc : c ∈ A) (hd : d ∈ A) (hcd : c + d = n) :
    (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
  rcases hn with ⟨p, hp₁, hp₂, hp, hunique⟩
  have h₁ := hunique a ha b hb hab
  have h₂ := hunique c hc d hd hcd
  rcases h₁ with h₁ | h₁ <;> rcases h₂ with h₂ | h₂ <;> simp_all

lemma exists_small_exception (A : Set ℕ) :
    ∃ n ∈ Set.Icc 1 6, n ∉ uniquePairSums A := by
  by_contra h
  push_neg at h
  have hu1 := h 1 (by simp)
  have hu2 := h 2 (by simp)
  have hu3 := h 3 (by simp)
  have hu4 := h 4 (by simp)
  have hu5 := h 5 (by simp)
  have hu6 := h 6 (by simp)
  rcases hu1 with ⟨p, hp₁, hp₂, hp, _⟩
  have hp_cases :
      (p.1 = 0 ∧ p.2 = 1) ∨ (p.1 = 1 ∧ p.2 = 0) := by
    omega
  have h0 : 0 ∈ A := by
    rcases hp_cases with hp_cases | hp_cases
    · simpa [hp_cases.1] using hp₁
    · simpa [hp_cases.2] using hp₂
  have h1 : 1 ∈ A := by
    rcases hp_cases with hp_cases | hp_cases
    · simpa [hp_cases.2] using hp₂
    · simpa [hp_cases.1] using hp₁
  have h2 : 2 ∉ A := by
    intro h2
    have hr := unique_representations hu2 h1 h1 (by omega) h0 h2 (by omega)
    rcases hr with hr | hr <;> omega
  have h3 : 3 ∈ A := by
    rcases hu3 with ⟨q, hq₁, hq₂, hq, _⟩
    have hq_cases :
        (q.1 = 0 ∧ q.2 = 3) ∨ (q.1 = 1 ∧ q.2 = 2) ∨
        (q.1 = 2 ∧ q.2 = 1) ∨ (q.1 = 3 ∧ q.2 = 0) := by
      omega
    rcases hq_cases with hq_cases | hq_cases | hq_cases | hq_cases
    · simpa [hq_cases.2] using hq₂
    · exact (h2 (by simpa [hq_cases.2] using hq₂)).elim
    · exact (h2 (by simpa [hq_cases.1] using hq₁)).elim
    · simpa [hq_cases.1] using hq₁
  have h4 : 4 ∉ A := by
    intro h4
    have hr := unique_representations hu4 h1 h3 (by omega) h0 h4 (by omega)
    rcases hr with hr | hr <;> omega
  have h5 : 5 ∈ A := by
    rcases hu5 with ⟨q, hq₁, hq₂, hq, _⟩
    have hq_cases :
        (q.1 = 0 ∧ q.2 = 5) ∨ (q.1 = 1 ∧ q.2 = 4) ∨
        (q.1 = 2 ∧ q.2 = 3) ∨ (q.1 = 3 ∧ q.2 = 2) ∨
        (q.1 = 4 ∧ q.2 = 1) ∨ (q.1 = 5 ∧ q.2 = 0) := by
      omega
    rcases hq_cases with hq_cases | hq_cases | hq_cases | hq_cases | hq_cases | hq_cases
    · simpa [hq_cases.2] using hq₂
    · exact (h4 (by simpa [hq_cases.2] using hq₂)).elim
    · exact (h2 (by simpa [hq_cases.1] using hq₁)).elim
    · exact (h2 (by simpa [hq_cases.2] using hq₂)).elim
    · exact (h4 (by simpa [hq_cases.1] using hq₁)).elim
    · simpa [hq_cases.1] using hq₁
  have hr := unique_representations hu6 h1 h5 (by omega) h3 h3 (by omega)
  rcases hr with hr | hr <;> omega

lemma one_le_exceptionCount (A : Set ℕ) {N : ℕ} (hN : 6 ≤ N) :
    1 ≤ exceptionCount A N := by
  rcases exists_small_exception A with ⟨n, hn, hnu⟩
  have hmem : n ∈ Set.Icc 1 N \ uniquePairSums A := by
    exact ⟨⟨hn.1, hn.2.trans hN⟩, hnu⟩
  rw [exceptionCount]
  exact_mod_cast ((Set.ncard_pos (s := Set.Icc 1 N \ uniquePairSums A)).mpr ⟨n, hmem⟩)

theorem proof :
    ∀ A : Set ℕ, ∀ ε : ℝ, 1 / 2 ≤ ε →
      Asymptotics.IsBigO atTop (almostSquareRoot ε) (exceptionCount A) := by
  intro A ε hε
  apply IsBigO.of_bound 1
  filter_upwards [eventually_atTop.2 ⟨6, fun _ hN => hN⟩] with N hN
  unfold almostSquareRoot exceptionCount
  have hrpow : 0 ≤ (N : ℝ).rpow (1 / 2 - ε) :=
    Real.rpow_nonneg (by positivity) _
  have hcount : 0 ≤ (((Set.Icc 1 N \ uniquePairSums A).ncard : ℕ) : ℝ) := by
    positivity
  rw [one_mul, Real.norm_eq_abs, abs_of_nonneg hrpow,
    Real.norm_eq_abs, abs_of_nonneg hcount]
  exact (Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast (show 1 ≤ N by omega))
    (by linarith)).trans (by simpa [exceptionCount] using one_le_exceptionCount A hN)

end Submissions.Erdos14LargeEpsilon.Direct
