import Mathlib.Tactic
import Mathlib.Data.Nat.ChineseRemainder
import Mathlib.NumberTheory.Bertrand

/-!
An elementary finite-support restriction for E287.
The CRT width obstruction is prior art: RexHannes/erdos-287-proof-search,
RequestProject/Erdos287/CeilingCRT.lean. The interval representative proof follows
the shorter Nat-only form in that project's NonAdjacentHoles.lean.
This file adds the explicit endpoint consequence M < 2*q*r.
-/
namespace Submissions.E287HighSmooth.Cole
open Finset

lemma residue_in_interval (N m c : ℕ) (hm : 0 < m) :
    ∃ x, N ≤ x ∧ x < N + m ∧ x ≡ c [MOD m] := by
  have hc : c % m ∈ Finset.range m := Finset.mem_range.mpr (Nat.mod_lt _ hm)
  rw [← Nat.image_Ico_mod N m] at hc
  obtain ⟨x, hx, hxm⟩ := Finset.mem_image.mp hc
  rw [Finset.mem_Ico] at hx
  exact ⟨x, hx.1, hx.2, hxm⟩

lemma adjacent_multiples (N M q r : ℕ)
    (hcop : Nat.Coprime q r) (hq : 0 < q) (hr : 0 < r)
    (hwidth : q * r ≤ M - N) :
    ∃ x, N ≤ x ∧ x + 1 ≤ M ∧ q ∣ x ∧ r ∣ x + 1 := by
  obtain ⟨k, hkq, hkr⟩ := Nat.chineseRemainder hcop 0 (r - 1)
  obtain ⟨x, hxlo, hxhi, hxk⟩ := residue_in_interval N (q * r) k (by positivity)
  refine ⟨x, hxlo, by omega, ?_, ?_⟩
  · have hxq : x ≡ k [MOD q] := hxk.of_dvd ⟨r, rfl⟩
    exact Nat.modEq_zero_iff_dvd.mp (hxq.trans hkq)
  · have hxr : x ≡ k [MOD r] := hxk.of_dvd ⟨q, by ring⟩
    have hh := (hxr.trans hkr).add_right 1
    have heq : r - 1 + 1 = r := by omega
    rw [heq] at hh
    exact Nat.modEq_zero_iff_dvd.mp (hh.trans (Nat.modEq_zero_iff_dvd.mpr dvd_rfl))

lemma twice_lower_le_upper (A : Finset ℕ) (N M : ℕ)
    (hN : 2 ≤ N) (hlo : ∀ a ∈ A, N ≤ a) (hhi : ∀ a ∈ A, a ≤ M)
    (hsum : ∑ a ∈ A, (1 : ℚ) / a = 1) : 2 * N ≤ M := by
  by_contra hnot
  have hMN : M < 2 * N := by omega
  have hsub : A ⊆ Finset.Ico N (2 * N) := by
    intro a ha
    exact Finset.mem_Ico.mpr ⟨hlo a ha, lt_of_le_of_lt (hhi a ha) hMN⟩
  have hle : ∑ a ∈ A, (1 : ℚ) / a ≤
      ∑ a ∈ Finset.Ico N (2 * N), (1 : ℚ) / a :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
  have hp : (0 : ℚ) < N := by exact_mod_cast (by omega : 0 < N)
  have hlt : (∑ a ∈ Finset.Ico N (2 * N), (1 : ℚ) / a) <
      ∑ _a ∈ Finset.Ico N (2 * N), (1 : ℚ) / N := by
    apply Finset.sum_lt_sum
    · intro a ha
      apply one_div_le_one_div_of_le hp
      exact_mod_cast (Finset.mem_Ico.mp ha).1
    · refine ⟨N + 1, Finset.mem_Ico.mpr ⟨by omega, by omega⟩, ?_⟩
      exact one_div_lt_one_div_of_lt hp (by push_cast; linarith)
  have hconst : (∑ _a ∈ Finset.Ico N (2 * N), (1 : ℚ) / N) = 1 := by
    simp only [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]
    have heq : 2 * N - N = N := by omega
    rw [heq]
    field_simp
  rw [hsum] at hle
  rw [hconst] at hlt
  linarith

theorem endpoint_bound (A : Finset ℕ) (N M q r : ℕ)
    (hN : 2 ≤ N) (hlo : ∀ a ∈ A, N ≤ a) (hhi : ∀ a ∈ A, a ≤ M)
    (hsum : ∑ a ∈ A, (1 : ℚ) / a = 1)
    (hgap : ∀ x, N ≤ x → x + 1 ≤ M → x ∈ A ∨ x + 1 ∈ A)
    (hcop : Nat.Coprime q r) (hq : 0 < q) (hr : 0 < r)
    (haq : ∀ a ∈ A, ¬q ∣ a) (har : ∀ a ∈ A, ¬r ∣ a) :
    M < 2 * (q * r) := by
  have hlower := twice_lower_le_upper A N M hN hlo hhi hsum
  have hwidth : M - N < q * r := by
    by_contra hn
    obtain ⟨x, hxlo, hxhi, hxq, hxr⟩ :=
      adjacent_multiples N M q r hcop hq hr (by omega)
    rcases hgap x hxlo hxhi with hx | hx
    · exact haq x hx hxq
    · exact har (x + 1) hx hxr
  omega

/-- A CRT/Bertrand consequence, not a solution of E287: a gap-two unit-sum
set supported on primes at most B cannot start at or above 8*B^2. -/
theorem smooth_minimum_bound (A : Finset ℕ) (N M B : ℕ)
    (hB : 0 < B) (hN : 2 ≤ N)
    (hlo : ∀ a ∈ A, N ≤ a) (hhi : ∀ a ∈ A, a ≤ M)
    (hsum : ∑ a ∈ A, (1 : ℚ) / a = 1)
    (hgap : ∀ x, N ≤ x → x + 1 ≤ M → x ∈ A ∨ x + 1 ∈ A)
    (hsmooth : ∀ a ∈ A, ∀ p : ℕ, p.Prime → p ∣ a → p ≤ B) :
    N < 8 * B^2 := by
  obtain ⟨q, hq, hBq, hqB⟩ := Nat.exists_prime_lt_and_le_two_mul B (by omega)
  obtain ⟨r, hr, hBr, hrB⟩ := Nat.exists_prime_lt_and_le_two_mul (2*B) (by omega)
  have hcop : Nat.Coprime q r := hq.coprime_iff_not_dvd.mpr (by
    intro hd
    have he := (Nat.prime_dvd_prime_iff_eq hq hr).mp hd
    omega)
  have hb := endpoint_bound A N M q r hN hlo hhi hsum hgap hcop hq.pos hr.pos
    (by intro a ha hd; have := hsmooth a ha q hq hd; omega)
    (by intro a ha hd; have := hsmooth a ha r hr hd; omega)
  have hn := twice_lower_le_upper A N M hN hlo hhi hsum
  have hp : q*r ≤ 8*B^2 := by nlinarith [Nat.mul_le_mul hqB hrB]
  omega



theorem high_smooth_not_one (A : Finset ℕ) (N M B : ℕ)
    (hB : 0 < B) (hN : 2 ≤ N) (hhigh : 8 * B^2 ≤ N)
    (hlo : ∀ a ∈ A, N ≤ a) (hhi : ∀ a ∈ A, a ≤ M)
    (hgap : ∀ x, N ≤ x → x + 1 ≤ M → x ∈ A ∨ x + 1 ∈ A)
    (hsmooth : ∀ a ∈ A, ∀ p : ℕ, p.Prime → p ∣ a → p ≤ B) :
    ∑ a ∈ A, (1 : ℚ) / a ≠ 1 := by
  intro hsum
  have := smooth_minimum_bound A N M B hB hN hlo hhi hsum hgap hsmooth
  omega


#print axioms high_smooth_not_one
end Submissions.E287HighSmooth.Cole
