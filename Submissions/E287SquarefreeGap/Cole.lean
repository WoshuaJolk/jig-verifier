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
namespace Submissions.E287SquarefreeGap.Cole
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


theorem small_unit_sum :
    ∀ A ∈ (Finset.Icc (2 : ℕ) 8).powerset,
      (∑ a ∈ A, (1 : ℚ)/a) = 1 → A = {2,3,6} := by
  decide +kernel

theorem upper_mass :
    (∑ a ∈ (Finset.Icc (9 : ℕ) 24).filter Squarefree, (1 : ℚ)/a) < 1 := by
  decide +kernel

theorem squarefree_not_one (A : Finset ℕ) (N M : ℕ)
    (hN : 2 ≤ N) (hlo : ∀ a ∈ A, N ≤ a) (hhi : ∀ a ∈ A, a ≤ M)
    (hgap : ∀ x, N ≤ x → x + 1 ≤ M → x ∈ A ∨ x + 1 ∈ A)
    (hsq : ∀ a ∈ A, Squarefree a) :
    ∑ a ∈ A, (1 : ℚ) / a ≠ 1 := by
  intro hsum
  have omitted (d : ℕ) (hd : ¬ Squarefree d) : ∀ a ∈ A, ¬ d ∣ a := by
    intro a ha hdiv
    exact hd ((hsq a ha).squarefree_of_dvd hdiv)
  have hM := endpoint_bound A N M 4 9 hN hlo hhi hsum hgap
    (by decide) (by decide) (by decide)
    (omitted 4 (by decide +kernel)) (omitted 9 (by decide +kernel))
  have hNM := twice_lower_le_upper A N M hN hlo hhi hsum
  have absent (a : ℕ) (h : ¬ Squarefree a) : a ∉ A := fun ha => h (hsq a ha)
  have h8 := absent 8 (by decide +kernel)
  have h9 := absent 9 (by decide +kernel)
  have h24 := absent 24 (by decide +kernel)
  have h25 := absent 25 (by decide +kernel)
  have h48 := absent 48 (by decide +kernel)
  have h49 := absent 49 (by decide +kernel)
  have block8 : ¬ (N ≤ 8 ∧ 9 ≤ M) := by
    rintro ⟨hl, hu⟩
    exact (hgap 8 hl hu).elim h8 h9
  have block24 : ¬ (N ≤ 24 ∧ 25 ≤ M) := by
    rintro ⟨hl, hu⟩
    exact (hgap 24 hl hu).elim h24 h25
  have block48 : ¬ (N ≤ 48 ∧ 49 ≤ M) := by
    rintro ⟨hl, hu⟩
    exact (hgap 48 hl hu).elim h48 h49
  have cases : (N ≤ 4 ∧ M ≤ 8) ∨ (9 ≤ N ∧ M ≤ 24) := by omega
  rcases cases with ⟨hn, hm⟩ | ⟨hn, hm⟩
  · have hsub : A ⊆ Finset.Icc 2 8 := by
      intro a ha
      exact Finset.mem_Icc.mpr ⟨by have := hlo a ha; omega, by have := hhi a ha; omega⟩
    have heq := small_unit_sum A (Finset.mem_powerset.mpr hsub) hsum
    have h2 : 2 ∈ A := by simp [heq]
    have h6 : 6 ∈ A := by simp [heq]
    have hlow := hlo 2 h2
    have hhigh := hhi 6 h6
    have hh := hgap 4 (by omega) (by omega)
    simp [heq] at hh
  · have hsub : A ⊆ (Finset.Icc 9 24).filter Squarefree := by
      intro a ha
      exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr
        ⟨by have := hlo a ha; omega, by have := hhi a ha; omega⟩, hsq a ha⟩
    have hle := Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun a _ _ => (show (0 : ℚ) ≤ 1 / a by positivity))
    have hlt := upper_mass
    rw [hsum] at hle
    linarith

#print axioms squarefree_not_one
lemma sequence_pair_coverage (k : ℕ) (hk : 2 ≤ k) (s : Fin k → ℕ)
    (hstep : ∀ i : Fin (k-1),
      s ⟨i.val+1, by omega⟩ ≤ s ⟨i.val, by omega⟩ + 2)
    (x : ℕ) (hfirst : s ⟨0, by omega⟩ ≤ x)
    (hlast : x+1 ≤ s ⟨k-1, by omega⟩) :
    x ∈ Finset.univ.image s ∨ x+1 ∈ Finset.univ.image s := by
  classical
  let I : Finset (Fin k) := Finset.univ.filter (fun i => s i ≤ x)
  have hI : I.Nonempty := ⟨⟨0, by omega⟩, by simp [I, hfirst]⟩
  let i := I.max' hI
  have hi : s i ≤ x := (Finset.mem_filter.mp (Finset.max'_mem I hI)).2
  by_cases hx : s i = x
  · exact Or.inl (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, hx⟩)
  have hik : i.val+1 < k := by
    have hil := i.isLt
    by_contra hh
    have he : i = (⟨k-1, by omega⟩ : Fin k) := by
      apply Fin.ext
      change i.val = k-1
      omega
    rw [he] at hi
    omega
  let j : Fin k := ⟨i.val+1, hik⟩
  have hj : x < s j := by
    by_contra hh
    have hjI : j ∈ I := by simp [I, show s j ≤ x by omega]
    have hji : j ≤ i := Finset.le_max' I j hjI
    have hvals := Fin.le_iff_val_le_val.mp hji
    dsimp [j] at hvals
    omega
  have hsj : s j ≤ s i+2 := by
    simpa [j] using hstep ⟨i.val, by omega⟩
  have heq : s j = x+1 := by omega
  exact Or.inr (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, heq⟩)

def canonicalMaxGap (k : ℕ) (s : Fin k → ℕ) : ℕ :=
  Finset.sup Finset.univ (fun i : Fin (k - 1) =>
    s ⟨i.val + 1, by omega⟩ - s ⟨i.val, by omega⟩)

theorem proof (k : ℕ) (hk : 2 ≤ k) (s : Fin k → ℕ)
    (hmono : StrictMono s) (hfirst : 1 < s ⟨0, by omega⟩)
    (hsum : ∑ i : Fin k, 1 / (s i : ℝ) = 1)
    (hsquare : ∀ i : Fin k, Squarefree (s i)) :
    3 ≤ canonicalMaxGap k s := by
  classical
  by_contra hnot
  have hstep : ∀ i : Fin (k-1),
      s ⟨i.val+1, by omega⟩ ≤ s ⟨i.val, by omega⟩ + 2 := by
    intro i
    have hg := Finset.le_sup (f := fun i : Fin (k-1) =>
      s ⟨i.val+1, by omega⟩ - s ⟨i.val, by omega⟩) (Finset.mem_univ i)
    change s ⟨i.val+1, by omega⟩ - s ⟨i.val, by omega⟩ ≤ canonicalMaxGap k s at hg
    omega
  have hqsum : ∑ i : Fin k, (1 : ℚ) / (s i : ℚ) = 1 := by
    apply Rat.cast_injective (α := ℝ)
    push_cast
    exact hsum
  have hAsum : ∑ a ∈ Finset.univ.image s, (1 : ℚ)/a = 1 := by
    rw [Finset.sum_image]
    · simpa using hqsum
    · exact hmono.injective.injOn
  apply squarefree_not_one (Finset.univ.image s) (s ⟨0, by omega⟩)
    (s ⟨k-1, by omega⟩) (by omega) ?_ ?_ ?_ ?_ hAsum
  · intro a ha
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp ha
    exact hmono.monotone (by exact Fin.mk_le_mk.mpr (Nat.zero_le _))
  · intro a ha
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp ha
    exact hmono.monotone (by apply Fin.mk_le_mk.mpr; have := i.isLt; omega)
  · exact sequence_pair_coverage k hk s hstep
  · intro a ha
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp ha
    exact hsquare i


#print axioms proof
end Submissions.E287SquarefreeGap.Cole
