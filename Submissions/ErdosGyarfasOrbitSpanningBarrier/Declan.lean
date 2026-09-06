import Mathlib.Data.Nat.ModEq
import Mathlib.Tactic

/-
An obstruction to the numerical inference in Guillem Duran-Ballester,
'A Structural Exhaustion Proof of the Erdos-Gyarfas Conjecture on Power-of-Two
Cycles', Zenodo 22019344 (2026-08-20), Lemma 'System increment arithmetic'.
This is an arithmetic countermodel, not an Erdos-Gyarfas graph counterexample.
-/
namespace Submissions.ErdosGyarfasOrbitSpanningBarrier.Declan

/-- The spectrum of a serial system with increment 17 and thirteen offsets. -/
def InSpectrum (d y : ℕ) : Prop :=
  ∃ t ≤ 8 * d, ∃ r ≤ 12, y = 17 * (12 * d + t) + r

/-- A long central spectral interval can miss every power of two even though
its residue classes intersect the complete doubling orbit modulo 17. -/
theorem no_power_in_spectrum {d k : ℕ} (hd : 1 ≤ d)
    (hk : 2 ^ k = 272 * d + 16) :
    ∀ j : ℕ, ¬ InSpectrum d (2 ^ j) := by
  intro j ⟨t, ht, r, hr, he⟩
  have hlo : 2 ^ k < 2 * 2 ^ j := by omega
  have hhi : 2 ^ j < 2 * 2 ^ k := by omega
  have heq : j = k := by
    rcases lt_trichotomy j k with hlt | heq | hgt
    · have hp : 2 ^ (j + 1) ≤ 2 ^ k :=
        pow_le_pow_right' (by omega : 1 ≤ (2 : ℕ)) (by omega)
      rw [pow_succ] at hp
      omega
    · exact heq
    · have hp : 2 ^ (k + 1) ≤ 2 ^ j :=
        pow_le_pow_right' (by omega : 1 ≤ (2 : ℕ)) (by omega)
      rw [pow_succ] at hp
      omega
  subst j
  omega

theorem spans_power {d k : ℕ} (hd : 1 ≤ d)
    (hk : 2 ^ k = 272 * d + 16) :
    204 * d < 2 ^ k ∧ 2 ^ k < 340 * d + 12 := by omega

/-- These are the two realized endpoint lengths of the spectrum. -/
theorem spectral_endpoints (d : ℕ) :
    InSpectrum d (204 * d) ∧ InSpectrum d (340 * d + 12) := by
  constructor
  · exact ⟨0, by omega, 0, by omega, by omega⟩
  · exact ⟨8 * d, by omega, 12, by omega, by omega⟩

/-- The doubling orbit has order eight modulo 17. -/
theorem orbit_certificate :
    2 ^ 8 % 17 = 1 ∧
    (∀ k ∈ Finset.Icc 1 7, 2 ^ k % 17 ≠ 1) ∧
    8 > 17 - 13 ∧
    (∃ k : ℕ, 2 ^ k % 17 ≤ 12) := by
  refine ⟨by norm_num, by decide, by norm_num, 0, by norm_num⟩

/-- Explicit finite countermodel to orbit-hit + scale-spanning => power-hit. -/
theorem concrete_countermodel :
    204 * 3855 < 2 ^ 20 ∧
    2 ^ 20 < 340 * 3855 + 12 ∧
    InSpectrum 3855 (204 * 3855) ∧
    InSpectrum 3855 (340 * 3855 + 12) ∧
    (∀ j : ℕ, ¬ InSpectrum 3855 (2 ^ j)) ∧
    8 * 3855 ≥ 2 * 17 ^ 2 := by
  have hk : (2 : ℕ) ^ 20 = 272 * 3855 + 16 := by norm_num
  have hs := spans_power (d := 3855) (by omega) hk
  have he := spectral_endpoints 3855
  exact ⟨hs.1, hs.2, he.1, he.2,
    no_power_in_spectrum (by omega) hk, by norm_num⟩

/-- Arbitrarily large members exist; bounded end trimming cannot repair the
inference. Every eighth binary exponent supplies the same forbidden residue. -/
theorem arbitrarily_large_parameters (B : ℕ) :
    ∃ d k : ℕ, B ≤ d ∧ 1 ≤ d ∧ 2 ^ k = 272 * d + 16 := by
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (272 * (B + 1) + 16)
    (by norm_num : 1 < (256 : ℕ))
  have hz : 256 ^ n % 17 = 1 := by norm_num [Nat.pow_mod]
  let d := (256 ^ n - 1) / 17
  have hd : 256 ^ n = 17 * d + 1 := by
    have hm := Nat.mod_add_div (256 ^ n - 1) 17
    have hp : 1 ≤ 256 ^ n := Nat.one_le_pow _ _ (by omega)
    dsimp [d]
    omega
  refine ⟨d, 8 * n + 4, by omega, by omega, ?_⟩
  calc
    (2 : ℕ) ^ (8 * n + 4) = 256 ^ n * 16 := by
      rw [pow_add, pow_mul]
      norm_num
    _ = 272 * d + 16 := by omega

/-- The power lies arbitrarily far from both spectrum endpoints, and there
are arbitrarily many identical increments. A fixed end correction or fixed
frequency threshold therefore cannot validate the orbit-hit inference. -/
theorem robust_countermodels (B : ℕ) :
    ∃ d k : ℕ,
      1 ≤ d ∧ B ≤ 8 * d ∧
      204 * d + 17 * B + 12 < 2 ^ k ∧
      2 ^ k + 17 * B + 12 < 340 * d + 12 ∧
      InSpectrum d (204 * d) ∧
      InSpectrum d (340 * d + 12) ∧
      (∀ j : ℕ, ¬ InSpectrum d (2 ^ j)) := by
  obtain ⟨d, k, hdB, hd, hk⟩ := arbitrarily_large_parameters (B + 1)
  have he := spectral_endpoints d
  exact ⟨d, k, hd, by omega, by omega, by omega, he.1, he.2,
    no_power_in_spectrum hd hk⟩

theorem no_power_between {k y : ℕ} (hlo : 2 ^ k < y)
    (hhi : y < 2 * 2 ^ k) : ∀ j : ℕ, 2 ^ j ≠ y := by
  intro j he
  by_cases hj : j ≤ k
  · have hp := pow_le_pow_right' (by omega : 1 ≤ (2 : ℕ)) hj
    omega
  · have hp : 2 ^ (k + 1) ≤ 2 ^ j :=
      pow_le_pow_right' (by omega : 1 ≤ (2 : ℕ)) (by omega)
    rw [pow_succ] at hp
    omega

/-- The other two kinds of cycle lengths in the explicit serial graph
realization are also harmless: a single cell has length21; two closing paths
have combined length376d+r+s. The graph realization itself is explained in
RESEARCH.md; this theorem checks its remaining numerical obligations. -/
theorem auxiliary_cycle_lengths {d k : ℕ} (hd : 1 ≤ d)
    (hk : 2 ^ k = 272 * d + 16) :
    (∀ j : ℕ, 2 ^ j ≠ 21) ∧
    (∀ r ≤ 12, ∀ s ≤ 12, ∀ j : ℕ, 2 ^ j ≠ 376 * d + r + s) := by
  constructor
  · exact no_power_between (k := 4) (by norm_num) (by norm_num)
  · intro r hr s hs
    apply no_power_between (k := k) <;> omega

#print axioms no_power_in_spectrum
#print axioms concrete_countermodel
#print axioms arbitrarily_large_parameters
#print axioms robust_countermodels
#print axioms auxiliary_cycle_lengths
abbrev statement : Prop :=
  (2 ^ 8 % 17 = 1 ∧
    (∀ k ∈ Finset.Icc 1 7, 2 ^ k % 17 ≠ 1) ∧
    8 > 17 - 13 ∧ (∃ k : ℕ, 2 ^ k % 17 ≤ 12)) ∧
  ∀ B : ℕ, ∃ d k : ℕ,
    1 ≤ d ∧ B ≤ 8 * d ∧
    204 * d + 17 * B + 12 < 2 ^ k ∧
    2 ^ k + 17 * B + 12 < 340 * d + 12 ∧
    InSpectrum d (204 * d) ∧
    InSpectrum d (340 * d + 12) ∧
    (∀ j : ℕ, ¬ InSpectrum d (2 ^ j))

theorem proof : statement := ⟨orbit_certificate, robust_countermodels⟩
#print axioms proof
end Submissions.ErdosGyarfasOrbitSpanningBarrier.Declan
