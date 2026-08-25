import Mathlib

namespace Submissions.Erdos280ResidueCoverRefutation.Full

set_option maxHeartbeats 8000000

open Nat

/-!
# Erdős Problem 280: Explicit Counterexample

We construct an explicit counterexample to the claim in Erdős Problem 280.

## The sequences

- `n_i = 2^i` for every `i ≥ 1`
- `a_1 = 0`
- `a_i = 2^(i-1) + 1` for every `i ≥ 2`

## Main result

For every `k ≥ 1`, among the integers `m < 2^k`, the only one not covered
by any residue class `a_i mod n_i` (for `1 ≤ i ≤ k`) is `m = 1`.

This gives a counterexample to Erdős Problem 280: the growth condition
`n_k > (1 + ε) k log k` is satisfied (with `ε = 1` for all `k ≥ 1`), yet
the uncovered count is exactly `1 = o(k)`.
-/

/-- An integer `m` is covered by the first `k` residue classes of a system `(n, a)` if
    some `i ∈ {1, …, k}` satisfies `m % n i = a i`. -/
def isCoveredBy (n a : ℕ → ℕ) (m k : ℕ) : Prop :=
  ∃ i, 1 ≤ i ∧ i ≤ k ∧ m % n i = a i

/-- The residue classes: a_1 = 0, a_i = 2^(i-1) + 1 for i ≥ 2 -/
def seq_a : ℕ → ℕ
  | 0 => 0
  | 1 => 0
  | (n + 2) => 2 ^ (n + 1) + 1

/-- Concrete coverage: `m` is covered at level `k` by the counterexample system
    with moduli `n_i = 2^i` and residues `a_i = seq_a i`. -/
@[reducible] def isCovered (m k : ℕ) : Prop :=
  isCoveredBy (fun i => 2 ^ i) seq_a m k

lemma seq_a_succ (v : ℕ) (hv : 1 ≤ v) : seq_a (v + 1) = 2 ^ v + 1 := by
  cases v <;> trivial

lemma seq_a_lt (i : ℕ) (hi : 1 ≤ i) : seq_a i < 2 ^ i := by
  rcases i with (_ | _ | n) <;> simp_all +decide [pow_succ]
  exact show 2 ^ (n + 1) + 1 < 2 ^ (n + 2) by ring_nf; linarith [Nat.one_le_pow n 2 zero_lt_two]

lemma one_mod_ne_seq_a (i : ℕ) (hi : 1 ≤ i) : 1 % 2 ^ i ≠ seq_a i := by
  rcases i with (_ | _ | i) <;> simp_all +arith +decide [seq_a]

theorem one_not_covered (k : ℕ) : ¬ isCovered 1 k := by
  rintro ⟨i, hi₁, hi₂, hi₃⟩
  exact one_mod_ne_seq_a i hi₁ hi₃

theorem even_covered (k : ℕ) (hk : 1 ≤ k) (m : ℕ) (hm : Even m) :
    isCovered m k := by
  obtain ⟨m, rfl⟩ := hm
  exact ⟨1, by norm_num, hk, by cases m <;> simp_all +arith +decide⟩

lemma padic_val_ge_one (m : ℕ) (hm1 : 1 < m) (hmodd : ¬ Even m) :
    1 ≤ padicValNat 2 (m - 1) := by
  apply one_le_padicValNat_of_dvd (by omega)
  obtain ⟨k, rfl⟩ := Nat.not_even_iff_odd.mp hmodd
  simp +arith +decide

lemma padic_val_bound (m k : ℕ) (hm1 : 1 < m) (hmk : m < 2 ^ k) :
    padicValNat 2 (m - 1) + 1 ≤ k := by
  have hv_le : (2 ^ (padicValNat 2 (m - 1))) ∣ m - 1 := Nat.ordProj_dvd _ _
  exact Nat.lt_of_not_ge fun h =>
    absurd (Nat.le_of_dvd (Nat.sub_pos_of_lt hm1) hv_le)
      (by linarith [Nat.pow_le_pow_right two_pos h, Nat.sub_add_cancel hm1.le])

lemma odd_mod_eq (m : ℕ) (hm1 : 1 < m) (hmodd : ¬ Even m) :
    m % 2 ^ (padicValNat 2 (m - 1) + 1) = 2 ^ padicValNat 2 (m - 1) + 1 := by
  obtain ⟨v, q, hq_odd, hv⟩ :
      ∃ v q, q % 2 = 1 ∧ m - 1 = 2 ^ v * q ∧ padicValNat 2 (m - 1) = v := by
    use padicValNat 2 (m - 1), (m - 1) / 2 ^ padicValNat 2 (m - 1)
    refine ⟨Nat.mod_two_ne_zero.mp fun h => ?_,
      Eq.symm (Nat.mul_div_cancel' <| Nat.ordProj_dvd _ _), rfl⟩
    exact absurd (Nat.dvd_of_mod_eq_zero h) (Nat.not_dvd_ordCompl (by norm_num) (by omega))
  rcases m <;> simp_all +decide [Nat.pow_succ']
  rw [Nat.ModEq.symm]
  rotate_right
  exact 2 ^ padicValNat 2 (2 ^ v * q) + 1
  · rw [Nat.mod_eq_of_lt]
    grind
  · rw [padicValNat.mul] <;> norm_num [hm1.ne', hq_odd]
    rw [padicValNat.eq_zero_of_not_dvd (by rw [Nat.dvd_iff_mod_eq_zero]; aesop)]
    ring_nf; norm_num [Nat.ModEq, Nat.add_mod, Nat.mul_mod_mul_left]
    norm_num [mul_comm, Nat.mul_mod_mul_right]
    aesop

theorem odd_gt_one_covered (k : ℕ) (m : ℕ) (hmk : m < 2 ^ k)
    (hm1 : 1 < m) (hmodd : ¬ Even m) :
    isCovered m k := by
  use padicValNat 2 (m - 1) + 1
  exact ⟨Nat.le_add_left _ _, padic_val_bound m k hm1 hmk,
    by rw [odd_mod_eq m hm1 hmodd, seq_a_succ _ (padic_val_ge_one m hm1 hmodd)]⟩

/-- **Core theorem**: `m < 2^k` is uncovered iff `m = 1`. -/
theorem uncovered_iff_eq_one (k : ℕ) (hk : 1 ≤ k) (m : ℕ) (hm : m < 2 ^ k) :
    ¬ isCovered m k ↔ m = 1 := by
  by_cases heven : Even m <;> by_cases hle1 : m ≤ 1 <;>
    simp_all +decide [even_covered, odd_gt_one_covered]
  · aesop
  · grind +splitIndPred
  · interval_cases m <;> simp_all +decide [one_not_covered]
  · linarith

-- ============================================================================
-- Top-level packaging: Disproof of Erdős Problem 280
-- ============================================================================

/-- `isCoveredBy` is decidable, so we can filter finite sets by it. -/
noncomputable instance isCoveredBy_decidable (n a : ℕ → ℕ) (m k : ℕ) :
    Decidable (isCoveredBy n a m k) :=
  Classical.dec _

/-- The uncovered set below `2^k` as a `Finset`. -/
noncomputable def uncoveredFinset (k : ℕ) : Finset ℕ :=
  (Finset.range (2 ^ k)).filter (fun m => ¬ isCovered m k)

/-- The uncovered set equals `{1}` for `k ≥ 1`. -/
theorem uncoveredFinset_eq (k : ℕ) (hk : 1 ≤ k) :
    uncoveredFinset k = {1} := by
  ext m
  simp [uncoveredFinset]
  exact ⟨fun h => uncovered_iff_eq_one k hk m h.1 |>.1 h.2,
    fun h => h.symm ▸ ⟨one_lt_pow₀ (by decide) (by linarith), one_not_covered k⟩⟩

/-- The uncovered count is exactly 1. -/
theorem uncoveredFinset_card (k : ℕ) (hk : 1 ≤ k) :
    (uncoveredFinset k).card = 1 := by
  rw [uncoveredFinset_eq k hk]; simp

/-- `2^k ≥ k * k` for `k ≥ 4`. -/
theorem pow_two_ge_sq (k : ℕ) (hk : 4 ≤ k) : k * k ≤ 2 ^ k := by
  induction' hk with k hk ih <;> norm_num [Nat.pow_succ] at *
  nlinarith

/-- **Growth condition**: `2^k > 2 · k · log k` for all `k ≥ 1`.
    This establishes the hypothesis of Erdős Problem 280 with `ε = 1`. -/
theorem growth_condition (k : ℕ) (hk : 1 ≤ k) :
    (2 : ℝ) ^ k > (1 + 1) * ↑k * Real.log ↑k := by
  by_cases h₂ : k ≤ 5
  · interval_cases k <;> norm_num at *
    · exact Real.log_two_lt_d9.trans_le <| by norm_num
    · rw [show (3 : ℝ) = (2 ^ 1) * 1.5 by norm_num, Real.log_mul, Real.log_pow] <;> norm_num
      exact lt_of_le_of_lt
        (mul_le_mul_of_nonneg_left
          (add_le_add Real.log_two_lt_d9.le (Real.log_le_sub_one_of_pos (by norm_num)))
          (by norm_num))
        (by norm_num)
    · rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
      norm_num; have := Real.log_two_lt_d9; norm_num at *; linarith
    · rw [← Real.log_rpow, Real.log_lt_iff_lt_exp] <;> norm_num
      have := Real.exp_one_gt_d9.le; norm_num at *
      rw [show Real.exp 32 = (Real.exp 1) ^ 32 by rw [← Real.exp_nat_mul]; norm_num]
      exact lt_of_lt_of_le (by norm_num) (pow_le_pow_left₀ (by positivity) this _)
  · have h_exp : (2 : ℝ) ^ k > k ^ 2 := by
      exact mod_cast Nat.le_induction (by norm_num)
        (fun n hn ih => by norm_num [Nat.pow_succ] at *; nlinarith) k (not_le.mp h₂)
    have h_log : Real.log k ≤ k / 2 := by
      have := Real.log_le_sub_one_of_pos (by positivity : 0 < (k : ℝ) / 2)
      rw [Real.log_div] at this <;> norm_num at * <;>
        linarith [Real.log_le_sub_one_of_pos zero_lt_two]
    nlinarith [(by norm_cast : ¬ (k : ℝ) ≤ 5)]

/-- **Disproof of Erdős Problem 280.**

There exist sequences `n, a : ℕ → ℕ` with `n` strictly increasing and each `aᵢ`
a valid residue class modulo `nᵢ`, satisfying the growth bound
`nₖ > (1 + ε) · k · log k` with `ε = 1` for all `k ≥ 1`, yet having exactly
one uncovered residue below `nₖ` for every `k ≥ 1`.

Since the uncovered count is the constant `1`, it is `o(k)` as `k → ∞`,
contradicting the conjecture of Erdős Problem 280.

The concrete witnesses are `n i = 2^i`, `a 1 = 0`, `a i = 2^(i-1) + 1` for `i ≥ 2`,
and `ε = 1`. -/
theorem erdos_280_counterexample :
    ∃ (n a : ℕ → ℕ) (ε : ℝ),
      0 < ε ∧
      StrictMono n ∧
      (∀ i, 1 ≤ i → a i < n i) ∧
      (∀ k, 1 ≤ k → (n k : ℝ) > (1 + ε) * ↑k * Real.log ↑k) ∧
      (∀ k, 1 ≤ k →
        ((Finset.range (n k)).filter
          (fun m => ¬ isCoveredBy n a m k)).card = 1) ∧
      Filter.Tendsto
        (fun k : ℕ =>
          (((Finset.range (n k)).filter
            (fun m => ¬ isCoveredBy n a m k)).card : ℝ) / ↑k)
        Filter.atTop (nhds 0) := by
  refine ⟨fun i => 2 ^ i, seq_a, 1, by norm_num, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun i j hij => pow_lt_pow_right₀ (by norm_num) hij
  · exact fun i a => seq_a_lt i a
  · exact fun k hk => by have := growth_condition k hk; norm_num at *; linarith
  · intro k hk
    show (uncoveredFinset k).card = 1
    exact uncoveredFinset_card k hk
  · show Filter.Tendsto
        (fun k => ((uncoveredFinset k).card : ℝ) / ↑k) Filter.atTop (nhds 0)
    exact squeeze_zero_norm'
      (Filter.eventually_atTop.mpr ⟨1, fun n hn => by
        rw [show uncoveredFinset n = {1} from uncoveredFinset_eq n hn]
        norm_num⟩)
      tendsto_one_div_atTop_nhds_zero_nat

/-- **Erdős Problem 280 (the claim).**

For every infinite sequence `n₁ < n₂ < ⋯` of integers with associated residues
`aₖ (mod nₖ)`, such that for some `ε > 0` we have `nₖ > (1 + ε)·k·log k` for all `k`,
the count `#{ m < nₖ : m ≢ aᵢ (mod nᵢ) for 1 ≤ i ≤ k }` is **not** `o(k)`
(i.e. `count(k)/k` does **not** tend to `0`). -/
def Conjecture280 : Prop :=
  ∀ (n a : ℕ → ℕ), StrictMono n → (∀ i, 1 ≤ i → a i < n i) →
    (∃ ε : ℝ, 0 < ε ∧ ∀ k, 1 ≤ k → (n k : ℝ) > (1 + ε) * ↑k * Real.log ↑k) →
    ¬ Filter.Tendsto
        (fun k : ℕ =>
          (((Finset.range (n k)).filter
            (fun m => ¬ isCoveredBy n a m k)).card : ℝ) / ↑k)
        Filter.atTop (nhds 0)

/-- **Disproof of Erdős Problem 280.** The claim is false: Cambie's system
`nₖ = 2ᵏ`, `aₖ = 2^(k-1) + 1` satisfies all hypotheses yet leaves exactly one
uncovered residue below `nₖ` for every `k`, so the count is the constant `1`,
which *is* `o(k)`. -/
theorem erdos_280 : ¬ Conjecture280 := by
  intro hconj
  obtain ⟨n, a, ε, hε, hmono, hres, hgrowth, _hcard, htendsto⟩ := erdos_280_counterexample
  exact hconj n a hmono hres ⟨ε, hε, hgrowth⟩ htendsto

#print axioms erdos_280

theorem proof :
    ¬ ∀ (n a : ℕ → ℕ), StrictMono n → (∀ i, 1 ≤ i → a i < n i) →
      (∃ ε : ℝ, 0 < ε ∧
        ∀ k, 1 ≤ k → (n k : ℝ) > (1 + ε) * (k : ℝ) * Real.log (k : ℝ)) →
      ¬ Filter.Tendsto
        (fun k : ℕ =>
          (((@Finset.filter ℕ
            (fun m => ¬ ∃ i ∈ Finset.Icc 1 k, m % n i = a i)
            (Classical.decPred _)
            (Finset.range (n k))).card : ℕ) : ℝ) / (k : ℝ))
        Filter.atTop (nhds 0) := by
  simpa [Conjecture280, isCoveredBy, Finset.mem_Icc, and_assoc] using erdos_280

end Submissions.Erdos280ResidueCoverRefutation.Full
