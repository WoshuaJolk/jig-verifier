import Mathlib

namespace Erdos700

noncomputable def f (n : ℕ) : ℕ :=
  sInf {m | ∃ k, 1 < k ∧ k ≤ n / 2 ∧ m = Nat.gcd n (n.choose k)}

def fSet (n : ℕ) : Set ℕ :=
  {m | ∃ k, 1 < k ∧ k ≤ n / 2 ∧ m = Nat.gcd n (n.choose k)}

lemma f_eq (n : ℕ) : f n = sInf (fSet n) := rfl

lemma f_mem (n k : ℕ) (h1 : 1 < k) (h2 : k ≤ n / 2) :
    Nat.gcd n (n.choose k) ∈ fSet n := ⟨k, h1, h2, rfl⟩

lemma f_le (n k : ℕ) (h1 : 1 < k) (h2 : k ≤ n / 2) :
    f n ≤ Nat.gcd n (n.choose k) := Nat.sInf_le (f_mem n k h1 h2)

lemma prime_dvd_of_not_dvd_choose (P n k : ℕ) (hP : P.Prime)
    (hPn : P ∣ n) (h : ¬ P ∣ n.choose k) : P ∣ k := by
  let _ := Fact.mk hP
  by_contra hk
  apply h
  have hmod : n.choose k ≡
      (n % P).choose (k % P) * (n / P).choose (k / P) [MOD P] :=
    Choose.choose_modEq_choose_mod_mul_choose_div_nat
  have hn0 : n % P = 0 := by
    have hz := (Nat.modEq_zero_iff_dvd).2 hPn
    simpa [Nat.ModEq, Nat.zero_mod] using hz
  have hkP : 0 < k % P :=
    Nat.pos_of_ne_zero (fun hh => hk (Nat.dvd_of_mod_eq_zero hh))
  rw [hn0, Nat.choose_eq_zero_of_lt hkP, zero_mul] at hmod
  exact (Nat.modEq_zero_iff_dvd).1 hmod

end Erdos700


open Filter Real

theorem Erdos700PNT.eventually_primeCounting_sixteen_interval :
    ∀ᶠ x : ℝ in atTop,
      x / (10 * log x) ≤
        (Nat.primeCounting ⌊16 * x⌋₊ : ℝ) -
          (Nat.primeCounting ⌊x⌋₊ : ℝ) := by
  have hupper := Chebyshev.eventually_primeCounting_le (ε := (1 : ℝ)) one_pos
  have hscale : Tendsto (fun x : ℝ ↦ 16 * x + 2) atTop atTop := by
    exact tendsto_atTop_add_const_right _ _
      (tendsto_id.const_mul_atTop (by norm_num : (0 : ℝ) < 16))
  have hlogsmall :=
    hscale.eventually (Real.isLittleO_log_id_atTop.bound (by norm_num : (0 : ℝ) < 1 / 100))
  filter_upwards [hupper, hlogsmall, eventually_ge_atTop (Real.exp 10)] with
      x hupper hlogsmall hx
  have hxpos : 0 < x := (Real.exp_pos 10).trans_le hx
  have hxone : 1 ≤ x := by
    have : 1 ≤ Real.exp 10 := (Real.one_le_exp_iff.mpr (by norm_num))
    exact this.trans hx
  have hlogx : 10 ≤ log x := by
    rw [← Real.exp_le_exp]
    simpa [Real.exp_log hxpos] using hx
  have hlogxpos : 0 < log x := by linarith
  have hlogtwo_lower : (69 / 100 : ℝ) < log 2 :=
    (by norm_num : (69 / 100 : ℝ) < 0.6931471803).trans log_two_gt_d9
  have hlogtwo_upper : log 2 < (7 / 10 : ℝ) :=
    log_two_lt_d9.trans (by norm_num)
  have hlog16 : log (16 : ℝ) = 4 * log 2 := by
    calc
      log (16 : ℝ) = log ((2 : ℝ) ^ 4) := by norm_num
      _ = 4 * log 2 := by simpa using Real.log_pow (2 : ℝ) 4
  have hlog4 : log (4 : ℝ) = 2 * log 2 := by
    calc
      log (4 : ℝ) = log ((2 : ℝ) ^ 2) := by norm_num
      _ = 2 * log 2 := by simpa using Real.log_pow (2 : ℝ) 2
  have hlog16x : log (16 * x) = log 16 + log x := by
    rw [Real.log_mul (by norm_num : (16 : ℝ) ≠ 0) hxpos.ne']
  have hlog16xpos : 0 < log (16 * x) := Real.log_pos (by nlinarith)
  have hlog16x_le : log (16 * x) ≤ 2 * log x := by
    rw [hlog16x, hlog16]
    nlinarith
  have hypos : 0 < 16 * x + 2 := by positivity
  have hlogy_nonneg : 0 ≤ log (16 * x + 2) := Real.log_nonneg (by nlinarith)
  have hlogy :
      log (16 * x + 2) ≤ (1 / 100 : ℝ) * (16 * x + 2) := by
    rw [Real.norm_eq_abs, abs_of_nonneg hlogy_nonneg,
      Real.norm_eq_abs, id_eq, abs_of_pos hypos] at hlogsmall
    simpa using hlogsmall
  have hnum :
      10 * x ≤ (16 * x - 1) * log 2 - log (16 * x + 2) := by
    nlinarith
  have hlower_raw := Chebyshev.pi_ge' (x := 16 * x) (by nlinarith : 1 < 16 * x)
  have hlower : 5 * (x / log x) ≤ (Nat.primeCounting ⌊16 * x⌋₊ : ℝ) := by
    calc
      5 * (x / log x)
          = (10 * x) / (2 * log x) := by field_simp <;> ring
      _ ≤ ((16 * x - 1) * log 2 - log (16 * x + 2)) / log (16 * x) := by
        exact div_le_div₀ (by linarith) hnum hlog16xpos hlog16x_le
      _ ≤ (Nat.primeCounting ⌊16 * x⌋₊ : ℝ) := hlower_raw
  have hupper' :
      (Nat.primeCounting ⌊x⌋₊ : ℝ) ≤ 3 * (x / log x) := by
    calc
      (Nat.primeCounting ⌊x⌋₊ : ℝ)
          ≤ (log 4 + 1) * x / log x := by exact_mod_cast hupper
      _ = (log 4 + 1) * (x / log x) := by ring
      _ ≤ 3 * (x / log x) := by
        rw [hlog4]
        have hxlog : 0 ≤ x / log x := div_nonneg hxpos.le hlogxpos.le
        nlinarith
  have htarget : x / (10 * log x) = (1 / 10 : ℝ) * (x / log x) := by
    field_simp
    <;> ring
  rw [htarget]
  have hxlog : 0 ≤ x / log x := div_nonneg hxpos.le hlogxpos.le
  nlinarith


namespace Erdos700PNT

theorem eventually_primeCounting_eight_cube_interval :
    ∀ᶠ T : ℕ in Filter.atTop,
      ((8 * T ^ 3 : ℕ) : ℝ) /
          (10 * Real.log (((8 * T ^ 3 : ℕ) : ℝ))) ≤
        (Nat.primeCounting (128 * T ^ 3) : ℝ) -
          (Nat.primeCounting (8 * T ^ 3) : ℝ) := by
  have hscale :
      Filter.Tendsto (fun T : ℕ ↦ (8 : ℝ) * (T : ℝ) ^ 3)
        Filter.atTop Filter.atTop := by
    exact (tendsto_const_mul_pow_atTop (by norm_num : (3 : ℕ) ≠ 0)
      (by norm_num : (0 : ℝ) < 8)).comp tendsto_natCast_atTop_atTop
  have h := hscale.eventually eventually_primeCounting_sixteen_interval
  filter_upwards [h] with T hT
  have h8 : (8 : ℝ) * (T : ℝ) ^ 3 = ((8 * T ^ 3 : ℕ) : ℝ) := by
    norm_num [Nat.cast_mul, Nat.cast_pow]
  have h128 : (16 : ℝ) * ((8 * T ^ 3 : ℕ) : ℝ) =
      ((128 * T ^ 3 : ℕ) : ℝ) := by
    norm_num [Nat.cast_mul, Nat.cast_pow]
    <;> ring
  have hfloor8 : ⌊(8 : ℝ) * (T : ℝ) ^ 3⌋₊ = 8 * T ^ 3 := by
    exact (congrArg (fun z : ℝ ↦ ⌊z⌋₊) h8).trans (Nat.floor_natCast _)
  have hfloor128 :
      ⌊(16 : ℝ) * ((8 : ℝ) * (T : ℝ) ^ 3)⌋₊ = 128 * T ^ 3 := by
    have hreal :
        (16 : ℝ) * ((8 : ℝ) * (T : ℝ) ^ 3) =
          ((128 * T ^ 3 : ℕ) : ℝ) :=
      (congrArg (fun z : ℝ ↦ (16 : ℝ) * z) h8).trans h128
    exact (congrArg (fun z : ℝ ↦ ⌊z⌋₊) hreal).trans (Nat.floor_natCast _)
  rw [hfloor8, hfloor128] at hT
  simpa [Nat.cast_mul, Nat.cast_pow] using hT

theorem eventually_primeCounting_eight_cube_interval_nat_sub :
    ∀ᶠ T : ℕ in Filter.atTop,
      ((8 * T ^ 3 : ℕ) : ℝ) /
          (10 * Real.log (((8 * T ^ 3 : ℕ) : ℝ))) ≤
        ((Nat.primeCounting (128 * T ^ 3) -
          Nat.primeCounting (8 * T ^ 3) : ℕ) : ℝ) := by
  filter_upwards [eventually_primeCounting_eight_cube_interval] with T hT
  have hendpoints : 8 * T ^ 3 ≤ 128 * T ^ 3 := by omega
  have hcounts :
      Nat.primeCounting (8 * T ^ 3) ≤ Nat.primeCounting (128 * T ^ 3) :=
    Nat.monotone_primeCounting hendpoints
  rwa [Nat.cast_sub hcounts]

end Erdos700PNT


/-! Flattened from PackingWork/AsymmetricGap.lean. -/


/-!
# A finite asymmetric-gap lemma

The proof is the elementary "exponentially growing suffix gaps" argument used
in the PNT route to Erdős 700(ii).  If

`x₀ < x₁ < ... < xₙ < z`

and no adjacent pair `xᵢ < xᵢ₊₁ < z` satisfies

`z - xᵢ₊₁ > xᵢ₊₁ - xᵢ`,

then every suffix distance is at least twice the next one.  Consequently
`z - x₀ ≥ 2ⁿ`.
-/

namespace Erdos700PNT.PackingWork

/-- An adjacent pair in `xs` forms an asymmetric triple with the final point
`z`.  The decomposition records adjacency without introducing list indices. -/
def HasAsymmetricAdjacentPair (z : ℕ) (xs : List ℕ) : Prop :=
  ∃ pre x y post,
    xs = pre ++ x :: y :: post ∧
      z - y > y - x

/-- The exponential suffix-gap bound, stated contrapositively in a form that is
convenient for induction. -/
theorem pow_two_le_span_of_no_asymmetric_adjacent
    (z x : ℕ) (xs : List ℕ)
    (hinc : (x :: xs ++ [z]).Pairwise (· < ·))
    (hno : ¬ HasAsymmetricAdjacentPair z (x :: xs)) :
    2 ^ xs.length ≤ z - x := by
  induction xs generalizing x with
  | nil =>
      have hxz : x < z := List.rel_of_pairwise_cons hinc (by simp)
      simp only [List.length_nil, pow_zero]
      omega
  | cons y ys ih =>
      have hxy : x < y := List.rel_of_pairwise_cons hinc (by simp)
      have htail : (y :: ys ++ [z]).Pairwise (· < ·) := by
        exact hinc.of_cons
      have hyz : y < z := List.rel_of_pairwise_cons htail (by simp)
      have hno_head : ¬ z - y > y - x := by
        intro h
        apply hno
        refine ⟨[], x, y, ys, ?_, h⟩
        simp
      have hno_tail : ¬ HasAsymmetricAdjacentPair z (y :: ys) := by
        intro h
        rcases h with ⟨pre, a, b, post, hdecomp, hab⟩
        apply hno
        refine ⟨x :: pre, a, b, post, ?_, hab⟩
        simp [hdecomp]
      have hpow : 2 ^ ys.length ≤ z - y :=
        ih y htail hno_tail
      have hdouble : 2 * (z - y) ≤ z - x := by
        have hle : z - y ≤ y - x := by omega
        omega
      rw [List.length_cons, pow_succ]
      omega

/-- If an increasing finite chain is too long for its span, one of its
adjacent pairs forms the desired asymmetric triple with the final point. -/
theorem exists_asymmetric_adjacent_of_span_lt_pow_two
    (z x : ℕ) (xs : List ℕ)
    (hinc : (x :: xs ++ [z]).Pairwise (· < ·))
    (hspan : z - x < 2 ^ xs.length) :
    HasAsymmetricAdjacentPair z (x :: xs) := by
  by_contra hno
  exact (Nat.not_le.mpr hspan)
    (pow_two_le_span_of_no_asymmetric_adjacent z x xs hinc hno)

/-- Membership-oriented version: a sufficiently dense increasing list contains
three entries `p < q < r` with `r - q > q - p`.  Here `r` is the final point,
which is enough for the interval-packing application. -/
theorem exists_asymmetric_triple_with_last
    (z x : ℕ) (xs : List ℕ)
    (hinc : (x :: xs ++ [z]).Pairwise (· < ·))
    (hspan : z - x < 2 ^ xs.length) :
    ∃ p ∈ x :: xs, ∃ q ∈ x :: xs,
      p < q ∧ q < z ∧ z - q > q - p := by
  rcases exists_asymmetric_adjacent_of_span_lt_pow_two z x xs hinc hspan with
    ⟨pre, p, q, post, hdecomp, hasym⟩
  have hinc' : (pre ++ p :: q :: post ++ [z]).Pairwise (· < ·) := by
    rw [← hdecomp]
    simpa only [List.cons_append] using hinc
  have hsuffix : (p :: q :: post ++ [z]).Pairwise (· < ·) := by
    simpa using List.Pairwise.drop (i := pre.length) hinc'
  have hpq : p < q := by
    exact List.rel_of_pairwise_cons hsuffix (by simp)
  have hqz : q < z := by
    exact List.rel_of_pairwise_cons hsuffix.of_cons (by simp)
  refine ⟨p, ?_, q, ?_, hpq, hqz, hasym⟩ <;>
    simp [hdecomp]


end Erdos700PNT.PackingWork

/-! Flattened from PackingWork/IntervalPacking.lean. -/


/-!
# Packing a finite set into equal half-open intervals

This file separates the finite pigeonhole step from the analytic prime-counting
input.  No primality assumption is needed here.
-/

namespace Erdos700PNT.PackingWork

/-- A generic finite-set pigeonhole lemma with `B` explicitly numbered bins. -/
theorem exists_large_numbered_bin
    (s : Finset ℕ) (bin : ℕ → ℕ) (B K : ℕ)
    (hbin : ∀ n ∈ s, bin n < B)
    (hcard : B * K < s.card) :
    ∃ i < B, K < (s.filter fun n => bin n = i).card := by
  classical
  have hmaps : ∀ n ∈ s, bin n ∈ Finset.range B := by
    intro n hn
    exact Finset.mem_range.mpr (hbin n hn)
  simpa using
    (Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to
      (s := s) (t := Finset.range B) (f := bin) hmaps (by simpa using hcard))

/-- If more than `B*K` points lie in `[N, N+B*T)`, one of its `B`
half-open subintervals of length `T` contains more than `K` points. -/
theorem exists_large_half_open_interval
    (s : Finset ℕ) (N T B K : ℕ)
    (hT : 0 < T)
    (hbounds : ∀ n ∈ s, N ≤ n ∧ n < N + B * T)
    (hcard : B * K < s.card) :
    ∃ i < B,
      K < (s.filter fun n => N + i * T ≤ n ∧ n < N + (i + 1) * T).card := by
  classical
  let bin : ℕ → ℕ := fun n => (n - N) / T
  have hbin : ∀ n ∈ s, bin n < B := by
    intro n hn
    have hn_bounds := hbounds n hn
    apply (Nat.div_lt_iff_lt_mul hT).mpr
    omega
  obtain ⟨i, hiB, hi⟩ :=
    exists_large_numbered_bin s bin B K hbin hcard
  have heq :
      (s.filter fun n => bin n = i) =
        (s.filter fun n => N + i * T ≤ n ∧ n < N + (i + 1) * T) := by
    ext n
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hns, hquot⟩
      have hn_bounds := hbounds n hns
      have hl0 : (n - N) / T * T ≤ n - N :=
        Nat.div_mul_le_self (n - N) T
      have hl : i * T ≤ n - N := by
        simpa [bin, hquot] using hl0
      have hu : n - N < (i + 1) * T := by
        apply (Nat.div_lt_iff_lt_mul hT).mp
        simp [bin, hquot]
      constructor <;> omega
    · rintro ⟨hns, hlo, hhi⟩
      have hNn : N ≤ n := by omega
      have hl : i * T ≤ n - N := by omega
      have hu : n - N < (i + 1) * T := by omega
      have hi_le : i ≤ (n - N) / T :=
        (Nat.le_div_iff_mul_le hT).mpr hl
      have hdiv_lt : (n - N) / T < i + 1 :=
        (Nat.div_lt_iff_lt_mul hT).mpr hu
      refine ⟨hns, ?_⟩
      simp only [bin]
      omega
  refine ⟨i, hiB, ?_⟩
  rwa [heq] at hi


end Erdos700PNT.PackingWork

/-! Flattened from PackingWork/DenseInterval.lean. -/


/-!
# Dense finite sets contain asymmetric triples

This composes sorting, the exponential suffix-gap lemma, and equal-interval
packing.  The final theorem is specialized to the exact interval
`[8*T^3, 16*T^3)` used in the PNT proof of Erdős 700(ii).
-/

namespace Erdos700PNT.PackingWork

/-- More than `K+2` points in a half-open interval of length `T`, together with
`T < 2^(K+1)`, force an asymmetric triple. -/
theorem dense_finset_has_asymmetric_triple
    (s : Finset ℕ) (A T K : ℕ)
    (hbounds : ∀ n ∈ s, A ≤ n ∧ n < A + T)
    (hcard : K + 2 < s.card)
    (hpow : T < 2 ^ (K + 1)) :
    ∃ p ∈ s, ∃ q ∈ s, ∃ r ∈ s,
      p < q ∧ q < r ∧ r - q > q - p ∧ r - p < T := by
  classical
  let l : List ℕ := s.sort
  have hlen : K + 2 < l.length := by
    simpa [l] using hcard
  cases hl : l with
  | nil =>
      simp [hl] at hlen
  | cons x tail =>
      have htail : tail ≠ [] := by
        intro hnil
        rw [hnil] at hl
        simp [hl] at hlen
      let z : ℕ := tail.getLast htail
      let xs : List ℕ := tail.dropLast
      have hdecomp : l = x :: xs ++ [z] := by
        rw [hl]
        simp only [xs, z]
        simp only [List.cons_append]
        rw [List.dropLast_append_getLast htail]
      have hinc : (x :: xs ++ [z]).Pairwise (· < ·) := by
        rw [← hdecomp]
        exact (Finset.sortedLT_sort s).pairwise
      have hx_l : x ∈ l := by
        rw [hdecomp]
        simp
      have hz_l : z ∈ l := by
        rw [hdecomp]
        simp
      have hx_s : x ∈ s := by
        simpa [l] using hx_l
      have hz_s : z ∈ s := by
        simpa [l] using hz_l
      have hxs_len : K < xs.length := by
        have hlen_eq : l.length = xs.length + 2 := by
          rw [hdecomp]
          simp
        omega
      have hx_bounds := hbounds x hx_s
      have hz_bounds := hbounds z hz_s
      have hzxT : z - x < T := by omega
      have hpow_mono : 2 ^ (K + 1) ≤ 2 ^ xs.length :=
        Nat.pow_le_pow_right (by decide) (by omega)
      have hspan : z - x < 2 ^ xs.length :=
        hzxT.trans (hpow.trans_le hpow_mono)
      obtain ⟨p, hp, q, hq, hpq, hqz, hasym⟩ :=
        exists_asymmetric_triple_with_last z x xs hinc hspan
      have hp_l : p ∈ l := by
        rw [hdecomp]
        exact List.mem_append_left [z] hp
      have hq_l : q ∈ l := by
        rw [hdecomp]
        exact List.mem_append_left [z] hq
      have hp_s : p ∈ s := by
        simpa [l] using hp_l
      have hq_s : q ∈ s := by
        simpa [l] using hq_l
      have hp_bounds := hbounds p hp_s
      have hzpT : z - p < T := by omega
      exact ⟨p, hp_s, q, hq_s, z, hz_s, hpq, hqz, hasym, hzpT⟩

/-- Equal-interval packing followed by the dense-interval asymmetric-gap
argument. -/
theorem packed_finset_has_asymmetric_triple
    (s : Finset ℕ) (N T B K : ℕ)
    (hT : 0 < T)
    (hbounds : ∀ n ∈ s, N ≤ n ∧ n < N + B * T)
    (hcard : B * (K + 2) < s.card)
    (hpow : T < 2 ^ (K + 1)) :
    ∃ p ∈ s, ∃ q ∈ s, ∃ r ∈ s,
      N ≤ p ∧ p < q ∧ q < r ∧
        r - q > q - p ∧ r - p < T := by
  classical
  obtain ⟨i, hiB, hi⟩ :=
    exists_large_half_open_interval s N T B (K + 2) hT hbounds hcard
  let box : Finset ℕ :=
    s.filter fun n => N + i * T ≤ n ∧ n < N + (i + 1) * T
  have hbox_bounds :
      ∀ n ∈ box, N + i * T ≤ n ∧ n < N + i * T + T := by
    intro n hn
    simp only [box, Finset.mem_filter] at hn
    constructor
    · exact hn.2.1
    · convert hn.2.2 using 1 <;> ring
  have hbox_card : K + 2 < box.card := by
    simpa [box] using hi
  obtain ⟨p, hp, q, hq, r, hr, hpq, hqr, hasym, hrpT⟩ :=
    dense_finset_has_asymmetric_triple box (N + i * T) T K
      hbox_bounds hbox_card hpow
  have hp' : p ∈ s := (Finset.mem_filter.mp hp).1
  have hq' : q ∈ s := (Finset.mem_filter.mp hq).1
  have hr' : r ∈ s := (Finset.mem_filter.mp hr).1
  have hNp : N ≤ p := by
    have := (hbox_bounds p hp).1
    omega
  exact ⟨p, hp', q, hq', r, hr', hNp, hpq, hqr, hasym, hrpT⟩

/-- The exact `8*T^3` packing geometry used by the PNT route. -/
theorem eight_cube_interval_has_asymmetric_triple
    (s : Finset ℕ) (T K : ℕ)
    (hT : 0 < T)
    (hbounds : ∀ n ∈ s, 8 * T ^ 3 ≤ n ∧ n < 128 * T ^ 3)
    (hcard : (120 * T ^ 2) * (K + 2) < s.card)
    (hpow : T < 2 ^ (K + 1)) :
    ∃ p ∈ s, ∃ q ∈ s, ∃ r ∈ s,
      8 * T ^ 3 ≤ p ∧ p < q ∧ q < r ∧
        r - q > q - p ∧ r - p < T := by
  have hbounds' :
      ∀ n ∈ s, 8 * T ^ 3 ≤ n ∧
        n < 8 * T ^ 3 + (120 * T ^ 2) * T := by
    intro n hn
    have h := hbounds n hn
    exact ⟨h.1, h.2.trans_le (by ring_nf; exact le_rfl)⟩
  exact packed_finset_has_asymmetric_triple
    s (8 * T ^ 3) T (120 * T ^ 2) K hT hbounds' hcard hpow

/-- Closed-right version matching
`primeCounting (16*T^3) - primeCounting (8*T^3)`, which counts primes in
`(8*T^3, 16*T^3]`.  Adding one to both half-open endpoints removes the
off-by-one issue without changing either the number or the length of boxes. -/
theorem eight_cube_right_closed_interval_has_asymmetric_triple
    (s : Finset ℕ) (T K : ℕ)
    (hT : 0 < T)
    (hbounds : ∀ n ∈ s, 8 * T ^ 3 < n ∧ n ≤ 128 * T ^ 3)
    (hcard : (120 * T ^ 2) * (K + 2) < s.card)
    (hpow : T < 2 ^ (K + 1)) :
    ∃ p ∈ s, ∃ q ∈ s, ∃ r ∈ s,
      8 * T ^ 3 ≤ p ∧ p < q ∧ q < r ∧
        r - q > q - p ∧ r - p < T := by
  have hbounds' :
      ∀ n ∈ s, 8 * T ^ 3 + 1 ≤ n ∧
        n < (8 * T ^ 3 + 1) + (120 * T ^ 2) * T := by
    intro n hn
    have h := hbounds n hn
    constructor
    · omega
    · have hgeom :
          (8 * T ^ 3 + 1) + (120 * T ^ 2) * T =
            128 * T ^ 3 + 1 := by
          ring_nf
      rw [hgeom]
      omega
  obtain ⟨p, hp, q, hq, r, hr, hNp, hpq, hqr, hasym, hrpT⟩ :=
    packed_finset_has_asymmetric_triple
      s (8 * T ^ 3 + 1) T (120 * T ^ 2) K hT hbounds' hcard hpow
  exact ⟨p, hp, q, hq, r, hr, by omega, hpq, hqr, hasym, hrpT⟩


end Erdos700PNT.PackingWork

/-! Flattened from DominanceWork/Dominance.lean. -/


open Filter Real Asymptotics

namespace Erdos700PNT

/--
The elementary analytic estimate behind the packing argument.  The deliberately
loose constant is chosen so that the later comparison with `Nat.log 2 T` is
transparent.
-/
theorem eventually_log_square_dominated :
    ∀ᶠ x : ℝ in atTop, (1800 / log 2) * log x ^ 2 < x := by
  have hlogtwo : 0 < log (2 : ℝ) := Real.log_pos (by norm_num)
  have hlittle :
      (fun x : ℝ ↦ (1800 / log 2) * log x ^ 2) =o[atTop] id :=
    Real.isLittleO_pow_log_id_atTop.const_mul_left (1800 / log 2)
  have hbound := hlittle.def (by norm_num : (0 : ℝ) < 1 / 2)
  filter_upwards [hbound, eventually_gt_atTop (0 : ℝ)] with x hx hxpos
  have hcoef : 0 ≤ 1800 / log 2 := (div_pos (by norm_num) hlogtwo).le
  have hleft : 0 ≤ (1800 / log 2) * log x ^ 2 :=
    mul_nonneg hcoef (sq_nonneg _)
  have hx' : (1800 / log 2) * log x ^ 2 ≤ (1 / 2 : ℝ) * x := by
    simpa [Real.norm_eq_abs, abs_of_nonneg hleft, abs_of_pos hxpos,
      abs_of_pos hlogtwo] using hx
  linarith

/--
For large natural `T`, the exact logarithmic expression needed after cancelling
`8*T^2` from the PNT lower bound is strictly smaller than `T`.
-/
theorem eventually_log_budget_lt :
    ∀ᶠ T : ℕ in atTop,
      150 * log (((8 * T ^ 3 : ℕ) : ℝ)) *
          (((Nat.log 2 T : ℕ) : ℝ) + 2) < (T : ℝ) := by
  have hdom :
      ∀ᶠ T : ℕ in atTop,
        (1800 / log 2) * log (T : ℝ) ^ 2 < (T : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually eventually_log_square_dominated
  filter_upwards [hdom, eventually_ge_atTop (8 : ℕ)] with T hdomT hT
  have hTpos_nat : 0 < T := by omega
  have hTpos : 0 < (T : ℝ) := by positivity
  have hlogtwo : 0 < log (2 : ℝ) := Real.log_pos (by norm_num)
  have hlogT : 0 < log (T : ℝ) := Real.log_pos (by
    exact_mod_cast (show 1 < T by omega))
  have hlog8_le : log (8 : ℝ) ≤ log (T : ℝ) := by
    exact Real.strictMonoOn_log.monotoneOn
      (by norm_num : (8 : ℝ) ∈ Set.Ioi 0)
      (show 0 < (T : ℝ) from hTpos)
      (by exact_mod_cast hT)
  have hlog_cube :
      log (((8 * T ^ 3 : ℕ) : ℝ)) =
        log (8 : ℝ) + 3 * log (T : ℝ) := by
    rw [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow, Real.log_mul
      (by norm_num : (8 : ℝ) ≠ 0) (pow_ne_zero 3 hTpos.ne')]
    rw [Real.log_pow]
    norm_num
  have hlogN_le :
      log (((8 * T ^ 3 : ℕ) : ℝ)) ≤ 4 * log (T : ℝ) := by
    rw [hlog_cube]
    linarith
  have hnatlog :
      ((Nat.log 2 T : ℕ) : ℝ) ≤ log (T : ℝ) / log 2 := by
    simpa [Real.logb] using Real.natLog_le_logb T 2
  have hlogtwo_le_logT : log (2 : ℝ) ≤ log (T : ℝ) := by
    exact Real.strictMonoOn_log.monotoneOn
      (by norm_num : (2 : ℝ) ∈ Set.Ioi 0)
      (show 0 < (T : ℝ) from hTpos)
      (by exact_mod_cast (show 2 ≤ T by omega))
  have htwo_le : (2 : ℝ) ≤ 2 * (log (T : ℝ) / log 2) := by
    have hratio : (1 : ℝ) ≤ log (T : ℝ) / log 2 := by
      exact (le_div_iff₀ hlogtwo).2 (by simpa using hlogtwo_le_logT)
    linarith
  have hlogcount :
      ((Nat.log 2 T : ℕ) : ℝ) + 2 ≤
        (3 / log 2) * log (T : ℝ) := by
    have hsum :
        ((Nat.log 2 T : ℕ) : ℝ) + 2 ≤
          3 * (log (T : ℝ) / log 2) := by
      linarith
    calc
      ((Nat.log 2 T : ℕ) : ℝ) + 2
          ≤ 3 * (log (T : ℝ) / log 2) := hsum
      _ = (3 / log 2) * log (T : ℝ) := by ring
  have hlogNpos : 0 < log (((8 * T ^ 3 : ℕ) : ℝ)) := by
    rw [hlog_cube]
    positivity
  have hcount_nonneg : 0 ≤ ((Nat.log 2 T : ℕ) : ℝ) + 2 := by positivity
  calc
    150 * log (((8 * T ^ 3 : ℕ) : ℝ)) *
          (((Nat.log 2 T : ℕ) : ℝ) + 2)
        ≤ 150 * (4 * log (T : ℝ)) *
            ((3 / log 2) * log (T : ℝ)) := by
              gcongr
    _ = (1800 / log 2) * log (T : ℝ) ^ 2 := by ring
    _ < (T : ℝ) := hdomT

/--
The exact real inequality needed to combine the PNT interval lower bound with
the finite pigeonhole argument.
-/
theorem eventually_packing_threshold_lt_pnt_lower_bound :
    ∀ᶠ T : ℕ in atTop,
      ((120 * T ^ 2 * (Nat.log 2 T + 2) : ℕ) : ℝ) <
        ((8 * T ^ 3 : ℕ) : ℝ) /
          (10 * log (((8 * T ^ 3 : ℕ) : ℝ))) := by
  filter_upwards [eventually_log_budget_lt, eventually_ge_atTop (8 : ℕ)] with
      T hbudget hT
  have hTpos_nat : 0 < T := by omega
  have hTpos : 0 < (T : ℝ) := by positivity
  have hlogNpos : 0 < log (((8 * T ^ 3 : ℕ) : ℝ)) := by
    have hNgt : (1 : ℝ) < ((8 * T ^ 3 : ℕ) : ℝ) := by
      have hcube : 1 ≤ T ^ 3 :=
        Nat.one_le_iff_ne_zero.mpr (pow_ne_zero 3 hTpos_nat.ne')
      exact_mod_cast (show 1 < 8 * T ^ 3 by omega)
    exact Real.log_pos hNgt
  have hdenpos :
      0 < 10 * log (((8 * T ^ 3 : ℕ) : ℝ)) := mul_pos (by norm_num) hlogNpos
  have hscale : 0 < (8 : ℝ) * (T : ℝ) ^ 2 := by positivity
  have hscaled :
      ((8 : ℝ) * (T : ℝ) ^ 2) *
          (150 * log (((8 * T ^ 3 : ℕ) : ℝ)) *
            (((Nat.log 2 T : ℕ) : ℝ) + 2)) <
        ((8 : ℝ) * (T : ℝ) ^ 2) * (T : ℝ) :=
    mul_lt_mul_of_pos_left hbudget hscale
  rw [lt_div_iff₀ hdenpos]
  norm_num [Nat.cast_mul, Nat.cast_add, Nat.cast_pow] at hscaled ⊢
  nlinarith

/--
Consequently, the actual natural prime-count difference is eventually strictly
larger than the number of boxes times the allowed occupancy.
-/
theorem eventually_packing_threshold_lt_prime_count :
    ∀ᶠ T : ℕ in atTop,
      120 * T ^ 2 * (Nat.log 2 T + 2) <
        Nat.primeCounting (128 * T ^ 3) -
          Nat.primeCounting (8 * T ^ 3) := by
  filter_upwards
    [eventually_packing_threshold_lt_pnt_lower_bound,
      eventually_primeCounting_eight_cube_interval_nat_sub] with T hthreshold hpnt
  exact_mod_cast hthreshold.trans_le hpnt


end Erdos700PNT

/-! Flattened from PackingWork/PrimeBoxes.lean. -/


/-!
# From the PNT count to asymmetric prime triples

The prime-counting difference `π(16*T^3) - π(8*T^3)` is exactly the cardinality
of the primes in the closed-right interval `(8*T^3, 16*T^3]`.  This file feeds
that finite set to the packing theorem.
-/

open Filter

namespace Erdos700PNT.PackingWork

/-- The finite set of primes in `(a,b]`. -/
def primesIoc (a b : ℕ) : Finset ℕ :=
  (Finset.Ioc a b).filter Nat.Prime

theorem card_primesIoc (a b : ℕ) (hab : a ≤ b) :
    (primesIoc a b).card =
      Nat.primeCounting b - Nat.primeCounting a := by
  classical
  have heq :
      primesIoc a b =
        (Finset.range (b + 1)).filter Nat.Prime \
          (Finset.range (a + 1)).filter Nat.Prime := by
    ext p
    simp only [primesIoc, Finset.mem_filter, Finset.mem_Ioc,
      Finset.mem_sdiff, Finset.mem_range]
    by_cases hp : p.Prime <;> simp [hp] <;> omega
  have hsub :
      (Finset.range (a + 1)).filter Nat.Prime ⊆
        (Finset.range (b + 1)).filter Nat.Prime := by
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_range] at hp ⊢
    exact ⟨by omega, hp.2⟩
  rw [heq, Finset.card_sdiff_of_subset hsub]
  simp only [Nat.primeCounting, Nat.primeCounting',
    Nat.count_eq_card_filter_range]

/-- The PNT lower bound and finite packing produce the exact asymmetric prime
triple needed by the structural Erdős-700 argument, for all sufficiently large
`T`. -/
theorem eventually_exists_asymmetric_prime_triple :
    ∀ᶠ T : ℕ in atTop,
      ∃ p q r : ℕ,
        p.Prime ∧ q.Prime ∧ r.Prime ∧
          8 * T ^ 3 ≤ p ∧ p < q ∧ q < r ∧
            r - q > q - p ∧ r - p < T := by
  filter_upwards
      [Erdos700PNT.eventually_packing_threshold_lt_prime_count,
        eventually_ge_atTop (1 : ℕ)] with T hcount hT
  let s : Finset ℕ := primesIoc (8 * T ^ 3) (128 * T ^ 3)
  have hendpoints : 8 * T ^ 3 ≤ 128 * T ^ 3 := by omega
  have hcard :
      (120 * T ^ 2) * (Nat.log 2 T + 2) < s.card := by
    simpa [s, card_primesIoc _ _ hendpoints] using hcount
  have hbounds :
      ∀ n ∈ s, 8 * T ^ 3 < n ∧ n ≤ 128 * T ^ 3 := by
    intro n hn
    exact (Finset.mem_Ioc.mp (Finset.mem_filter.mp hn).1)
  have hpow : T < 2 ^ (Nat.log 2 T + 1) := by
    simpa [Nat.succ_eq_add_one] using
      (Nat.lt_pow_succ_log_self (by decide : 1 < 2) T)
  obtain ⟨p, hp, q, hq, r, hr, hNp, hpq, hqr, hasym, hrpT⟩ :=
    eight_cube_right_closed_interval_has_asymmetric_triple
      s T (Nat.log 2 T) (by omega) hbounds hcard hpow
  have hpprime : p.Prime := (Finset.mem_filter.mp hp).2
  have hqprime : q.Prime := (Finset.mem_filter.mp hq).2
  have hrprime : r.Prime := (Finset.mem_filter.mp hr).2
  exact ⟨p, q, r, hpprime, hqprime, hrprime, hNp, hpq, hqr, hasym, hrpT⟩


end Erdos700PNT.PackingWork

/-! Flattened from Target.lean. -/


/-!
# Exact solved-side target for Erdős 700(ii)

The upstream conjecture wraps the mathematical assertion in an unspecified
answer placeholder.  A solution should prove the right-hand set infinite
directly; it must not use the open equivalence theorem.
-/

namespace Erdos700PNT

def target : Set ℕ :=
  {n : ℕ | ¬n.Prime ∧ 1 < n ∧ (Erdos700.f n) ^ 2 > n}

theorem target_infinite_of_unbounded
    (h : ∀ B : ℕ, ∃ n : ℕ, n ∈ target ∧ B < n) :
    target.Infinite := by
  exact Set.infinite_of_forall_exists_gt h

theorem exact_erdos_700_ii_target_of_unbounded
    (h : ∀ B : ℕ, ∃ n : ℕ,
      ¬n.Prime ∧ 1 < n ∧ (Erdos700.f n) ^ 2 > n ∧ B < n) :
    {n : ℕ | ¬n.Prime ∧ 1 < n ∧ (Erdos700.f n) ^ 2 > n}.Infinite := by
  apply target_infinite_of_unbounded
  intro B
  obtain ⟨n, hnprime, hn1, hnf, hBn⟩ := h B
  exact ⟨n, ⟨hnprime, hn1, hnf⟩, hBn⟩

end Erdos700PNT


/-! Flattened from Assembly.lean. -/


/-!
# Order-theoretic assembly for Erdős 700(ii)

This file isolates the `sInf` bookkeeping from the Lucas arithmetic. Once a
prime-triple proof supplies a uniform lower bound for every relevant gcd and
one witness attaining it, the exact value of `Erdos700.f` follows.
-/

namespace Erdos700PNT

lemma f_eq_of_gcd_lower_and_witness
    (n d witness : ℕ)
    (hw1 : 1 < witness)
    (hw2 : witness ≤ n / 2)
    (hwgcd : Nat.gcd n (n.choose witness) = d)
    (hlower : ∀ k, 1 < k → k ≤ n / 2 → d ≤ Nat.gcd n (n.choose k)) :
    Erdos700.f n = d := by
  apply Nat.le_antisymm
  · simpa [hwgcd] using Erdos700.f_le n witness hw1 hw2
  · have hne : (Erdos700.fSet n).Nonempty :=
      ⟨Nat.gcd n (n.choose witness), Erdos700.f_mem n witness hw1 hw2⟩
    obtain ⟨k, hk1, hk2, hkeq⟩ := Nat.sInf_mem hne
    rw [Erdos700.f_eq, hkeq]
    exact hlower k hk1 hk2

lemma f_square_gt_of_all_gcd_square_gt
    (n witness : ℕ)
    (hw1 : 1 < witness)
    (hw2 : witness ≤ n / 2)
    (hlower : ∀ k, 1 < k → k ≤ n / 2 →
      n < (Nat.gcd n (n.choose k)) ^ 2) :
    n < (Erdos700.f n) ^ 2 := by
  have hne : (Erdos700.fSet n).Nonempty :=
    ⟨Nat.gcd n (n.choose witness), Erdos700.f_mem n witness hw1 hw2⟩
  obtain ⟨k, hk1, hk2, hkeq⟩ := Nat.sInf_mem hne
  rw [Erdos700.f_eq, hkeq]
  exact hlower k hk1 hk2

lemma product_le_gcd_of_two_prime_pairs
    (p q r C : ℕ) (hC : 0 < C) (hp : p ≤ q) (hqr : q ≤ r)
    (hpq : p * q ∣ C ∨ p * r ∣ C ∨ q * r ∣ C) :
    p * q ≤ C := by
  rcases hpq with hpq | hpr | hqr'
  · exact Nat.le_of_dvd hC hpq
  · have hpr_le : p * r ≤ C := Nat.le_of_dvd hC hpr
    exact (Nat.mul_le_mul_left p hqr).trans hpr_le
  · have hqr_le : q * r ≤ C := Nat.le_of_dvd hC hqr'
    exact (Nat.mul_le_mul hp hqr).trans hqr_le

lemma square_gt_of_f_eq
    (n p q : ℕ) (hf : Erdos700.f n = p * q) (h : n < (p * q) ^ 2) :
    n < (Erdos700.f n) ^ 2 := by
  simpa [hf] using h

lemma gcd_square_of_pairwise_not_omitted
    (p q r a c C : ℕ)
    (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (hqeq : q = p + a) (hreq : r = q + c)
    (ha : 0 < a) (hac : a < c)
    (hlarge : 4 * (a + c) ^ 3 < p)
    (not_pq : ¬(¬p ∣ C ∧ ¬q ∣ C))
    (not_pr : ¬(¬p ∣ C ∧ ¬r ∣ C))
    (not_qr : ¬(¬q ∣ C ∧ ¬r ∣ C)) :
    p * q * r < (Nat.gcd (p * q * r) C) ^ 2 := by
  have hpq : p < q := by omega
  have hqr : q < r := by omega
  have hnpos : 0 < p * q * r :=
    Nat.mul_pos (Nat.mul_pos hp.pos hq.pos) hr.pos
  have hgpos : 0 < Nat.gcd (p * q * r) C :=
    Nat.gcd_pos_of_pos_left C hnpos
  have hgle : p * q ≤ Nat.gcd (p * q * r) C := by
    by_cases hpC : p ∣ C
    · by_cases hqC : q ∣ C
      · have hpqC : p * q ∣ C :=
          Nat.Coprime.mul_dvd_of_dvd_of_dvd
            ((Nat.coprime_primes hp hq).2 (by omega)) hpC hqC
        exact Nat.le_of_dvd hgpos (Nat.dvd_gcd ⟨r, rfl⟩ hpqC)
      · have hrC : r ∣ C := by
          by_contra hrC
          exact not_qr ⟨hqC, hrC⟩
        have hprC : p * r ∣ C :=
          Nat.Coprime.mul_dvd_of_dvd_of_dvd
            ((Nat.coprime_primes hp hr).2 (by omega)) hpC hrC
        have hprg : p * r ∣ Nat.gcd (p * q * r) C :=
          Nat.dvd_gcd ⟨q, by ring⟩ hprC
        exact (Nat.mul_le_mul_left p hqr.le).trans (Nat.le_of_dvd hgpos hprg)
    · have hqC : q ∣ C := by
        by_contra hqC
        exact not_pq ⟨hpC, hqC⟩
      have hrC : r ∣ C := by
        by_contra hrC
        exact not_pr ⟨hpC, hrC⟩
      have hqrC : q * r ∣ C :=
        Nat.Coprime.mul_dvd_of_dvd_of_dvd
          ((Nat.coprime_primes hq hr).2 (by omega)) hqC hrC
      have hqrg : q * r ∣ Nat.gcd (p * q * r) C :=
        Nat.dvd_gcd ⟨p, by ring⟩ hqrC
      exact (Nat.mul_le_mul hpq.le hqr.le).trans (Nat.le_of_dvd hgpos hqrg)
  have hbpos : 0 < a + c := by omega
  have hb_lt_p : a + c < p := by
    have hb_le_cube : a + c ≤ (a + c) ^ 3 := Nat.le_self_pow (by omega) _
    omega
  have hr_lt_p2 : r < p * 2 := by omega
  have hp2_le_pq : p * 2 ≤ p * q := Nat.mul_le_mul_left p hq.two_le
  have hr_lt_pq : r < p * q := hr_lt_p2.trans_le hp2_le_pq
  have hsmall : p * q * r < (p * q) ^ 2 := by
    rw [pow_two]
    exact (Nat.mul_lt_mul_left (Nat.mul_pos hp.pos hq.pos)).2 hr_lt_pq
  have hsquares : (p * q) ^ 2 ≤ (Nat.gcd (p * q * r) C) ^ 2 := by
    simpa [pow_two] using Nat.mul_le_mul hgle hgle
  exact hsmall.trans_le hsquares

lemma prime_triple_f_square_gt_of_pairwise_not_omitted
    (p q r a c : ℕ)
    (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (hqeq : q = p + a) (hreq : r = q + c)
    (ha : 0 < a) (hac : a < c)
    (hlarge : 4 * (a + c) ^ 3 < p)
    (homission : ∀ k, 1 < k → k ≤ (p * q * r) / 2 →
      ¬(¬p ∣ (p * q * r).choose k ∧ ¬q ∣ (p * q * r).choose k) ∧
      ¬(¬p ∣ (p * q * r).choose k ∧ ¬r ∣ (p * q * r).choose k) ∧
      ¬(¬q ∣ (p * q * r).choose k ∧ ¬r ∣ (p * q * r).choose k)) :
    p * q * r < (Erdos700.f (p * q * r)) ^ 2 := by
  have hr1 : 1 < r := hr.one_lt
  have hpq2 : 2 ≤ p * q := by
    have hp2 := hp.two_le
    have hq1 := hq.one_lt
    nlinarith
  have hrhalf : r ≤ (p * q * r) / 2 := by
    have htwor : 2 * r ≤ p * q * r := by
      calc
        2 * r ≤ (p * q) * r := Nat.mul_le_mul_right r hpq2
        _ = p * q * r := rfl
    omega
  apply f_square_gt_of_all_gcd_square_gt (p * q * r) r hr1 hrhalf
  intro k hk1 hk2
  obtain ⟨hpq, hpr, hqr⟩ := homission k hk1 hk2
  exact gcd_square_of_pairwise_not_omitted
    p q r a c ((p * q * r).choose k) hp hq hr hqeq hreq ha hac hlarge hpq hpr hqr

end Erdos700PNT


/-! Flattened from CoreHelpers.lean. -/


/-!
# Kernel-checked helper lemmas for Erdős 700(ii)

These lemmas expose the exact one-step Lucas consequences used by the
structural part of the proof. They deliberately avoid a custom base-digit
representation.
-/

namespace Erdos700PNT

lemma lucas_step_not_dvd (P n k : ℕ) (hP : P.Prime)
    (h : ¬P ∣ n.choose k) :
    k % P ≤ n % P ∧ ¬P ∣ (n / P).choose (k / P) := by
  letI := Fact.mk hP
  have hmod : n.choose k ≡
      (n % P).choose (k % P) * (n / P).choose (k / P) [MOD P] :=
    Choose.choose_modEq_choose_mod_mul_choose_div_nat
  have hprod : ¬P ∣
      (n % P).choose (k % P) * (n / P).choose (k / P) := by
    intro hd
    apply h
    exact (Nat.modEq_zero_iff_dvd).1
      (hmod.trans ((Nat.modEq_zero_iff_dvd).2 hd))
  constructor
  · by_contra hle
    have hlt : n % P < k % P := Nat.lt_of_not_ge hle
    apply hprod
    rw [Nat.choose_eq_zero_of_lt hlt, zero_mul]
    exact dvd_zero P
  · intro hd
    exact hprod (dvd_mul_of_dvd_right hd _)

lemma lucas_two_digits_le (P n k : ℕ) (hP : P.Prime)
    (h : ¬P ∣ n.choose k) :
    k % P ≤ n % P ∧ (k / P) % P ≤ (n / P) % P := by
  have h₁ := lucas_step_not_dvd P n k hP h
  have h₂ := lucas_step_not_dvd P (n / P) (k / P) hP h₁.2
  exact ⟨h₁.1, h₂.1⟩

lemma near_base_dvd_forces_residue
    (s d u v : ℕ) (hdu : d * u < s) (hv : v < s)
    (hdiv : s ∣ (s - d) * u + v) (hds : d ≤ s) :
    v = d * u := by
  obtain ⟨w, hw⟩ := hdiv
  have hsd : s - d + d = s := Nat.sub_add_cancel hds
  by_cases hu : u = 0
  · subst u
    simp only [mul_zero, zero_add] at hw hdu ⊢
    have hw0 : w = 0 := by nlinarith
    simpa [hw0] using hw
  have hu0 : 0 < u := Nat.pos_of_ne_zero hu
  have hwle : w ≤ u := by
    by_contra hn
    have huw : u < w := by omega
    have hmul : s * (u + 1) ≤ s * w :=
      Nat.mul_le_mul_left s (by omega)
    rw [← hw] at hmul
    nlinarith [Nat.sub_add_cancel hds]
  have huw : u ≤ w := by
    by_contra hn
    have hwu : w < u := by omega
    have hsw_le : s * w ≤ s * (u - 1) :=
      Nat.mul_le_mul_left s (by omega)
    have hbase_le : (s - d) * u ≤ s * w := by
      rw [← hw]
      exact Nat.le_add_right _ _
    have hgap : s * (u - 1) < (s - d) * u := by
      nlinarith [Nat.sub_add_cancel (show 1 ≤ u by omega),
        Nat.sub_add_cancel hds]
    omega
  have hwu : w = u := Nat.le_antisymm hwle huw
  subst w
  nlinarith [Nat.sub_add_cancel hds]

end Erdos700PNT


/-! Flattened from StructuralWork/PROmission.lean. -/


/-!
# The `p,r` simultaneous-omission contradiction

This is one of the three problem-specific Lucas digit arguments in the
prime-triple structural lemma for Erdős 700.
-/

namespace Erdos700PNT

set_option maxHeartbeats 1000000

private lemma normalized_two_digits (P lo hi : ℕ) (hP : 0 < P) (hlo : lo < P) :
    (lo + P * hi) % P = lo ∧ (lo + P * hi) / P = hi := by
  constructor
  · simpa [Nat.mod_eq_of_lt hlo] using Nat.add_mul_mod_self_left lo P hi
  · simpa [Nat.div_eq_of_lt hlo] using Nat.add_mul_div_left lo hi hP

private lemma pair_quotient_le_half
    (P Q R t : ℕ) (hP : 0 < P) (hQ : 0 < Q)
    (h : P * Q * t ≤ (P * Q * R) / 2) :
    t ≤ R / 2 := by
  have htwice : (P * Q * t) * 2 ≤ P * Q * R :=
    (Nat.le_div_iff_mul_le (by omega : 0 < 2)).1 h
  have hcancel : t * 2 ≤ R := by
    apply Nat.le_of_mul_le_mul_left (c := P * Q)
    · simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using htwice
    · exact Nat.mul_pos hP hQ
  exact (Nat.le_div_iff_mul_le (by omega : 0 < 2)).2 hcancel

private lemma below_base_mul_expansion
    (R d t : ℕ) (hdR : d ≤ R) (hdtR : d * t ≤ R) (ht : 1 ≤ t) :
    (R - d) * t = (R - d * t) + R * (t - 1) := by
  nlinarith [Nat.sub_add_cancel hdR, Nat.sub_add_cancel hdtR,
    Nat.sub_add_cancel ht]

private lemma pq_near_base_expansion
    (p a c : ℕ) (hcp : c ≤ p) :
    p * (p + a) = (a + c) * c + (p + a + c) * (p - c) := by
  nlinarith [Nat.sub_add_cancel hcp]

/-- Under the prime-triple gap hypotheses, `p` and `r` cannot both be absent
from the binomial coefficient in the defining half-range. -/
theorem not_p_and_r_omitted
    (p q r a c k : ℕ)
    (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (hqeq : q = p + a) (hreq : r = q + c)
    (ha : 0 < a) (hac : a < c)
    (hlarge : 4 * (a + c) ^ 3 < p)
    (hk1 : 1 < k) (hk2 : k ≤ (p * q * r) / 2) :
    ¬ (¬ p ∣ (p * q * r).choose k ∧ ¬ r ∣ (p * q * r).choose k) := by
  rintro ⟨hpC, hrC⟩
  have hpq : p < q := by omega
  have hqr : q < r := by omega
  have hpr : p ≠ r := by omega
  have hpk : p ∣ k :=
    Erdos700.prime_dvd_of_not_dvd_choose p (p * q * r) k hp
      ⟨q * r, by ring⟩ hpC
  have hrk : r ∣ k :=
    Erdos700.prime_dvd_of_not_dvd_choose r (p * q * r) k hr
      ⟨p * q, by ring⟩ hrC
  have hprk : p * r ∣ k :=
    ((Nat.coprime_primes hp hr).2 hpr).mul_dvd_of_dvd_of_dvd hpk hrk
  obtain ⟨t, hkt⟩ := hprk
  have ht : 0 < t := by
    by_contra ht0
    have : t = 0 := by omega
    subst t
    simp at hkt
    omega
  have hkt' : k = p * r * t := hkt
  have htq : t ≤ q / 2 := by
    apply pair_quotient_le_half p r q t hp.pos hr.pos
    simpa [hkt', Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hk2

  have hb : 0 < a + c := by omega
  have hb_le_cube : a + c ≤ (a + c) ^ 3 :=
    Nat.le_self_pow (by omega : 3 ≠ 0) (a + c)
  have hb_lt_p : a + c < p := by
    have hcubelt : (a + c) ^ 3 < 4 * (a + c) ^ 3 := by
      nlinarith [pow_pos hb 3]
    exact hb_le_cube.trans_lt (hcubelt.trans hlarge)
  have hc_lt_p : c < p := by omega
  have ha_lt_p : a < p := by omega
  have ht_lt_p : t < p := by
    rw [hqeq] at htq
    omega

  -- Lucas in base p compares `r*t` against `q*r`.
  have hpDivK : k / p = r * t := by
    rw [hkt']
    simpa [Nat.mul_assoc] using Nat.mul_div_cancel_left (r * t) hp.pos
  have hpDivN : (p * q * r) / p = q * r := by
    simpa [Nat.mul_assoc] using Nat.mul_div_cancel_left (q * r) hp.pos
  have hpDigits :
      (r * t) % p ≤ (q * r) % p ∧
      ((r * t) / p) % p ≤ ((q * r) / p) % p := by
    have hdiv :=
      (lucas_step_not_dvd p (p * q * r) k hp hpC).2
    simpa [hpDivK, hpDivN] using
      (lucas_two_digits_le p ((p * q * r) / p) (k / p) hp hdiv)

  let u := (a + c) * t / p
  let v := (a + c) * t % p
  have hvp : v < p := Nat.mod_lt _ hp.pos
  have hat_lt : (a + c) * t < (a + c) * p :=
    Nat.mul_lt_mul_of_pos_left ht_lt_p hb
  have hu_lt : u < a + c := by
    exact (Nat.div_lt_iff_lt_mul hp.pos).2 (by
      simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hat_lt)
  have ht_u_lt_p : t + u < p := by
    have hu_le : u ≤ a + c - 1 := by omega
    rw [hqeq] at htq
    have hsmall : a + 2 * (a + c) < p := by
      have : 3 * (a + c) < p := by
        have hb3 : 3 * (a + c) ≤ 4 * (a + c) ^ 3 := by
          nlinarith [hb_le_cube]
        exact hb3.trans_lt hlarge
      omega
    omega

  have hbt : (a + c) * t = p * u + v := by
    dsimp [u, v]
    exact (Nat.div_add_mod ((a + c) * t) p).symm
  have hrt : r * t = v + p * (t + u) := by
    rw [hreq, hqeq]
    nlinarith [hbt]

  have hab_lt_p : a * (a + c) < p := by
    have haa : a ≤ a + c := by omega
    have hprod : a * (a + c) ≤ (a + c) * (a + c) :=
      Nat.mul_le_mul_right (a + c) haa
    have hsquare : (a + c) ^ 2 ≤ (a + c) ^ 3 :=
      Nat.pow_le_pow_right hb (by omega)
    have hcubep : (a + c) ^ 3 < p :=
      lt_trans (by nlinarith [pow_pos hb 3]) hlarge
    have hprod' : a * (a + c) ≤ (a + c) ^ 2 := by
      simpa [pow_two] using hprod
    exact hprod'.trans_lt (hsquare.trans_lt hcubep)
  have habmid_lt_p : a + (a + c) < p := by
    have : 2 * (a + c) < p := by
      have h2 : 2 * (a + c) ≤ 4 * (a + c) ^ 3 := by
        nlinarith [hb_le_cube]
      exact h2.trans_lt hlarge
    omega
  have hqrExpansion :
      q * r = a * (a + c) + p * ((a + (a + c)) + p) := by
    rw [hqeq, hreq, hqeq]
    ring
  have hqrMod : (q * r) % p = a * (a + c) := by
    rw [hqrExpansion]
    exact (normalized_two_digits p (a * (a + c)) ((a + (a + c)) + p)
      hp.pos hab_lt_p).1
  have hqrDiv :
      (q * r) / p = (a + (a + c)) + p := by
    rw [hqrExpansion]
    exact (normalized_two_digits p (a * (a + c)) ((a + (a + c)) + p)
      hp.pos hab_lt_p).2
  have hqrSecond : ((q * r) / p) % p = a + (a + c) := by
    rw [hqrDiv]
    simpa [Nat.mod_eq_of_lt habmid_lt_p] using
      Nat.add_mod_right (a + (a + c)) p

  have hrtMod : (r * t) % p = v := by
    rw [hrt]
    exact (normalized_two_digits p v (t + u) hp.pos hvp).1
  have hrtDiv : (r * t) / p = t + u := by
    rw [hrt]
    exact (normalized_two_digits p v (t + u) hp.pos hvp).2
  have htu : t + u ≤ a + (a + c) := by
    have := hpDigits.2
    rw [hrtDiv, Nat.mod_eq_of_lt ht_u_lt_p, hqrSecond] at this
    exact this
  have ht_small : t ≤ a + (a + c) :=
    (Nat.le_add_right t u).trans htu
  have hbt_lt_p : (a + c) * t < p := by
    have hmul : (a + c) * t ≤ (a + c) * (a + (a + c)) :=
      Nat.mul_le_mul_left (a + c) ht_small
    have hbound : (a + c) * (a + (a + c)) < p := by
      have : (a + c) * (a + (a + c)) ≤ 2 * (a + c) ^ 2 := by
        nlinarith
      have : 2 * (a + c) ^ 2 < 4 * (a + c) ^ 3 := by
        nlinarith [hb]
      omega
    exact hmul.trans_lt hbound
  have hu0 : u = 0 := by
    dsimp [u]
    exact Nat.div_eq_of_lt hbt_lt_p
  have hvEq : v = (a + c) * t := by
    dsimp [v]
    exact Nat.mod_eq_of_lt hbt_lt_p
  have hvle : v ≤ a * (a + c) := by
    have := hpDigits.1
    rw [hrtMod, hqrMod] at this
    exact this
  have ht_le_a : t ≤ a := by
    rw [hvEq] at hvle
    apply Nat.le_of_mul_le_mul_left (c := a + c)
    · simpa [Nat.mul_comm] using hvle
    · exact hb

  -- Lucas in base r compares `p*t` against `p*q`.
  have hrDivK : k / r = p * t := by
    rw [hkt']
    simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using
      Nat.mul_div_cancel_left (p * t) hr.pos
  have hrDivN : (p * q * r) / r = p * q := by
    exact Nat.mul_div_cancel (p * q) hr.pos
  have hrLow :
      (p * t) % r ≤ (p * q) % r := by
    have h := (lucas_two_digits_le r (p * q * r) k hr hrC).2
    simpa [hrDivK, hrDivN] using h

  have hbt_lt_r : (a + c) * t < r := by
    rw [hreq, hqeq]
    have hle : (a + c) * t ≤ (a + c) * a :=
      Nat.mul_le_mul_left (a + c) ht_le_a
    have hle' : (a + c) * t ≤ a * (a + c) := by
      simpa [Nat.mul_comm] using hle
    exact hle'.trans_lt (hab_lt_p.trans (by omega))
  have hp_as_sub : p = r - (a + c) := by omega
  have hptExpansion :
      p * t = (r - (a + c) * t) + r * (t - 1) := by
    rw [hp_as_sub]
    exact below_base_mul_expansion r (a + c) t
      (by omega) hbt_lt_r.le (by omega)
  have hptMod : (p * t) % r = r - (a + c) * t := by
    rw [hptExpansion]
    exact (normalized_two_digits r (r - (a + c) * t) (t - 1) hr.pos
      (Nat.sub_lt (by omega) (Nat.mul_pos hb ht))).1

  have hbc_lt_r : (a + c) * c < r := by
    rw [hreq, hqeq]
    have hc_le : c ≤ a + c := by omega
    have hbc_sq : (a + c) * c ≤ (a + c) ^ 2 := by
      simpa [pow_two] using Nat.mul_le_mul_left (a + c) hc_le
    have hsq_cube : (a + c) ^ 2 ≤ (a + c) ^ 3 :=
      Nat.pow_le_pow_right hb (by omega)
    have hcube_four : (a + c) ^ 3 ≤ 4 * (a + c) ^ 3 := by
      have := Nat.mul_le_mul_right ((a + c) ^ 3) (by omega : 1 ≤ 4)
      simpa [Nat.mul_comm] using this
    have hsqp : (a + c) ^ 2 < p :=
      hsq_cube.trans_lt (hcube_four.trans_lt hlarge)
    exact hbc_sq.trans_lt (hsqp.trans (by omega))
  have hpqcExpansion :
      p * q = (a + c) * c + r * (p - c) := by
    rw [hqeq, hreq, hqeq]
    exact pq_near_base_expansion p a c hc_lt_p.le
  have hpqMod : (p * q) % r = (a + c) * c := by
    rw [hpqcExpansion]
    exact (normalized_two_digits r ((a + c) * c) (p - c) hr.pos hbc_lt_r).1

  rw [hptMod, hpqMod] at hrLow
  have hrUpper : r ≤ (a + c) * t + (a + c) * c := by
    omega
  have hsmallUpper :
      (a + c) * t + (a + c) * c ≤ (a + c) ^ 2 := by
    calc
      (a + c) * t + (a + c) * c = (a + c) * (t + c) := by ring
      _ ≤ (a + c) * (a + c) :=
        Nat.mul_le_mul_left (a + c) (Nat.add_le_add_right ht_le_a c)
      _ = (a + c) ^ 2 := by ring
  have hrLarge : (a + c) ^ 2 < r := by
    have hsq_cube : (a + c) ^ 2 ≤ (a + c) ^ 3 :=
      Nat.pow_le_pow_right hb (by omega)
    have hcube_four : (a + c) ^ 3 ≤ 4 * (a + c) ^ 3 := by
      have := Nat.mul_le_mul_right ((a + c) ^ 3) (by omega : 1 ≤ 4)
      simpa [Nat.mul_comm] using this
    exact hsq_cube.trans_lt (hcube_four.trans_lt (hlarge.trans (by omega)))
  omega


end Erdos700PNT

/-! Flattened from StructuralWork/PQOmission.lean. -/


/-! The `p,q` simultaneous-omission contradiction for Erdős 700. -/

namespace Erdos700PNT

set_option maxHeartbeats 1000000

private lemma norm2pq (P lo hi : ℕ) (hP : 0 < P) (hlo : lo < P) :
    (lo + P * hi) % P = lo ∧ (lo + P * hi) / P = hi := by
  constructor
  · simpa [Nat.mod_eq_of_lt hlo] using Nat.add_mul_mod_self_left lo P hi
  · simpa [Nat.div_eq_of_lt hlo] using Nat.add_mul_div_left lo hi hP

private lemma quotient_half_pq (P Q R t : ℕ) (hP : 0 < P) (hQ : 0 < Q)
    (h : P * Q * t ≤ (P * Q * R) / 2) : t ≤ R / 2 := by
  have h2 : (P * Q * t) * 2 ≤ P * Q * R :=
    (Nat.le_div_iff_mul_le (by omega : 0 < 2)).1 h
  have hc : t * 2 ≤ R := by
    apply Nat.le_of_mul_le_mul_left (c := P * Q)
    · simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using h2
    · exact Nat.mul_pos hP hQ
  exact (Nat.le_div_iff_mul_le (by omega : 0 < 2)).2 hc

private lemma below_mul_pq (R d t : ℕ) (hdR : d ≤ R) (hdtR : d * t ≤ R)
    (ht : 1 ≤ t) :
    (R - d) * t = (R - d * t) + R * (t - 1) := by
  nlinarith [Nat.sub_add_cancel hdR, Nat.sub_add_cancel hdtR,
    Nat.sub_add_cancel ht]

private lemma pr_q_expansion_pq (q a c : ℕ)
    (haq : a ≤ q) (hacq : a * c ≤ q) (hgap : a + 1 ≤ c) :
    (q - a) * (q + c) =
      (q - a * c) + q * ((c - a - 1) + q) := by
  have hqa : q - a + a = q := Nat.sub_add_cancel haq
  have hqac : q - a * c + a * c = q := Nat.sub_add_cancel hacq
  have hca : c - a + a = c := Nat.sub_add_cancel (by omega)
  have hca1 : c - a - 1 + 1 = c - a := Nat.sub_add_cancel (by omega)
  nlinarith

theorem not_p_and_q_omitted
    (p q r a c k : ℕ)
    (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (hqeq : q = p + a) (hreq : r = q + c)
    (ha : 0 < a) (hac : a < c)
    (hlarge : 4 * (a + c) ^ 3 < p)
    (hk1 : 1 < k) (hk2 : k ≤ (p * q * r) / 2) :
    ¬ (¬ p ∣ (p * q * r).choose k ∧ ¬ q ∣ (p * q * r).choose k) := by
  rintro ⟨hpC, hqC⟩
  have hpq : p < q := by omega
  have hqr : q < r := by omega
  have hpqne : p ≠ q := by omega
  have hpk : p ∣ k :=
    Erdos700.prime_dvd_of_not_dvd_choose p (p * q * r) k hp
      ⟨q * r, by ring⟩ hpC
  have hqk : q ∣ k :=
    Erdos700.prime_dvd_of_not_dvd_choose q (p * q * r) k hq
      ⟨p * r, by ring⟩ hqC
  have hpqk : p * q ∣ k :=
    ((Nat.coprime_primes hp hq).2 hpqne).mul_dvd_of_dvd_of_dvd hpk hqk
  obtain ⟨t, hkt⟩ := hpqk
  have ht : 0 < t := by
    by_contra h
    have : t = 0 := by omega
    subst t
    simp at hkt
    omega
  have hkt' : k = p * q * t := hkt
  have htr : t ≤ r / 2 := by
    apply quotient_half_pq p q r t hp.pos hq.pos
    simpa [hkt'] using hk2

  have hb : 0 < a + c := by omega
  have hb_le_cube : a + c ≤ (a + c) ^ 3 :=
    Nat.le_self_pow (by omega : 3 ≠ 0) _
  have hcube4 : (a + c) ^ 3 ≤ 4 * (a + c) ^ 3 := by
    have := Nat.mul_le_mul_right ((a + c) ^ 3) (by omega : 1 ≤ 4)
    simpa [Nat.mul_comm] using this
  have hb_lt_p : a + c < p :=
    hb_le_cube.trans_lt (hcube4.trans_lt hlarge)
  have ht_lt_p : t < p := by
    rw [hreq, hqeq] at htr
    omega

  have hpDivK : k / p = q * t := by
    rw [hkt']
    simpa [Nat.mul_assoc] using Nat.mul_div_cancel_left (q * t) hp.pos
  have hpDivN : (p * q * r) / p = q * r := by
    simpa [Nat.mul_assoc] using Nat.mul_div_cancel_left (q * r) hp.pos
  have hpStep := (lucas_step_not_dvd p (p * q * r) k hp hpC).2
  have hpDigits :
      (q * t) % p ≤ (q * r) % p ∧
      ((q * t) / p) % p ≤ ((q * r) / p) % p := by
    simpa [hpDivK, hpDivN] using
      lucas_two_digits_le p ((p * q * r) / p) (k / p) hp hpStep

  let u := a * t / p
  let v := a * t % p
  have hvp : v < p := Nat.mod_lt _ hp.pos
  have hat_ap : a * t < a * p :=
    Nat.mul_lt_mul_of_pos_left ht_lt_p ha
  have hu_lt_a : u < a :=
    (Nat.div_lt_iff_lt_mul hp.pos).2 (by
      simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hat_ap)
  have ht_u_lt_p : t + u < p := by
    have hu : u ≤ a - 1 := by omega
    rw [hreq, hqeq] at htr
    have h3b : 3 * (a + c) < p :=
      (by
        have hle : 3 * (a + c) ≤ 4 * (a + c) ^ 3 := by
          have h1 : 3 * (a + c) ≤ 3 * (a + c) ^ 3 :=
            Nat.mul_le_mul_left 3 hb_le_cube
          have h2 : 3 * (a + c) ^ 3 ≤ 4 * (a + c) ^ 3 := by
            have := Nat.mul_le_mul_right ((a + c) ^ 3) (by omega : 3 ≤ 4)
            simpa [Nat.mul_comm] using this
          exact h1.trans h2
        exact hle.trans_lt hlarge)
    omega
  have hat : a * t = p * u + v := by
    dsimp [u, v]
    exact (Nat.div_add_mod (a * t) p).symm
  have hqt : q * t = v + p * (t + u) := by
    rw [hqeq]
    nlinarith [hat]

  have hab_sq : a * (a + c) ≤ (a + c) ^ 2 := by
    have hm := Nat.mul_le_mul (by omega : a ≤ a + c) (by omega : a + c ≤ a + c)
    simpa [pow_two] using hm
  have hsq_cube : (a + c) ^ 2 ≤ (a + c) ^ 3 :=
    Nat.pow_le_pow_right hb (by omega)
  have hab_lt_p : a * (a + c) < p :=
    hab_sq.trans_lt (hsq_cube.trans_lt (hcube4.trans_lt hlarge))
  have hmid_lt_p : a + (a + c) < p := by
    have h2b : 2 * (a + c) ≤ 4 * (a + c) ^ 3 := by
      have h1 : 2 * (a + c) ≤ 2 * (a + c) ^ 3 :=
        Nat.mul_le_mul_left 2 hb_le_cube
      have h2 : 2 * (a + c) ^ 3 ≤ 4 * (a + c) ^ 3 := by
        have := Nat.mul_le_mul_right ((a + c) ^ 3) (by omega : 2 ≤ 4)
        simpa [Nat.mul_comm] using this
      exact h1.trans h2
    omega
  have hqrNorm :
      q * r = a * (a + c) + p * ((a + (a + c)) + p) := by
    rw [hqeq, hreq, hqeq]
    ring
  have hqrMod : (q * r) % p = a * (a + c) := by
    rw [hqrNorm]
    exact (norm2pq p (a * (a + c)) ((a + (a + c)) + p)
      hp.pos hab_lt_p).1
  have hqrDiv : (q * r) / p = (a + (a + c)) + p := by
    rw [hqrNorm]
    exact (norm2pq p (a * (a + c)) ((a + (a + c)) + p)
      hp.pos hab_lt_p).2
  have hqrSecond : ((q * r) / p) % p = a + (a + c) := by
    rw [hqrDiv]
    simpa [Nat.mod_eq_of_lt hmid_lt_p] using Nat.add_mod_right (a + (a + c)) p
  have hqtMod : (q * t) % p = v := by
    rw [hqt]
    exact (norm2pq p v (t + u) hp.pos hvp).1
  have hqtDiv : (q * t) / p = t + u := by
    rw [hqt]
    exact (norm2pq p v (t + u) hp.pos hvp).2
  have htu : t + u ≤ a + (a + c) := by
    have h := hpDigits.2
    rw [hqtDiv, Nat.mod_eq_of_lt ht_u_lt_p, hqrSecond] at h
    exact h
  have ht_mid : t ≤ a + (a + c) := (Nat.le_add_right t u).trans htu
  have hat_lt_p : a * t < p := by
    have hle : a * t ≤ a * (a + (a + c)) :=
      Nat.mul_le_mul_left a ht_mid
    have hbound : a * (a + (a + c)) ≤ 2 * (a + c) ^ 2 := by
      have h1 : a ≤ a + c := by omega
      have h2 : a + (a + c) ≤ 2 * (a + c) := by omega
      have hm := Nat.mul_le_mul h1 h2
      nlinarith
    have h2sq : 2 * (a + c) ^ 2 ≤ 4 * (a + c) ^ 3 := by
      have hpw := Nat.mul_le_mul_left 2 hsq_cube
      have hd : 2 * (a + c) ^ 3 ≤ 4 * (a + c) ^ 3 := by
        have := Nat.mul_le_mul_right ((a + c) ^ 3) (by omega : 2 ≤ 4)
        simpa [Nat.mul_comm] using this
      exact hpw.trans hd
    exact (hle.trans hbound).trans_lt (h2sq.trans_lt hlarge)
  have hvEq : v = a * t := by
    dsimp [v]
    exact Nat.mod_eq_of_lt hat_lt_p
  have hvle : v ≤ a * (a + c) := by
    have h := hpDigits.1
    rw [hqtMod, hqrMod] at h
    exact h
  have ht_le_b : t ≤ a + c := by
    rw [hvEq] at hvle
    exact Nat.le_of_mul_le_mul_left hvle ha

  have hqDivK : k / q = p * t := by
    rw [hkt']
    simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using
      Nat.mul_div_cancel_left (p * t) hq.pos
  have hqDivN : (p * q * r) / q = p * r := by
    simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using
      Nat.mul_div_cancel_left (p * r) hq.pos
  have hqStep := (lucas_step_not_dvd q (p * q * r) k hq hqC).2
  have hqDigits :
      (p * t) % q ≤ (p * r) % q ∧
      ((p * t) / q) % q ≤ ((p * r) / q) % q := by
    simpa [hqDivK, hqDivN] using
      lucas_two_digits_le q ((p * q * r) / q) (k / q) hq hqStep

  have hat_lt_q : a * t < q := hat_lt_p.trans hpq
  have hp_as_sub : p = q - a := by omega
  have hptNorm : p * t = (q - a * t) + q * (t - 1) := by
    rw [hp_as_sub]
    exact below_mul_pq q a t (by omega) hat_lt_q.le (by omega)
  have hptMod : (p * t) % q = q - a * t := by
    rw [hptNorm]
    exact (norm2pq q (q - a * t) (t - 1) hq.pos
      (Nat.sub_lt (by omega) (Nat.mul_pos ha ht))).1
  have hptDiv : (p * t) / q = t - 1 := by
    rw [hptNorm]
    exact (norm2pq q (q - a * t) (t - 1) hq.pos
      (Nat.sub_lt (by omega) (Nat.mul_pos ha ht))).2

  have hac_lt_q : a * c < q := by
    have hle : a * c ≤ a * (a + c) :=
      Nat.mul_le_mul_left a (by omega)
    exact (hle.trans_lt hab_lt_p).trans hpq
  have hgap : a + 1 ≤ c := by omega
  have hprNorm :
      p * r = (q - a * c) + q * ((c - a - 1) + q) := by
    rw [hp_as_sub, hreq]
    exact pr_q_expansion_pq q a c (by omega) hac_lt_q.le hgap
  have hlo : q - a * c < q :=
    Nat.sub_lt hq.pos (Nat.mul_pos ha (by omega))
  have hprMod : (p * r) % q = q - a * c := by
    rw [hprNorm]
    exact (norm2pq q (q - a * c) ((c - a - 1) + q) hq.pos hlo).1
  have hprDiv : (p * r) / q = (c - a - 1) + q := by
    rw [hprNorm]
    exact (norm2pq q (q - a * c) ((c - a - 1) + q) hq.pos hlo).2
  have hprSecond : ((p * r) / q) % q = c - a - 1 := by
    rw [hprDiv]
    have hm : c - a - 1 < q := by omega
    simpa [Nat.mod_eq_of_lt hm] using Nat.add_mod_right (c - a - 1) q
  have hlow := hqDigits.1
  rw [hptMod, hprMod] at hlow
  have hhigh := hqDigits.2
  rw [hptDiv, Nat.mod_eq_of_lt (by omega : t - 1 < q), hprSecond] at hhigh
  have hct : c ≤ t := by
    have hatac : a * c ≤ a * t := by omega
    exact Nat.le_of_mul_le_mul_left hatac ha
  omega


end Erdos700PNT

/-! Flattened from StructuralWork/QROmission.lean. -/


/-! The `q,r` simultaneous-omission contradiction for Erdős 700. -/

namespace Erdos700PNT

set_option maxHeartbeats 1000000

private lemma norm2 (P lo hi : ℕ) (hP : 0 < P) (hlo : lo < P) :
    (lo + P * hi) % P = lo ∧ (lo + P * hi) / P = hi := by
  constructor
  · simpa [Nat.mod_eq_of_lt hlo] using Nat.add_mul_mod_self_left lo P hi
  · simpa [Nat.div_eq_of_lt hlo] using Nat.add_mul_div_left lo hi hP

private lemma quotient_half (P Q R t : ℕ) (hP : 0 < P) (hQ : 0 < Q)
    (h : P * Q * t ≤ (P * Q * R) / 2) : t ≤ R / 2 := by
  have h2 : (P * Q * t) * 2 ≤ P * Q * R :=
    (Nat.le_div_iff_mul_le (by omega : 0 < 2)).1 h
  have hc : t * 2 ≤ R := by
    apply Nat.le_of_mul_le_mul_left (c := P * Q)
    · simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using h2
    · exact Nat.mul_pos hP hQ
  exact (Nat.le_div_iff_mul_le (by omega : 0 < 2)).2 hc

private lemma below_mul (R d t : ℕ) (hdR : d ≤ R) (hdtR : d * t ≤ R)
    (ht : 1 ≤ t) :
    (R - d) * t = (R - d * t) + R * (t - 1) := by
  nlinarith [Nat.sub_add_cancel hdR, Nat.sub_add_cancel hdtR,
    Nat.sub_add_cancel ht]

private lemma pr_q_expansion (q a c : ℕ)
    (haq : a ≤ q) (hacq : a * c ≤ q) (hgap : a + 1 ≤ c) :
    (q - a) * (q + c) =
      (q - a * c) + q * ((c - a - 1) + q) := by
  have hqa : q - a + a = q := Nat.sub_add_cancel haq
  have hqac : q - a * c + a * c = q := Nat.sub_add_cancel hacq
  have hca : c - a + a = c := Nat.sub_add_cancel (by omega)
  have hca1 : c - a - 1 + 1 = c - a :=
    Nat.sub_add_cancel (by omega)
  nlinarith

private lemma pq_r_expansion (p a c : ℕ) (hcp : c ≤ p) :
    p * (p + a) = (a + c) * c + (p + a + c) * (p - c) := by
  nlinarith [Nat.sub_add_cancel hcp]

theorem not_q_and_r_omitted
    (p q r a c k : ℕ)
    (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (hqeq : q = p + a) (hreq : r = q + c)
    (ha : 0 < a) (hac : a < c)
    (hlarge : 4 * (a + c) ^ 3 < p)
    (hk1 : 1 < k) (hk2 : k ≤ (p * q * r) / 2) :
    ¬ (¬ q ∣ (p * q * r).choose k ∧ ¬ r ∣ (p * q * r).choose k) := by
  rintro ⟨hqC, hrC⟩
  have hpq : p < q := by omega
  have hqr : q < r := by omega
  have hqrne : q ≠ r := by omega
  have hqk : q ∣ k :=
    Erdos700.prime_dvd_of_not_dvd_choose q (p * q * r) k hq
      ⟨p * r, by ring⟩ hqC
  have hrk : r ∣ k :=
    Erdos700.prime_dvd_of_not_dvd_choose r (p * q * r) k hr
      ⟨p * q, by ring⟩ hrC
  have hqrk : q * r ∣ k :=
    ((Nat.coprime_primes hq hr).2 hqrne).mul_dvd_of_dvd_of_dvd hqk hrk
  obtain ⟨t, hkt⟩ := hqrk
  have ht : 0 < t := by
    by_contra h
    have : t = 0 := by omega
    subst t
    simp at hkt
    omega
  have hkt' : k = q * r * t := hkt
  have htp : t ≤ p / 2 := by
    apply quotient_half q r p t hq.pos hr.pos
    simpa [hkt', Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hk2

  have hb : 0 < a + c := by omega
  have hb_le_cube : a + c ≤ (a + c) ^ 3 :=
    Nat.le_self_pow (by omega : 3 ≠ 0) _
  have hb_lt_p : a + c < p := by
    have hcube4 : (a + c) ^ 3 ≤ 4 * (a + c) ^ 3 := by
      have := Nat.mul_le_mul_right ((a + c) ^ 3) (by omega : 1 ≤ 4)
      simpa [Nat.mul_comm] using this
    exact hb_le_cube.trans_lt (hcube4.trans_lt hlarge)
  have ht_lt_q : t < q := by omega
  have hcq : c < q := by omega
  have haq : a < q := by omega

  have hqDivK : k / q = r * t := by
    rw [hkt']
    simpa [Nat.mul_assoc] using Nat.mul_div_cancel_left (r * t) hq.pos
  have hqDivN : (p * q * r) / q = p * r := by
    simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using
      Nat.mul_div_cancel_left (p * r) hq.pos
  have hqStep := (lucas_step_not_dvd q (p * q * r) k hq hqC).2
  have hqDigits :
      (r * t) % q ≤ (p * r) % q ∧
      ((r * t) / q) % q ≤ ((p * r) / q) % q := by
    simpa [hqDivK, hqDivN] using
      lucas_two_digits_le q ((p * q * r) / q) (k / q) hq hqStep

  let u := c * t / q
  let v := c * t % q
  have hvq : v < q := Nat.mod_lt _ hq.pos
  have hct_lt_cq : c * t < c * q :=
    Nat.mul_lt_mul_of_pos_left ht_lt_q (by omega)
  have hu_lt_c : u < c :=
    (Nat.div_lt_iff_lt_mul hq.pos).2 (by
      simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hct_lt_cq)
  have ht_u_lt_q : t + u < q := by
    have hu : u ≤ c - 1 := by omega
    have : p / 2 + c < q := by rw [hqeq]; omega
    omega
  have hct : c * t = q * u + v := by
    dsimp [u, v]
    exact (Nat.div_add_mod (c * t) q).symm
  have hrt : r * t = v + q * (t + u) := by
    rw [hreq]
    nlinarith [hct]

  have hac_le_sq : a * c ≤ (a + c) ^ 2 := by
    have ha' : a ≤ a + c := by omega
    have hc' : c ≤ a + c := by omega
    simpa [pow_two] using Nat.mul_le_mul ha' hc'
  have hsq_cube : (a + c) ^ 2 ≤ (a + c) ^ 3 :=
    Nat.pow_le_pow_right hb (by omega)
  have hcube4 : (a + c) ^ 3 ≤ 4 * (a + c) ^ 3 := by
    have := Nat.mul_le_mul_right ((a + c) ^ 3) (by omega : 1 ≤ 4)
    simpa [Nat.mul_comm] using this
  have hac_lt_q : a * c < q :=
    hac_le_sq.trans_lt
      ((hsq_cube.trans_lt (hcube4.trans_lt hlarge)).trans hpq)
  have hgap : a + 1 ≤ c := by omega
  have hp_as_sub : p = q - a := by omega
  have hprNorm :
      p * r = (q - a * c) + q * ((c - a - 1) + q) := by
    rw [hp_as_sub, hreq]
    exact pr_q_expansion q a c haq.le hac_lt_q.le hgap
  have hloq : q - a * c < q := Nat.sub_lt hq.pos (Nat.mul_pos ha (by omega))
  have hprMod : (p * r) % q = q - a * c := by
    rw [hprNorm]
    exact (norm2 q (q - a * c) ((c - a - 1) + q) hq.pos hloq).1
  have hprDiv : (p * r) / q = (c - a - 1) + q := by
    rw [hprNorm]
    exact (norm2 q (q - a * c) ((c - a - 1) + q) hq.pos hloq).2
  have hprSecond : ((p * r) / q) % q = c - a - 1 := by
    rw [hprDiv]
    have hmid : c - a - 1 < q := by omega
    simpa [Nat.mod_eq_of_lt hmid] using Nat.add_mod_right (c - a - 1) q
  have hrtMod : (r * t) % q = v := by
    rw [hrt]
    exact (norm2 q v (t + u) hq.pos hvq).1
  have hrtDiv : (r * t) / q = t + u := by
    rw [hrt]
    exact (norm2 q v (t + u) hq.pos hvq).2
  have htu : t + u ≤ c - a - 1 := by
    have h := hqDigits.2
    rw [hrtDiv, Nat.mod_eq_of_lt ht_u_lt_q, hprSecond] at h
    exact h
  have htgap : t ≤ c - a - 1 := (Nat.le_add_right t u).trans htu
  have ht_le_c : t ≤ c := by omega

  have hrDivK : k / r = q * t := by
    rw [hkt']
    simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using
      Nat.mul_div_cancel_left (q * t) hr.pos
  have hrDivN : (p * q * r) / r = p * q := Nat.mul_div_cancel (p * q) hr.pos
  have hrLow : (q * t) % r ≤ (p * q) % r := by
    have hstep := (lucas_step_not_dvd r (p * q * r) k hr hrC).2
    have h := (lucas_two_digits_le r ((p * q * r) / r) (k / r) hr hstep).1
    simpa [hrDivK, hrDivN] using h

  have hsq_r : (a + c) ^ 2 < r :=
    (hsq_cube.trans_lt (hcube4.trans_lt hlarge)).trans (by omega)
  have hct_lt_r : c * t < r := by
    have hle : c * t ≤ c * c := Nat.mul_le_mul_left c ht_le_c
    have hcc : c * c ≤ (a + c) ^ 2 := by
      have := Nat.mul_le_mul (by omega : c ≤ a + c) (by omega : c ≤ a + c)
      simpa [pow_two] using this
    exact hle.trans_lt (hcc.trans_lt hsq_r)
  have hq_as_sub : q = r - c := by omega
  have hqtNorm : q * t = (r - c * t) + r * (t - 1) := by
    rw [hq_as_sub]
    exact below_mul r c t (by omega) hct_lt_r.le (by omega)
  have hqtMod : (q * t) % r = r - c * t := by
    rw [hqtNorm]
    exact (norm2 r (r - c * t) (t - 1) hr.pos
      (Nat.sub_lt (by omega) (Nat.mul_pos (by omega) ht))).1

  have hcp : c < p := by omega
  have hbc_sq : (a + c) * c ≤ (a + c) ^ 2 := by
    simpa [pow_two] using Nat.mul_le_mul_left (a + c) (by omega : c ≤ a + c)
  have hbc_lt_r : (a + c) * c < r :=
    hbc_sq.trans_lt hsq_r
  have hpqNorm : p * q = (a + c) * c + r * (p - c) := by
    rw [hqeq, hreq, hqeq]
    exact pq_r_expansion p a c hcp.le
  have hpqMod : (p * q) % r = (a + c) * c := by
    rw [hpqNorm]
    exact (norm2 r ((a + c) * c) (p - c) hr.pos hbc_lt_r).1
  rw [hqtMod, hpqMod] at hrLow
  have hrUpper : r ≤ c * t + (a + c) * c := by omega
  have hupper : c * t + (a + c) * c ≤ 2 * (a + c) ^ 2 := by
    have hctsq : c * t ≤ (a + c) ^ 2 := by
      have hm := Nat.mul_le_mul (by omega : c ≤ a + c) (by omega : t ≤ a + c)
      simpa [pow_two] using hm
    have := Nat.add_le_add hctsq hbc_sq
    simpa [two_mul] using this
  have h2sq_lt_r : 2 * (a + c) ^ 2 < r := by
    have h2cube : 2 * (a + c) ^ 2 ≤ 4 * (a + c) ^ 3 := by
      have hpow : (a + c) ^ 2 ≤ (a + c) ^ 3 :=
        Nat.pow_le_pow_right hb (by omega)
      have htwice := Nat.mul_le_mul_left 2 hpow
      have hdouble : 2 * (a + c) ^ 3 ≤ 4 * (a + c) ^ 3 := by
        have := Nat.mul_le_mul_right ((a + c) ^ 3) (by omega : 2 ≤ 4)
        simpa [Nat.mul_comm] using this
      exact htwice.trans hdouble
    exact h2cube.trans_lt (hlarge.trans (by omega))
  omega


end Erdos700PNT

/-! Flattened from StructuralWork/Combined.lean. -/


/-!
# Complete structural theorem for Erdős 700

The three independently checked Lucas digit arguments are assembled into the
uniform omission theorem and then into the exact `f(n)^2 > n` conclusion.
-/

namespace Erdos700PNT

theorem prime_triple_pairwise_not_omitted
    (p q r a c : ℕ)
    (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (hqeq : q = p + a) (hreq : r = q + c)
    (ha : 0 < a) (hac : a < c)
    (hlarge : 4 * (a + c) ^ 3 < p) :
    ∀ k, 1 < k → k ≤ (p * q * r) / 2 →
      ¬(¬p ∣ (p * q * r).choose k ∧ ¬q ∣ (p * q * r).choose k) ∧
      ¬(¬p ∣ (p * q * r).choose k ∧ ¬r ∣ (p * q * r).choose k) ∧
      ¬(¬q ∣ (p * q * r).choose k ∧ ¬r ∣ (p * q * r).choose k) := by
  intro k hk1 hk2
  exact ⟨
    not_p_and_q_omitted p q r a c k hp hq hr hqeq hreq ha hac hlarge hk1 hk2,
    not_p_and_r_omitted p q r a c k hp hq hr hqeq hreq ha hac hlarge hk1 hk2,
    not_q_and_r_omitted p q r a c k hp hq hr hqeq hreq ha hac hlarge hk1 hk2⟩

theorem prime_triple_f_square_gt
    (p q r a c : ℕ)
    (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (hqeq : q = p + a) (hreq : r = q + c)
    (ha : 0 < a) (hac : a < c)
    (hlarge : 4 * (a + c) ^ 3 < p) :
    p * q * r < (Erdos700.f (p * q * r)) ^ 2 := by
  exact prime_triple_f_square_gt_of_pairwise_not_omitted
    p q r a c hp hq hr hqeq hreq ha hac hlarge
    (prime_triple_pairwise_not_omitted p q r a c hp hq hr
      hqeq hreq ha hac hlarge)


end Erdos700PNT

/-! Flattened from Reduction.lean. -/


/-!
# Exact reduction of Erdős 700(ii) to unbounded structured prime triples

This theorem packages the final quantifiers.  The remaining proof-producing
modules only need to supply unbounded triples and the three simultaneous
Lucas-omission contradictions.
-/

namespace Erdos700PNT

theorem exact_erdos_700_ii_of_unbounded_prime_triples
    (htriples : ∀ B : ℕ, ∃ p q r a c : ℕ,
      p.Prime ∧ q.Prime ∧ r.Prime ∧
      q = p + a ∧ r = q + c ∧
      0 < a ∧ a < c ∧
      4 * (a + c) ^ 3 < p ∧
      B < p * q * r ∧
      ∀ k, 1 < k → k ≤ (p * q * r) / 2 →
        ¬(¬p ∣ (p * q * r).choose k ∧ ¬q ∣ (p * q * r).choose k) ∧
        ¬(¬p ∣ (p * q * r).choose k ∧ ¬r ∣ (p * q * r).choose k) ∧
        ¬(¬q ∣ (p * q * r).choose k ∧ ¬r ∣ (p * q * r).choose k)) :
    {n : ℕ | ¬n.Prime ∧ 1 < n ∧ (Erdos700.f n) ^ 2 > n}.Infinite := by
  apply exact_erdos_700_ii_target_of_unbounded
  intro B
  obtain ⟨p, q, r, a, c, hp, hq, hr, hqeq, hreq, ha, hac, hlarge,
    hB, homission⟩ := htriples B
  have hnprime : ¬(p * q * r).Prime := by
    intro hn
    have hpdiv : p ∣ p * q * r := ⟨q * r, by ring⟩
    have heq : p = p * q * r :=
      (Nat.prime_dvd_prime_iff_eq hp hn).1 hpdiv
    have hq2 := hq.two_le
    have hr2 := hr.two_le
    have heq' : p * 1 = p * (q * r) := by
      simpa [Nat.mul_assoc] using heq
    have hqr1 : 1 = q * r := Nat.mul_left_cancel hp.pos heq'
    have hfour : 4 ≤ q * r := by
      simpa using Nat.mul_le_mul hq2 hr2
    omega
  have hn1 : 1 < p * q * r := by
    have hnpos : 0 < p * q * r :=
      Nat.mul_pos (Nat.mul_pos hp.pos hq.pos) hr.pos
    have hpdiv : p ∣ p * q * r := ⟨q * r, by ring⟩
    exact hp.one_lt.trans_le (Nat.le_of_dvd hnpos hpdiv)
  have hsquare :=
    prime_triple_f_square_gt_of_pairwise_not_omitted
      p q r a c hp hq hr hqeq hreq ha hac hlarge homission
  exact ⟨p * q * r, hnprime, hn1, hsquare, hB⟩

end Erdos700PNT


/-! Flattened from Solution.lean. -/


/-!
# Complete formal solution of Erdős 700(ii)

The PNT packing theorem supplies unbounded asymmetric prime triples.  Their
gap geometry implies the cubic largeness hypothesis, the structural Lucas
theorem supplies the binomial-coefficient divisibility property, and the
order-theoretic reduction proves the exact solved-side infinitude statement.
-/

open Filter

namespace Erdos700PNT

theorem unbounded_structured_prime_triples :
    ∀ B : ℕ, ∃ p q r a c : ℕ,
      p.Prime ∧ q.Prime ∧ r.Prime ∧
      q = p + a ∧ r = q + c ∧
      0 < a ∧ a < c ∧
      4 * (a + c) ^ 3 < p ∧
      B < p * q * r := by
  intro B
  obtain ⟨T₀, hT₀⟩ :=
    (eventually_atTop.1 PackingWork.eventually_exists_asymmetric_prime_triple)
  let T := max (B + 1) (max T₀ 1)
  have hT₀T : T₀ ≤ T := by simp [T]
  obtain ⟨p, q, r, hp, hq, hr, hNp, hpq, hqr, hasym, hspan⟩ :=
    hT₀ T hT₀T
  let a := q - p
  let c := r - q
  have hTpos : 0 < T := by simp [T]
  have hBT : B < T := by
    dsimp [T]
    omega
  have hqa : q = p + a := by
    dsimp [a]
    omega
  have hrc : r = q + c := by
    dsimp [c]
    omega
  have ha : 0 < a := by
    dsimp [a]
    omega
  have hac : a < c := by
    dsimp [a, c]
    exact hasym
  have hgap : a + c = r - p := by
    dsimp [a, c]
    omega
  have hbT : a + c < T := by
    rw [hgap]
    exact hspan
  have hpow : (a + c) ^ 3 < T ^ 3 := by
    gcongr
  have hTcube : 0 < T ^ 3 := pow_pos hTpos 3
  have hlarge : 4 * (a + c) ^ 3 < p := by
    have h4 : 4 * (a + c) ^ 3 < 8 * T ^ 3 := by
      nlinarith
    exact h4.trans_le hNp
  have hT_le_cube : T ≤ T ^ 3 := Nat.le_self_pow (by omega) T
  have hBp : B < p := by
    have hT_le_N : T ≤ 8 * T ^ 3 := by nlinarith
    exact hBT.trans_le (hT_le_N.trans hNp)
  have hnpos : 0 < p * q * r :=
    Nat.mul_pos (Nat.mul_pos hp.pos hq.pos) hr.pos
  have hpdiv : p ∣ p * q * r := ⟨q * r, by ring⟩
  have hBprod : B < p * q * r :=
    hBp.trans_le (Nat.le_of_dvd hnpos hpdiv)
  exact ⟨p, q, r, a, c, hp, hq, hr, hqa, hrc, ha, hac, hlarge, hBprod⟩

/-- The solved mathematical side of Formal Conjectures' Erdős 700(ii). -/
theorem erdos_700_ii :
    {n : ℕ | ¬n.Prime ∧ 1 < n ∧ (Erdos700.f n) ^ 2 > n}.Infinite := by
  apply exact_erdos_700_ii_of_unbounded_prime_triples
  intro B
  obtain ⟨p, q, r, a, c, hp, hq, hr, hqeq, hreq, ha, hac, hlarge, hB⟩ :=
    unbounded_structured_prime_triples B
  exact ⟨p, q, r, a, c, hp, hq, hr, hqeq, hreq, ha, hac, hlarge, hB,
    prime_triple_pairwise_not_omitted p q r a c hp hq hr
      hqeq hreq ha hac hlarge⟩


end Erdos700PNT


namespace Erdos700CanonicalPort

noncomputable def f (n : ℕ) : ℕ :=
  sInf {m | ∃ k, 1 < k ∧ k ≤ n / 2 ∧ m = Nat.gcd n (n.choose k)}

abbrev statement : Prop :=
  {n : ℕ | ¬ n.Prime ∧ 1 < n ∧ n < (f n) ^ 2}.Infinite

theorem proof : statement := by
  simpa only [statement, f, Erdos700.f] using Erdos700PNT.erdos_700_ii

end Erdos700CanonicalPort

namespace Submissions.Erdos700LargeBinomialGcd.Published

theorem proof : Erdos700CanonicalPort.statement := Erdos700CanonicalPort.proof

#print axioms proof

end Submissions.Erdos700LargeBinomialGcd.Published
