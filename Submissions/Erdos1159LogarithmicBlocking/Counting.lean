import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Data.Finset.Powerset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Algebra.Order.Ring.Pow

namespace Submissions.Erdos1159LogarithmicBlocking.Counting

open Finset
open scoped BigOperators

namespace PlaneMoments

variable {Point Line : Type*} [Fintype Line]
  (I : Point → Line → Prop) [DecidableRel I] (q : ℕ)

theorem first_moment
    (degree : ∀ p : Point, (univ.filter fun l => I p l).card = q + 1)
    (S : Finset Point) :
    (∑ l : Line, (S.filter fun p => I p l).card) = S.card * (q + 1) := by
  classical
  calc
    _ = ∑ p ∈ S, (univ.filter fun l => I p l).card := by
      simpa only [bipartiteAbove, bipartiteBelow] using
        (sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow I
          (s := S) (t := univ)).symm
    _ = S.card * (q + 1) := by simp [degree]

theorem common_lines [DecidableEq Point]
    (degree : ∀ p : Point, (univ.filter fun l => I p l).card = q + 1)
    (join : ∀ p r : Point, p ≠ r → ∃ l : Line, I p l ∧ I r l)
    (unique : ∀ p r : Point, ∀ l m : Line, p ≠ r →
      I p l → I r l → I p m → I r m → l = m)
    (p r : Point) :
    (univ.filter fun l => I p l ∧ I r l).card = if p = r then q + 1 else 1 := by
  classical
  by_cases h : p = r
  · subst r
    simpa using degree p
  · rw [if_neg h]
    obtain ⟨l, hlp, hlr⟩ := join p r h
    apply card_eq_one.mpr
    refine ⟨l, ?_⟩
    ext m
    simp only [mem_filter, mem_univ, true_and, mem_singleton]
    constructor
    · rintro ⟨hmp, hmr⟩
      exact (unique p r l m h hlp hlr hmp hmr).symm
    · intro hm
      subst m
      exact ⟨hlp, hlr⟩

theorem second_moment
    (degree : ∀ p : Point, (univ.filter fun l => I p l).card = q + 1)
    (join : ∀ p r : Point, p ≠ r → ∃ l : Line, I p l ∧ I r l)
    (unique : ∀ p r : Point, ∀ l m : Line, p ≠ r →
      I p l → I r l → I p m → I r m → l = m)
    (S : Finset Point) :
    (∑ l : Line, (S.filter fun p => I p l).card ^ 2) =
      S.card * (S.card + q) := by
  classical
  have expand (l : Line) :
      (S.filter fun p => I p l).card ^ 2 =
        ∑ p ∈ S, ∑ r ∈ S, if I p l ∧ I r l then 1 else 0 := by
    simp_rw [card_eq_sum_ones, sum_filter, pow_two, sum_mul, mul_sum]
    apply sum_congr rfl
    intro p hp
    apply sum_congr rfl
    intro r hr
    by_cases hpl : I p l <;> by_cases hrl : I r l <;> simp [hpl, hrl]
  calc
    _ = ∑ l : Line, ∑ p ∈ S, ∑ r ∈ S, if I p l ∧ I r l then 1 else 0 := by
      exact sum_congr rfl fun l _ => expand l
    _ = ∑ p ∈ S, ∑ r ∈ S, ∑ l : Line, if I p l ∧ I r l then 1 else 0 := by
      rw [sum_comm]
      apply sum_congr rfl
      intro p hp
      rw [sum_comm]
    _ = ∑ p ∈ S, ∑ r ∈ S, (univ.filter fun l => I p l ∧ I r l).card := by
      simp_rw [card_eq_sum_ones, sum_filter]
    _ = ∑ p ∈ S, ∑ r ∈ S, if p = r then q + 1 else 1 := by
      simp_rw [common_lines I q degree join unique]
    _ = ∑ p ∈ S, (S.card + q) := by
      apply sum_congr rfl
      intro p hp
      have split (r : Point) :
          (if p = r then q + 1 else 1) = (if p = r then q else 0) + 1 := by
        by_cases h : p = r <;> simp [h]
      simp_rw [split, sum_add_distrib]
      simp [hp, Nat.add_comm]
    _ = S.card * (S.card + q) := by simp

theorem line_count [Fintype Point] [Nonempty Line]
    (lineDegree : ∀ l : Line, (univ.filter fun p => I p l).card = q + 1)
    (pointDegree : ∀ p : Point, (univ.filter fun l => I p l).card = q + 1)
    (join : ∀ p r : Point, p ≠ r → ∃ l : Line, I p l ∧ I r l)
    (unique : ∀ p r : Point, ∀ l m : Line, p ≠ r →
      I p l → I r l → I p m → I r m → l = m) :
    Fintype.card Line = q * q + q + 1 := by
  classical
  have hfirst := first_moment I q pointDegree (univ : Finset Point)
  simp only [lineDegree, sum_const, card_univ, nsmul_eq_mul] at hfirst
  have hcard : Fintype.card Line = Fintype.card Point :=
    Nat.eq_of_mul_eq_mul_right (Nat.succ_pos q) hfirst
  have hsecond := second_moment I q pointDegree join unique (univ : Finset Point)
  simp only [lineDegree, sum_const, card_univ, nsmul_eq_mul] at hsecond
  rw [← hcard] at hsecond
  have heq : (q + 1) ^ 2 = Fintype.card Line + q :=
    Nat.eq_of_mul_eq_mul_left (Fintype.card_pos) hsecond
  nlinarith only [heq]

end PlaneMoments

open Finset

namespace FiniteCriterion

/-- A finite union bound over missed lines and chosen `k`-point subsets of lines.
The usual conditions `1 ≤ k ≤ r` and `t ≤ card Point` are unnecessary here. -/
theorem exists_blocking_set
    {Point Line : Type*} [Fintype Point] [Fintype Line]
    (I : Point → Line → Prop) [DecidableRel I] (r t k : ℕ)
    (rowSize : ∀ l : Line, (univ.filter fun p => I p l).card = r)
    (hkt : k ≤ t)
    (hbound : Fintype.card Line *
      ((Fintype.card Point - r).choose t +
        r.choose k * (Fintype.card Point - k).choose (t - k)) <
      (Fintype.card Point).choose t) :
    ∃ S : Finset Point, S.card = t ∧ ∀ l : Line,
      1 ≤ (S.filter fun p => I p l).card ∧
        (S.filter fun p => I p l).card < k := by
  classical
  let row (l : Line) : Finset Point := univ.filter fun p => I p l
  let candidates : Finset (Finset Point) := (univ : Finset Point).powersetCard t
  let miss (l : Line) : Finset (Finset Point) :=
    ((univ : Finset Point) \ row l).powersetCard t
  let over (l : Line) : Finset (Finset Point) :=
    ((row l).powersetCard k).biUnion fun K => candidates.filter (K ⊆ ·)
  let bad : Finset (Finset Point) := univ.biUnion fun l : Line => miss l ∪ over l
  have hmiss (l : Line) : (miss l).card = (Fintype.card Point - r).choose t := by
    dsimp [miss]
    rw [card_powersetCard, card_sdiff_of_subset (subset_univ _), card_univ]
    rw [show (row l).card = r from rowSize l]
  have hover (l : Line) : (over l).card ≤
      r.choose k * (Fintype.card Point - k).choose (t - k) := by
    calc
      (over l).card ≤ ((row l).powersetCard k).card *
          (Fintype.card Point - k).choose (t - k) := by
        apply card_biUnion_le_card_mul
        intro K hK
        have hsize := (mem_powersetCard.mp hK).2
        have hKt : K.card ≤ t := by simpa only [hsize] using hkt
        have hcount := card_filter_powersetCard_subset K
          (univ : Finset Point) t (subset_univ _) hKt
        simpa only [candidates, card_univ, hsize] using hcount.le
      _ = r.choose k * (Fintype.card Point - k).choose (t - k) := by
        rw [card_powersetCard, show (row l).card = r from rowSize l]
  have hbad : bad.card ≤ Fintype.card Line *
      ((Fintype.card Point - r).choose t +
        r.choose k * (Fintype.card Point - k).choose (t - k)) := by
    change (univ.biUnion fun l : Line => miss l ∪ over l).card ≤ _
    rw [← card_univ (α := Line)]
    apply card_biUnion_le_card_mul
    intro l _
    exact (card_union_le _ _).trans (Nat.add_le_add (hmiss l).le (hover l))
  have hsmall : bad.card < candidates.card := by
    exact lt_of_le_of_lt hbad (by simpa only [candidates, card_powersetCard, card_univ] using hbound)
  obtain ⟨S, hS, hgood⟩ := exists_mem_notMem_of_card_lt_card hsmall
  have hsize : S.card = t := (mem_powersetCard.mp hS).2
  refine ⟨S, hsize, ?_⟩
  intro l
  have avoid : S ∉ miss l ∪ over l := fun h =>
    hgood (mem_biUnion.mpr ⟨l, mem_univ l, h⟩)
  constructor
  · apply Nat.one_le_iff_ne_zero.mpr
    intro hzero
    have hempty := card_eq_zero.mp hzero
    apply avoid
    apply mem_union_left
    apply mem_powersetCard.mpr
    refine ⟨?_, hsize⟩
    intro p hp
    apply mem_sdiff.mpr
    refine ⟨mem_univ p, ?_⟩
    intro hrow
    have hi : I p l := (mem_filter.mp hrow).2
    have hm : p ∈ S.filter fun p => I p l := mem_filter.mpr ⟨hp, hi⟩
    rw [hempty] at hm
    simpa using hm
  · apply Nat.lt_of_not_ge
    intro hlarge
    obtain ⟨K, hKS, hKsize⟩ := exists_subset_card_eq hlarge
    have hrow : K ⊆ row l := by
      intro p hp
      exact mem_filter.mpr ⟨mem_univ p, (mem_filter.mp (hKS hp)).2⟩
    have hsubset : K ⊆ S := hKS.trans (filter_subset _ S)
    apply avoid
    apply mem_union_right
    apply mem_biUnion.mpr
    exact ⟨K, mem_powersetCard.mpr ⟨hrow, hKsize⟩, mem_filter.mpr ⟨hS, hsubset⟩⟩

end FiniteCriterion

namespace BinomialRatio

/-- Sampling without replacement gives no larger containment ratio than powers. -/
theorem choose_mul_pow_le {a b : ℕ} (hab : a ≤ b) (k : ℕ) :
    a.choose k * b ^ k ≤ b.choose k * a ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    by_cases hka : k + 1 ≤ a
    · have hka' : k ≤ a := Nat.le_trans (Nat.le_succ k) hka
      have hkb' : k ≤ b := hka'.trans hab
      have hfactor : (a - k) * b ≤ (b - k) * a := by
        have ha := Nat.sub_add_cancel hka'
        have hb := Nat.sub_add_cancel hkb'
        nlinarith [Nat.mul_le_mul_left k hab]
      apply Nat.le_of_mul_le_mul_right ?_ (Nat.succ_pos k)
      calc
        a.choose (k + 1) * b ^ (k + 1) * (k + 1) =
            (a.choose (k + 1) * (k + 1)) * (b ^ k * b) := by
          rw [pow_succ]
          ring
        _ = (a.choose k * b ^ k) * ((a - k) * b) := by
          rw [Nat.choose_succ_right_eq]
          ring
        _ ≤ (b.choose k * a ^ k) * ((b - k) * a) := Nat.mul_le_mul ih hfactor
        _ = (b.choose (k + 1) * (k + 1)) * (a ^ k * a) := by
          rw [Nat.choose_succ_right_eq]
          ring
        _ = b.choose (k + 1) * a ^ (k + 1) * (k + 1) := by
          rw [pow_succ]
          ring
    · rw [Nat.choose_eq_zero_of_lt (Nat.lt_of_not_ge hka), zero_mul]
      exact Nat.zero_le _

/-- A fixed `k`-subset occurs in at most the `(t/v)^k` proportion of all `t`-subsets,
expressed without division. -/
theorem containing_mul_pow_le {v t k : ℕ} (hkt : k ≤ t) (htv : t ≤ v) :
    (v - k).choose (t - k) * v ^ k ≤ v.choose t * t ^ k := by
  have h := Nat.mul_le_mul_left (v.choose t) (choose_mul_pow_le htv k)
  apply Nat.le_of_mul_le_mul_left ?_ (Nat.choose_pos (hkt.trans htv))
  calc
    v.choose k * ((v - k).choose (t - k) * v ^ k) =
        (v.choose t * t.choose k) * v ^ k := by
      rw [Nat.choose_mul hkt]
      ring
    _ ≤ v.choose t * (v.choose k * t ^ k) := by
      simpa only [Nat.mul_assoc] using h
    _ = v.choose k * (v.choose t * t ^ k) := by ring

/-- A denominator-free power condition sufficient for the finite blocking-set criterion. -/
theorem power_condition_implies_criterion {v r b t k : ℕ}
    (hkt : k ≤ t) (htv : t ≤ v)
    (hpower : b * ((v - r) ^ t * v ^ k + r.choose k * t ^ k * v ^ t) <
      v ^ (t + k)) :
    b * ((v - r).choose t + r.choose k * (v - k).choose (t - k)) <
      v.choose t := by
  have hmiss := Nat.mul_le_mul_right (v ^ k)
    (choose_mul_pow_le (Nat.sub_le v r) t)
  have hover := Nat.mul_le_mul_left (r.choose k * v ^ t)
    (containing_mul_pow_le hkt htv)
  have hsum : ((v - r).choose t + r.choose k * (v - k).choose (t - k)) *
      v ^ (t + k) ≤
      v.choose t * ((v - r) ^ t * v ^ k + r.choose k * t ^ k * v ^ t) := by
    rw [pow_add]
    nlinarith only [hmiss, hover]
  have hscaled := Nat.mul_le_mul_left b hsum
  have hstrict := Nat.mul_lt_mul_of_pos_left hpower (Nat.choose_pos htv)
  have hfinal :
      (b * ((v - r).choose t + r.choose k * (v - k).choose (t - k))) *
        v ^ (t + k) < v.choose t * v ^ (t + k) := by
    nlinarith only [hscaled, hstrict]
  exact Nat.lt_of_mul_lt_mul_right hfinal

end BinomialRatio

namespace ElementaryBounds

lemma factorial_double (a : ℕ) (h : a ^ a ≤ 4 ^ a * a.factorial) :
    (2 * a) ^ (2 * a) ≤ 4 ^ (2 * a) * (2 * a).factorial := by
  have hf : a.factorial * a ^ a ≤ (2 * a).factorial := by
    simpa [two_mul] using
      (Nat.factorial_mul_pow_sub_le_factorial (n := a) (m := 2 * a) (by omega))
  calc
    (2 * a) ^ (2 * a) = 4 ^ a * (a ^ a * a ^ a) := by
      rw [mul_pow, pow_mul, show (2 : ℕ) ^ 2 = 4 by rfl, two_mul, pow_add]
    _ ≤ 4 ^ a * (4 ^ a * a.factorial * a ^ a) :=
      Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ h)
    _ = 4 ^ (2 * a) * (a.factorial * a ^ a) := by
      rw [two_mul, pow_add]
      ring
    _ ≤ 4 ^ (2 * a) * (2 * a).factorial := Nat.mul_le_mul_left _ hf

/-- A deliberately coarse factorial estimate needing no real analysis. -/
lemma pow_two_factorial (d : ℕ) :
    (2 ^ d) ^ (2 ^ d) ≤ 4 ^ (2 ^ d) * (2 ^ d).factorial := by
  induction d with
  | zero => norm_num
  | succ d ih => simpa [pow_succ, mul_comm] using factorial_double (2 ^ d) ih

lemma missed_block (v r : ℕ) (hr : 0 < r) (hrv : r ≤ v)
    (hsquare : v - r ≤ r * r) :
    2 * (v - r) ^ r ≤ v ^ r := by
  have hp : (v - r) ^ r = (v - r) ^ (r - 1) * (v - r) := by
    rw [← pow_succ, Nat.sub_add_cancel hr]
  have h := pow_add_mul_le_add_pow (a := v - r) (b := r)
    (Nat.zero_le _) (Nat.zero_le _) r
  rw [Nat.sub_add_cancel hrv] at h
  have hmul := Nat.mul_le_mul_left ((v - r) ^ (r - 1)) hsquare
  nlinarith

lemma overflow_bound (v r t k : ℕ) (hk : 0 < k)
    (hfactorial : k ^ k ≤ 4 ^ k * k.factorial)
    (hsmall : 8 * r * t ≤ v * k) :
    2 ^ k * r.choose k * t ^ k ≤ v ^ k := by
  have hc : k.factorial * r.choose k ≤ r ^ k := by
    rw [← Nat.descFactorial_eq_factorial_mul_choose]
    exact Nat.descFactorial_le_pow r k
  apply Nat.le_of_mul_le_mul_right (c := k ^ k) ?_ (Nat.pow_pos hk)
  calc
    (2 ^ k * r.choose k * t ^ k) * k ^ k ≤
        (2 ^ k * r.choose k * t ^ k) * (4 ^ k * k.factorial) :=
      Nat.mul_le_mul_left _ hfactorial
    _ = (8 * t) ^ k * (k.factorial * r.choose k) := by
      simp only [mul_pow, show (8 : ℕ) = 2 * 4 by rfl]
      ring
    _ ≤ (8 * t) ^ k * r ^ k := Nat.mul_le_mul_left _ hc
    _ = (8 * r * t) ^ k := by rw [← mul_pow]; congr 1 <;> ring
    _ ≤ (v * k) ^ k := Nat.pow_le_pow_left hsmall _
    _ = v ^ k * k ^ k := mul_pow _ _ _

end ElementaryBounds

namespace PowerCriterion

/-- The two tail bounds make the sufficient power expression strictly smaller
than its denominator. -/
theorem combine_tails {v r b t k m : ℕ} (hv : 0 < v) (hmk : m ≤ k)
    (hbudget : 2 * b < 2 ^ m)
    (hmiss : 2 ^ m * (v - r) ^ t ≤ v ^ t)
    (hover : 2 ^ k * r.choose k * t ^ k ≤ v ^ k) :
    b * ((v - r) ^ t * v ^ k + r.choose k * t ^ k * v ^ t) <
      v ^ (t + k) := by
  have hpow : 2 ^ m ≤ 2 ^ k := Nat.pow_le_pow_right (by decide) hmk
  have hover' : 2 ^ m * r.choose k * t ^ k ≤ v ^ k :=
    (Nat.mul_le_mul_right (t ^ k) (Nat.mul_le_mul_right (r.choose k) hpow)).trans hover
  have hm := Nat.mul_le_mul_right (v ^ k) hmiss
  have ho := Nat.mul_le_mul_right (v ^ t) hover'
  have hsum :
      2 ^ m * ((v - r) ^ t * v ^ k + r.choose k * t ^ k * v ^ t) ≤
        2 * v ^ (t + k) := by
    rw [pow_add]
    nlinarith only [hm, ho]
  by_contra hnot
  have hbad := Nat.le_of_not_gt hnot
  have hb := Nat.mul_le_mul_left (2 ^ m) hbad
  have hs := Nat.mul_le_mul_left b hsum
  have hcancel : 2 ^ m * v ^ (t + k) ≤ (2 * b) * v ^ (t + k) := by
    nlinarith only [hb, hs]
  exact (Nat.not_le_of_gt hbudget)
    (Nat.le_of_mul_le_mul_right hcancel (Nat.pow_pos hv))

/-- Exact side conditions for the logarithmic construction in its nontrivial branch.
The arithmetic is valid for every natural `q`; geometry will assume `q ≥ 2`. -/
theorem dyadic_parameters (q : ℕ) :
    let v := q * q + q + 1
    let r := q + 1
    let m := (2 * v).log2 + 1
    let k := 2 ^ ((16 * m).log2 + 1)
    k < r → m ≤ k ∧ k ≤ r * m ∧ r * m ≤ v ∧
      8 * r * (r * m) ≤ v * k ∧ k ≤ 32 * m ∧ 2 * v < 2 ^ m := by
  dsimp only
  generalize hv : q * q + q + 1 = v
  generalize hr : q + 1 = r
  generalize hm : (2 * v).log2 + 1 = m
  generalize hk : 2 ^ ((16 * m).log2 + 1) = k
  intro hbranch
  have hmpos : 0 < m := by
    rw [← hm]
    exact Nat.succ_pos _
  have hlarge : 16 * m < k := by
    rw [← hk]
    exact Nat.lt_log2_self
  have hsmall : k ≤ 32 * m := by
    have h := Nat.log2_self_le (n := 16 * m)
      (Nat.ne_of_gt (Nat.mul_pos (by decide) hmpos))
    rw [← hk, pow_succ]
    nlinarith only [h]
  have hbudget : 2 * v < 2 ^ m := by
    rw [← hm]
    exact Nat.lt_log2_self
  have hm1 : 1 ≤ m := hmpos
  have hm_r : m < r := by nlinarith only [hlarge, hbranch, hm1]
  have hkt : k ≤ r * m := by
    have h := Nat.mul_le_mul_left r hm1
    nlinarith only [h, hbranch]
  have htv : r * m ≤ v := by
    have h := Nat.mul_le_mul_left r (Nat.succ_le_of_lt hm_r)
    nlinarith only [h, hv, hr]
  have hrv : r * r ≤ 2 * v := by
    rw [← hv, ← hr]
    nlinarith
  have hover : 8 * r * (r * m) ≤ v * k := by
    have h₁ := Nat.mul_le_mul_right (8 * m) hrv
    have h₂ := Nat.mul_le_mul_left v (Nat.le_of_lt hlarge)
    nlinarith only [h₁, h₂]
  exact ⟨by nlinarith only [hlarge], hkt, htv, hover, hsmall, hbudget⟩

end PowerCriterion

-- This file is appended after the checked helper namespaces in LogarithmicProof.lean.


theorem finite_log_bound
    (Point Line : Type) [Fintype Point] [Fintype Line]
    (I : Point → Line → Prop) [DecidableRel I] (q : ℕ)
    (hP : Fintype.card Point = q * q + q + 1)
    (hL : Fintype.card Line = q * q + q + 1)
    (degree : ∀ l : Line, (Finset.univ.filter fun p => I p l).card = q + 1) :
    ∃ S : Finset Point, ∀ l : Line,
      1 ≤ (S.filter fun p => I p l).card ∧
      (S.filter fun p => I p l).card ≤ 32 * ((2 * (q * q + q + 1)).log2 + 1) := by
  classical
  let v := q * q + q + 1
  let r := q + 1
  let m := (2 * v).log2 + 1
  let k := 2 ^ ((16 * m).log2 + 1)
  have hm : 0 < m := Nat.succ_pos _
  have hk : 0 < k := Nat.pow_pos (by decide)
  have hk_upper : k ≤ 32 * m := by
    have h := Nat.log2_self_le (n := 16 * m)
      (Nat.ne_of_gt (Nat.mul_pos (by decide) hm))
    dsimp [k]
    rw [pow_succ]
    nlinarith only [h]
  by_cases hsmall : r ≤ k
  · refine ⟨Finset.univ, fun l => ?_⟩
    rw [degree l]
    exact ⟨Nat.succ_le_succ (Nat.zero_le q), hsmall.trans hk_upper⟩
  have hbranch : k < r := Nat.lt_of_not_ge hsmall
  obtain ⟨hmk, hkt, htv, hoverSize, _, hbudget⟩ := PowerCriterion.dyadic_parameters q hbranch
  have hv : 0 < v := Nat.succ_pos _
  have hrv : r ≤ v := by dsimp [r, v]; omega
  have hr : 0 < r := Nat.succ_pos _
  have hsquare : v - r ≤ r * r := by
    have hsub := Nat.sub_add_cancel hrv
    dsimp [v, r] at *
    nlinarith only [hsub]
  have hmiss : 2 ^ m * (v - r) ^ (r * m) ≤ v ^ (r * m) := by
    have h := Nat.pow_le_pow_left (ElementaryBounds.missed_block v r hr hrv hsquare) m
    simpa only [mul_pow, ← pow_mul] using h
  have hfactorial : k ^ k ≤ 4 ^ k * k.factorial :=
    ElementaryBounds.pow_two_factorial _
  have hover := ElementaryBounds.overflow_bound v r (r * m) k hk hfactorial hoverSize
  have hpower := PowerCriterion.combine_tails hv hmk hbudget hmiss hover
  have hbound := BinomialRatio.power_condition_implies_criterion hkt htv hpower
  have hbound' : Fintype.card Line *
      ((Fintype.card Point - r).choose (r * m) +
        r.choose k * (Fintype.card Point - k).choose (r * m - k)) <
      (Fintype.card Point).choose (r * m) := by
    simpa only [hP, hL] using hbound
  obtain ⟨S, _, hS⟩ := FiniteCriterion.exists_blocking_set I r (r * m) k degree hkt hbound'
  exact ⟨S, fun l => ⟨(hS l).1, (Nat.le_of_lt (hS l).2).trans hk_upper⟩⟩

theorem proof
    (Point Line : Type) [Fintype Point] [Fintype Line]
    (I : Point → Line → Prop) [DecidableRel I] (q : ℕ)
    (_hq : 2 ≤ q)
    (lineDegree : ∀ l : Line, (Finset.univ.filter fun p => I p l).card = q + 1)
    (pointDegree : ∀ p : Point, (Finset.univ.filter fun l => I p l).card = q + 1)
    (join : ∀ p r : Point, p ≠ r → ∃ l : Line, I p l ∧ I r l)
    (unique : ∀ p r : Point, ∀ l m : Line, p ≠ r →
      I p l → I r l → I p m → I r m → l = m)
    (_meet : ∀ l m : Line, l ≠ m → ∃ p : Point, I p l ∧ I p m)
    (_uniqueMeet : ∀ l m : Line, ∀ p r : Point, l ≠ m →
      I p l → I p m → I r l → I r m → p = r) :
    ∃ S : Finset Point, ∀ l : Line,
      1 ≤ (S.filter fun p => I p l).card ∧
      (S.filter fun p => I p l).card ≤ 32 * ((2 * (q * q + q + 1)).log2 + 1) := by
  classical
  cases isEmpty_or_nonempty Line with
  | inl h =>
    letI := h
    exact ⟨∅, fun l => isEmptyElim l⟩
  | inr h =>
    letI := h
    have hL := PlaneMoments.line_count I q lineDegree pointDegree join unique
    have hfirst := PlaneMoments.first_moment I q pointDegree (Finset.univ : Finset Point)
    simp only [lineDegree, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hfirst
    have hcard := Nat.eq_of_mul_eq_mul_right (Nat.succ_pos q) hfirst
    exact finite_log_bound Point Line I q (hcard.symm.trans hL) hL lineDegree



end Submissions.Erdos1159LogarithmicBlocking.Counting
