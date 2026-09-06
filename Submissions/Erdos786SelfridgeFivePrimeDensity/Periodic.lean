import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Count
import Mathlib.Data.Nat.Periodic
import Mathlib.Data.Set.Card
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic

/-
A Selfridge-type construction for the distinct-factor form of Erdős 786(i):
`A = {n : Σ_{p ∈ S} v_p(n) = 1}` for a finite set `S` of primes. The weight
`w = Σ_{p∈S} v_p` is completely additive, so a product of `k` distinct elements
of `A` has weight `k`, which gives `IsMulCardSet A`. The density of `A` is
`∏_{p∈S}(1-1/p) · Σ_{p∈S} 1/p`; here `S = {3,5,7,11,13}` and the density is
`1622144/5010005 ≈ 0.3238`. The set is split by which prime of `S` carries the
weight; each piece is periodic with a period below 200000 and its residue count
is checked by kernel evaluation, in blocks of 15015 to keep memory small.
-/

set_option Elab.async false

namespace Submissions.Erdos786SelfridgeFivePrimeDensity.Periodic

open Finset Filter
open scoped Topology

noncomputable abbrev partialDensity (A : Set ℕ) (n : ℕ) : ℝ :=
  ((((A ∩ Set.univ) ∩ Set.Iio n).ncard : ℕ) : ℝ) /
    ((((Set.univ : Set ℕ) ∩ Set.Iio n).ncard : ℕ) : ℝ)

def HasDensity (A : Set ℕ) (δ : ℝ) : Prop :=
  Tendsto (partialDensity A) atTop (𝓝 δ)

def IsMulCardSet (A : Set ℕ) : Prop :=
  ∀ a b : Finset ℕ, (a : Set ℕ) ⊆ A → (b : Set ℕ) ⊆ A →
    a.prod id = b.prod id → a.card = b.card

/-! ### Generic facts: additive weights give `IsMulCardSet`, periodic sets have a density -/

section Weight

variable (S : Finset ℕ)

/-- Number of prime factors of `n` lying in `S`, counted with multiplicity. -/
def w (n : ℕ) : ℕ := ∑ p ∈ S, n.factorization p

lemma w_zero : w S 0 = 0 := by simp [w]

lemma w_prod (U : Finset ℕ) (hU : ∀ u ∈ U, u ≠ 0) :
    w S (U.prod id) = ∑ u ∈ U, w S u := by
  unfold w
  rw [show U.prod id = ∏ x ∈ U, x from rfl, Nat.factorization_prod hU]
  simp only [Finsupp.finsetSum_apply]
  exact Finset.sum_comm

theorem isMulCardSet_level : IsMulCardSet {n | w S n = 1} := by
  intro a b ha hb hab
  have hne : ∀ (U : Finset ℕ), (U : Set ℕ) ⊆ {n | w S n = 1} → ∀ u ∈ U, u ≠ 0 := by
    intro U hU u hu h0
    have : w S u = 1 := hU hu
    rw [h0, w_zero] at this
    omega
  have hwa : w S (a.prod id) = a.card := by
    rw [w_prod S a (hne a ha)]
    rw [Finset.card_eq_sum_ones]
    exact Finset.sum_congr rfl (fun u hu => ha hu)
  have hwb : w S (b.prod id) = b.card := by
    rw [w_prod S b (hne b hb)]
    rw [Finset.card_eq_sum_ones]
    exact Finset.sum_congr rfl (fun u hu => hb hu)
  rw [← hwa, ← hwb, hab]

end Weight

section Periodic

variable (Q : ℕ → Prop) [DecidablePred Q] (M : ℕ)

lemma count_shift_eq (hQ : Function.Periodic Q M) (m : ℕ) :
    Nat.count (fun k => Q (M + k)) m = Nat.count Q m := by
  rw [Nat.count_eq_card_filter_range, Nat.count_eq_card_filter_range]
  congr 1
  apply Finset.filter_congr
  intro k _
  rw [add_comm, hQ k]

lemma count_shift (hQ : Function.Periodic Q M) (q r : ℕ) :
    Nat.count Q (M * q + r) = q * Nat.count Q M + Nat.count Q r := by
  induction q with
  | zero => simp
  | succ q ih =>
    have h1 : M * (q + 1) + r = M + (M * q + r) := by ring
    rw [h1, Nat.count_add, count_shift_eq Q M hQ, ih]
    ring

lemma partialDensity_eq (n : ℕ) :
    partialDensity {k | Q k} n = (Nat.count Q n : ℝ) / n := by
  have hnum : ({k | Q k} ∩ Set.univ) ∩ Set.Iio n = ((Finset.range n).filter Q : Set ℕ) := by
    ext k
    simp [and_comm]
  have hden : (Set.univ : Set ℕ) ∩ Set.Iio n = (Finset.range n : Set ℕ) := by
    ext k
    simp
  simp only [partialDensity, hnum, hden, Set.ncard_coe_finset, Finset.card_range,
    Nat.count_eq_card_filter_range]

theorem hasDensity_periodic (hM : 0 < M) (hQ : Function.Periodic Q M) :
    HasDensity {k | Q k} ((Nat.count Q M : ℝ) / M) := by
  set c : ℕ := Nat.count Q M with hc
  have key : ∀ n : ℕ, 0 < n →
      (c : ℝ) / M - c / n ≤ partialDensity {k | Q k} n ∧
      partialDensity {k | Q k} n ≤ (c : ℝ) / M + c / n := by
    intro n hn
    rw [partialDensity_eq]
    have hdiv : n = M * (n / M) + n % M := (Nat.div_add_mod n M).symm
    have hcount : Nat.count Q n = (n / M) * c + Nat.count Q (n % M) := by
      conv_lhs => rw [hdiv]
      exact count_shift Q M hQ _ _
    have hrem : Nat.count Q (n % M) ≤ c :=
      Nat.count_monotone Q (Nat.mod_lt n hM).le
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
    have hMpos : (0 : ℝ) < M := by exact_mod_cast hM
    -- real-number form of `n = M * (n / M) + n % M` with `n % M < M`
    have hq : (M : ℝ) * ((n / M : ℕ) : ℝ) ≤ n := by
      have : M * (n / M) ≤ n := Nat.mul_div_le n M
      exact_mod_cast this
    have hq' : (n : ℝ) < M * ((n / M : ℕ) : ℝ) + M := by
      have : n < M * (n / M) + M := by
        have := Nat.mod_lt n hM
        omega
      exact_mod_cast this
    have hcR : (Nat.count Q n : ℝ) = ((n / M : ℕ) : ℝ) * c + (Nat.count Q (n % M) : ℝ) := by
      rw [hcount]; push_cast; ring
    have hremR : (Nat.count Q (n % M) : ℝ) ≤ c := by exact_mod_cast hrem
    have hc0 : (0 : ℝ) ≤ c := by positivity
    have hn0 : (n : ℝ) ≠ 0 := hnpos.ne'
    have hM0 : (M : ℝ) ≠ 0 := hMpos.ne'
    constructor
    · have hq2 : (n : ℝ) / M - 1 ≤ ((n / M : ℕ) : ℝ) := by
        rw [sub_le_iff_le_add, div_le_iff₀ hMpos]
        linarith
      have hle : (c : ℝ) * (n / M - 1) ≤ (Nat.count Q n : ℝ) := by
        rw [hcR]
        have := mul_le_mul_of_nonneg_left hq2 hc0
        have hr0 : (0 : ℝ) ≤ (Nat.count Q (n % M) : ℝ) := by positivity
        nlinarith
      calc (c : ℝ) / M - c / n = (c * (n / M - 1)) / n := by field_simp
        _ ≤ _ := div_le_div_of_nonneg_right hle hnpos.le
    · have hq2 : ((n / M : ℕ) : ℝ) ≤ n / M := by
        rw [le_div_iff₀ hMpos]
        linarith
      have hle : (Nat.count Q n : ℝ) ≤ c * (n / M) + c := by
        rw [hcR]
        have := mul_le_mul_of_nonneg_left hq2 hc0
        nlinarith
      calc (Nat.count Q n : ℝ) / n ≤ (c * (n / M) + c) / n :=
            div_le_div_of_nonneg_right hle hnpos.le
        _ = c / M + c / n := by field_simp
  have hlim : Tendsto (fun n : ℕ => (c : ℝ) / n) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat (c : ℝ)
  have hlow : Tendsto (fun n : ℕ => (c : ℝ) / M - c / n) atTop (𝓝 ((c : ℝ) / M)) := by
    simpa using hlim.const_sub ((c : ℝ) / M)
  have hup : Tendsto (fun n : ℕ => (c : ℝ) / M + c / n) atTop (𝓝 ((c : ℝ) / M)) := by
    simpa using hlim.const_add ((c : ℝ) / M)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow hup ?_ ?_
  · filter_upwards [eventually_gt_atTop 0] with n hn
    exact (key n hn).1
  · filter_upwards [eventually_gt_atTop 0] with n hn
    exact (key n hn).2

end Periodic


/-! ### Disjoint unions -/

lemma partialDensity_union {A B : Set ℕ} (hd : Disjoint A B) (n : ℕ) :
    partialDensity (A ∪ B) n = partialDensity A n + partialDensity B n := by
  simp only [partialDensity, Set.inter_univ]
  rw [Set.union_inter_distrib_right, Set.ncard_union_eq
    (Set.disjoint_of_subset Set.inter_subset_left Set.inter_subset_left hd)
    ((Set.finite_Iio n).subset Set.inter_subset_right)
    ((Set.finite_Iio n).subset Set.inter_subset_right)]
  push_cast
  ring

lemma hasDensity_union {A B : Set ℕ} {a b : ℝ} (hA : HasDensity A a) (hB : HasDensity B b)
    (hd : Disjoint A B) : HasDensity (A ∪ B) (a + b) := by
  unfold HasDensity at *
  have : partialDensity (A ∪ B) = fun n => partialDensity A n + partialDensity B n := by
    funext n
    exact partialDensity_union hd n
  rw [this]
  exact hA.add hB

/-! ### Valuations through divisibility -/

lemma dvd_pow_iff_le_factorization {p n : ℕ} (hp : p.Prime) (hn : n ≠ 0) (k : ℕ) :
    p ^ k ∣ n ↔ k ≤ n.factorization p := by
  rw [Nat.factorization_def n hp]
  have := Fact.mk hp
  exact padicValNat_dvd_iff_le hn

lemma dvd_iff_le_factorization {p n : ℕ} (hp : p.Prime) (hn : n ≠ 0) :
    p ∣ n ↔ 1 ≤ n.factorization p := by
  simpa using dvd_pow_iff_le_factorization hp hn 1

/-! ### The instance `S = {3, 5, 7, 11, 13}` -/

/-- `p` divides `n` exactly once. -/
def P (p n : ℕ) : Prop := p ∣ n ∧ ¬ p ^ 2 ∣ n
/-- `q` does not divide `n`. -/
def C (q n : ℕ) : Prop := ¬ q ∣ n

instance (p n : ℕ) : Decidable (P p n) := by unfold P; infer_instance
instance (q n : ℕ) : Decidable (C q n) := by unfold C; infer_instance

def Q3 (n : ℕ) : Prop := P 3 n ∧ C 5 n ∧ C 7 n ∧ C 11 n ∧ C 13 n
def Q5 (n : ℕ) : Prop := P 5 n ∧ C 3 n ∧ C 7 n ∧ C 11 n ∧ C 13 n
def Q7 (n : ℕ) : Prop := P 7 n ∧ C 3 n ∧ C 5 n ∧ C 11 n ∧ C 13 n
def Q11 (n : ℕ) : Prop := P 11 n ∧ C 3 n ∧ C 5 n ∧ C 7 n ∧ C 13 n
def Q13 (n : ℕ) : Prop := P 13 n ∧ C 3 n ∧ C 5 n ∧ C 7 n ∧ C 11 n

instance : DecidablePred Q3 := fun n => by unfold Q3; infer_instance
instance : DecidablePred Q5 := fun n => by unfold Q5; infer_instance
instance : DecidablePred Q7 := fun n => by unfold Q7; infer_instance
instance : DecidablePred Q11 := fun n => by unfold Q11; infer_instance
instance : DecidablePred Q13 := fun n => by unfold Q13; infer_instance

lemma P_periodic {p M : ℕ} (h : p ^ 2 ∣ M) (n : ℕ) : P p (n + M) ↔ P p n := by
  have h1 : p ∣ M := (dvd_pow_self p two_ne_zero).trans h
  unfold P
  rw [Nat.dvd_add_left h1, Nat.dvd_add_left h]

lemma C_periodic {q M : ℕ} (h : q ∣ M) (n : ℕ) : C q (n + M) ↔ C q n := by
  unfold C
  rw [Nat.dvd_add_left h]

lemma Q3_periodic : Function.Periodic Q3 45045 := by
  intro n
  unfold Q3
  rw [P_periodic (by norm_num), C_periodic (by norm_num), C_periodic (by norm_num),
    C_periodic (by norm_num), C_periodic (by norm_num)]

lemma Q5_periodic : Function.Periodic Q5 75075 := by
  intro n
  unfold Q5
  rw [P_periodic (by norm_num), C_periodic (by norm_num), C_periodic (by norm_num),
    C_periodic (by norm_num), C_periodic (by norm_num)]

lemma Q7_periodic : Function.Periodic Q7 105105 := by
  intro n
  unfold Q7
  rw [P_periodic (by norm_num), C_periodic (by norm_num), C_periodic (by norm_num),
    C_periodic (by norm_num), C_periodic (by norm_num)]

lemma Q11_periodic : Function.Periodic Q11 165165 := by
  intro n
  unfold Q11
  rw [P_periodic (by norm_num), C_periodic (by norm_num), C_periodic (by norm_num),
    C_periodic (by norm_num), C_periodic (by norm_num)]

lemma Q13_periodic : Function.Periodic Q13 195195 := by
  intro n
  unfold Q13
  rw [P_periodic (by norm_num), C_periodic (by norm_num), C_periodic (by norm_num),
    C_periodic (by norm_num), C_periodic (by norm_num)]

set_option maxRecDepth 100000 in
lemma c3_0 : Nat.count Q3 15015 = 1920 := by decide +kernel

set_option maxRecDepth 100000 in
lemma c3_1 : Nat.count (fun k => Q3 (15015 + k)) 15015 = 1920 := by decide +kernel

set_option maxRecDepth 100000 in
lemma c3_2 : Nat.count (fun k => Q3 (30030 + k)) 15015 = 1920 := by decide +kernel

lemma s3_1 : Nat.count Q3 30030 = 3840 := by
  rw [show (30030:ℕ) = 15015 + 15015 by norm_num, Nat.count_add, c3_0, c3_1]

lemma s3_2 : Nat.count Q3 45045 = 5760 := by
  rw [show (45045:ℕ) = 30030 + 15015 by norm_num, Nat.count_add, s3_1, c3_2]

lemma count_Q3 : Nat.count Q3 45045 = 5760 := s3_2

set_option maxRecDepth 100000 in
lemma c5_0 : Nat.count Q5 15015 = 1152 := by decide +kernel

set_option maxRecDepth 100000 in
lemma c5_1 : Nat.count (fun k => Q5 (15015 + k)) 15015 = 1152 := by decide +kernel

set_option maxRecDepth 100000 in
lemma c5_2 : Nat.count (fun k => Q5 (30030 + k)) 15015 = 1152 := by decide +kernel

set_option maxRecDepth 100000 in
lemma c5_3 : Nat.count (fun k => Q5 (45045 + k)) 15015 = 1152 := by decide +kernel

set_option maxRecDepth 100000 in
lemma c5_4 : Nat.count (fun k => Q5 (60060 + k)) 15015 = 1152 := by decide +kernel

lemma s5_1 : Nat.count Q5 30030 = 2304 := by
  rw [show (30030:ℕ) = 15015 + 15015 by norm_num, Nat.count_add, c5_0, c5_1]

lemma s5_2 : Nat.count Q5 45045 = 3456 := by
  rw [show (45045:ℕ) = 30030 + 15015 by norm_num, Nat.count_add, s5_1, c5_2]

lemma s5_3 : Nat.count Q5 60060 = 4608 := by
  rw [show (60060:ℕ) = 45045 + 15015 by norm_num, Nat.count_add, s5_2, c5_3]

lemma s5_4 : Nat.count Q5 75075 = 5760 := by
  rw [show (75075:ℕ) = 60060 + 15015 by norm_num, Nat.count_add, s5_3, c5_4]

lemma count_Q5 : Nat.count Q5 75075 = 5760 := s5_4

set_option maxRecDepth 100000 in
lemma c7_0 : Nat.count Q7 15015 = 822 := by decide +kernel

set_option maxRecDepth 100000 in
lemma c7_1 : Nat.count (fun k => Q7 (15015 + k)) 15015 = 824 := by decide +kernel

set_option maxRecDepth 100000 in
lemma c7_2 : Nat.count (fun k => Q7 (30030 + k)) 15015 = 822 := by decide +kernel

set_option maxRecDepth 100000 in
lemma c7_3 : Nat.count (fun k => Q7 (45045 + k)) 15015 = 824 := by decide +kernel

set_option maxRecDepth 100000 in
lemma c7_4 : Nat.count (fun k => Q7 (60060 + k)) 15015 = 822 := by decide +kernel

set_option maxRecDepth 100000 in
lemma c7_5 : Nat.count (fun k => Q7 (75075 + k)) 15015 = 824 := by decide +kernel

set_option maxRecDepth 100000 in
lemma c7_6 : Nat.count (fun k => Q7 (90090 + k)) 15015 = 822 := by decide +kernel

lemma s7_1 : Nat.count Q7 30030 = 1646 := by
  rw [show (30030:ℕ) = 15015 + 15015 by norm_num, Nat.count_add, c7_0, c7_1]

lemma s7_2 : Nat.count Q7 45045 = 2468 := by
  rw [show (45045:ℕ) = 30030 + 15015 by norm_num, Nat.count_add, s7_1, c7_2]

lemma s7_3 : Nat.count Q7 60060 = 3292 := by
  rw [show (60060:ℕ) = 45045 + 15015 by norm_num, Nat.count_add, s7_2, c7_3]

lemma s7_4 : Nat.count Q7 75075 = 4114 := by
  rw [show (75075:ℕ) = 60060 + 15015 by norm_num, Nat.count_add, s7_3, c7_4]

lemma s7_5 : Nat.count Q7 90090 = 4938 := by
  rw [show (90090:ℕ) = 75075 + 15015 by norm_num, Nat.count_add, s7_4, c7_5]

lemma s7_6 : Nat.count Q7 105105 = 5760 := by
  rw [show (105105:ℕ) = 90090 + 15015 by norm_num, Nat.count_add, s7_5, c7_6]

lemma count_Q7 : Nat.count Q7 105105 = 5760 := s7_6

set_option maxRecDepth 100000 in
lemma c11_0 : Nat.count Q11 15015 = 523 := by decide +kernel

set_option maxRecDepth 100000 in
lemma c11_1 : Nat.count (fun k => Q11 (15015 + k)) 15015 = 524 := by decide +kernel

set_option maxRecDepth 100000 in
lemma c11_2 : Nat.count (fun k => Q11 (30030 + k)) 15015 = 524 := by decide +kernel

set_option maxRecDepth 100000 in
lemma c11_3 : Nat.count (fun k => Q11 (45045 + k)) 15015 = 523 := by decide +kernel

set_option maxRecDepth 100000 in
lemma c11_4 : Nat.count (fun k => Q11 (60060 + k)) 15015 = 525 := by decide +kernel

set_option maxRecDepth 100000 in
lemma c11_5 : Nat.count (fun k => Q11 (75075 + k)) 15015 = 522 := by decide +kernel

set_option maxRecDepth 100000 in
lemma c11_6 : Nat.count (fun k => Q11 (90090 + k)) 15015 = 525 := by decide +kernel

set_option maxRecDepth 100000 in
lemma c11_7 : Nat.count (fun k => Q11 (105105 + k)) 15015 = 523 := by decide +kernel

set_option maxRecDepth 100000 in
lemma c11_8 : Nat.count (fun k => Q11 (120120 + k)) 15015 = 524 := by decide +kernel

set_option maxRecDepth 100000 in
lemma c11_9 : Nat.count (fun k => Q11 (135135 + k)) 15015 = 524 := by decide +kernel

set_option maxRecDepth 100000 in
lemma c11_10 : Nat.count (fun k => Q11 (150150 + k)) 15015 = 523 := by decide +kernel

lemma s11_1 : Nat.count Q11 30030 = 1047 := by
  rw [show (30030:ℕ) = 15015 + 15015 by norm_num, Nat.count_add, c11_0, c11_1]

lemma s11_2 : Nat.count Q11 45045 = 1571 := by
  rw [show (45045:ℕ) = 30030 + 15015 by norm_num, Nat.count_add, s11_1, c11_2]

lemma s11_3 : Nat.count Q11 60060 = 2094 := by
  rw [show (60060:ℕ) = 45045 + 15015 by norm_num, Nat.count_add, s11_2, c11_3]

lemma s11_4 : Nat.count Q11 75075 = 2619 := by
  rw [show (75075:ℕ) = 60060 + 15015 by norm_num, Nat.count_add, s11_3, c11_4]

lemma s11_5 : Nat.count Q11 90090 = 3141 := by
  rw [show (90090:ℕ) = 75075 + 15015 by norm_num, Nat.count_add, s11_4, c11_5]

lemma s11_6 : Nat.count Q11 105105 = 3666 := by
  rw [show (105105:ℕ) = 90090 + 15015 by norm_num, Nat.count_add, s11_5, c11_6]

lemma s11_7 : Nat.count Q11 120120 = 4189 := by
  rw [show (120120:ℕ) = 105105 + 15015 by norm_num, Nat.count_add, s11_6, c11_7]

lemma s11_8 : Nat.count Q11 135135 = 4713 := by
  rw [show (135135:ℕ) = 120120 + 15015 by norm_num, Nat.count_add, s11_7, c11_8]

lemma s11_9 : Nat.count Q11 150150 = 5237 := by
  rw [show (150150:ℕ) = 135135 + 15015 by norm_num, Nat.count_add, s11_8, c11_9]

lemma s11_10 : Nat.count Q11 165165 = 5760 := by
  rw [show (165165:ℕ) = 150150 + 15015 by norm_num, Nat.count_add, s11_9, c11_10]

lemma count_Q11 : Nat.count Q11 165165 = 5760 := s11_10

set_option maxRecDepth 100000 in
lemma c13_0 : Nat.count Q13 15015 = 443 := by decide +kernel

set_option maxRecDepth 100000 in
lemma c13_1 : Nat.count (fun k => Q13 (15015 + k)) 15015 = 443 := by decide +kernel

set_option maxRecDepth 100000 in
lemma c13_2 : Nat.count (fun k => Q13 (30030 + k)) 15015 = 444 := by decide +kernel

set_option maxRecDepth 100000 in
lemma c13_3 : Nat.count (fun k => Q13 (45045 + k)) 15015 = 443 := by decide +kernel

set_option maxRecDepth 100000 in
lemma c13_4 : Nat.count (fun k => Q13 (60060 + k)) 15015 = 442 := by decide +kernel

set_option maxRecDepth 100000 in
lemma c13_5 : Nat.count (fun k => Q13 (75075 + k)) 15015 = 444 := by decide +kernel

set_option maxRecDepth 100000 in
lemma c13_6 : Nat.count (fun k => Q13 (90090 + k)) 15015 = 442 := by decide +kernel

set_option maxRecDepth 100000 in
lemma c13_7 : Nat.count (fun k => Q13 (105105 + k)) 15015 = 444 := by decide +kernel

set_option maxRecDepth 100000 in
lemma c13_8 : Nat.count (fun k => Q13 (120120 + k)) 15015 = 442 := by decide +kernel

set_option maxRecDepth 100000 in
lemma c13_9 : Nat.count (fun k => Q13 (135135 + k)) 15015 = 443 := by decide +kernel

set_option maxRecDepth 100000 in
lemma c13_10 : Nat.count (fun k => Q13 (150150 + k)) 15015 = 444 := by decide +kernel

set_option maxRecDepth 100000 in
lemma c13_11 : Nat.count (fun k => Q13 (165165 + k)) 15015 = 443 := by decide +kernel

set_option maxRecDepth 100000 in
lemma c13_12 : Nat.count (fun k => Q13 (180180 + k)) 15015 = 443 := by decide +kernel

lemma s13_1 : Nat.count Q13 30030 = 886 := by
  rw [show (30030:ℕ) = 15015 + 15015 by norm_num, Nat.count_add, c13_0, c13_1]

lemma s13_2 : Nat.count Q13 45045 = 1330 := by
  rw [show (45045:ℕ) = 30030 + 15015 by norm_num, Nat.count_add, s13_1, c13_2]

lemma s13_3 : Nat.count Q13 60060 = 1773 := by
  rw [show (60060:ℕ) = 45045 + 15015 by norm_num, Nat.count_add, s13_2, c13_3]

lemma s13_4 : Nat.count Q13 75075 = 2215 := by
  rw [show (75075:ℕ) = 60060 + 15015 by norm_num, Nat.count_add, s13_3, c13_4]

lemma s13_5 : Nat.count Q13 90090 = 2659 := by
  rw [show (90090:ℕ) = 75075 + 15015 by norm_num, Nat.count_add, s13_4, c13_5]

lemma s13_6 : Nat.count Q13 105105 = 3101 := by
  rw [show (105105:ℕ) = 90090 + 15015 by norm_num, Nat.count_add, s13_5, c13_6]

lemma s13_7 : Nat.count Q13 120120 = 3545 := by
  rw [show (120120:ℕ) = 105105 + 15015 by norm_num, Nat.count_add, s13_6, c13_7]

lemma s13_8 : Nat.count Q13 135135 = 3987 := by
  rw [show (135135:ℕ) = 120120 + 15015 by norm_num, Nat.count_add, s13_7, c13_8]

lemma s13_9 : Nat.count Q13 150150 = 4430 := by
  rw [show (150150:ℕ) = 135135 + 15015 by norm_num, Nat.count_add, s13_8, c13_9]

lemma s13_10 : Nat.count Q13 165165 = 4874 := by
  rw [show (165165:ℕ) = 150150 + 15015 by norm_num, Nat.count_add, s13_9, c13_10]

lemma s13_11 : Nat.count Q13 180180 = 5317 := by
  rw [show (180180:ℕ) = 165165 + 15015 by norm_num, Nat.count_add, s13_10, c13_11]

lemma s13_12 : Nat.count Q13 195195 = 5760 := by
  rw [show (195195:ℕ) = 180180 + 15015 by norm_num, Nat.count_add, s13_11, c13_12]

lemma count_Q13 : Nat.count Q13 195195 = 5760 := s13_12

/-- The five pieces, as sets. -/
def A3 : Set ℕ := {k | Q3 k}
def A5 : Set ℕ := {k | Q5 k}
def A7 : Set ℕ := {k | Q7 k}
def A11 : Set ℕ := {k | Q11 k}
def A13 : Set ℕ := {k | Q13 k}

def Afull : Set ℕ := (((A3 ∪ A5) ∪ A7) ∪ A11) ∪ A13

lemma density_A3 : HasDensity A3 (128 / 1001) := by
  have := hasDensity_periodic Q3 45045 (by norm_num) Q3_periodic
  rw [count_Q3] at this
  have h : ((5760 : ℕ) : ℝ) / ((45045 : ℕ) : ℝ) = 128 / 1001 := by norm_num
  rw [h] at this
  exact this

lemma density_A5 : HasDensity A5 (384 / 5005) := by
  have := hasDensity_periodic Q5 75075 (by norm_num) Q5_periodic
  rw [count_Q5] at this
  have h : ((5760 : ℕ) : ℝ) / ((75075 : ℕ) : ℝ) = 384 / 5005 := by norm_num
  rw [h] at this
  exact this

lemma density_A7 : HasDensity A7 (384 / 7007) := by
  have := hasDensity_periodic Q7 105105 (by norm_num) Q7_periodic
  rw [count_Q7] at this
  have h : ((5760 : ℕ) : ℝ) / ((105105 : ℕ) : ℝ) = 384 / 7007 := by norm_num
  rw [h] at this
  exact this

lemma density_A11 : HasDensity A11 (384 / 11011) := by
  have := hasDensity_periodic Q11 165165 (by norm_num) Q11_periodic
  rw [count_Q11] at this
  have h : ((5760 : ℕ) : ℝ) / ((165165 : ℕ) : ℝ) = 384 / 11011 := by norm_num
  rw [h] at this
  exact this

lemma density_A13 : HasDensity A13 (384 / 13013) := by
  have := hasDensity_periodic Q13 195195 (by norm_num) Q13_periodic
  rw [count_Q13] at this
  have h : ((5760 : ℕ) : ℝ) / ((195195 : ℕ) : ℝ) = 384 / 13013 := by norm_num
  rw [h] at this
  exact this

lemma disj_A3_A5 : Disjoint A3 A5 := by
  rw [Set.disjoint_left]
  intro n h3 h5
  exact h5.2.1 h3.1.1

lemma disj_A35_A7 : Disjoint (A3 ∪ A5) A7 := by
  rw [Set.disjoint_union_left]
  constructor
  · rw [Set.disjoint_left]
    intro n h3 h7
    exact h7.2.1 h3.1.1
  · rw [Set.disjoint_left]
    intro n h5 h7
    exact h7.2.2.1 h5.1.1

lemma disj_A357_A11 : Disjoint ((A3 ∪ A5) ∪ A7) A11 := by
  rw [Set.disjoint_union_left, Set.disjoint_union_left]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [Set.disjoint_left]
    intro n h3 h11
    exact h11.2.1 h3.1.1
  · rw [Set.disjoint_left]
    intro n h5 h11
    exact h11.2.2.1 h5.1.1
  · rw [Set.disjoint_left]
    intro n h7 h11
    exact h11.2.2.2.1 h7.1.1

lemma disj_A35711_A13 : Disjoint (((A3 ∪ A5) ∪ A7) ∪ A11) A13 := by
  rw [Set.disjoint_union_left, Set.disjoint_union_left, Set.disjoint_union_left]
  refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
  · rw [Set.disjoint_left]
    intro n h3 h13
    exact h13.2.1 h3.1.1
  · rw [Set.disjoint_left]
    intro n h5 h13
    exact h13.2.2.1 h5.1.1
  · rw [Set.disjoint_left]
    intro n h7 h13
    exact h13.2.2.2.1 h7.1.1
  · rw [Set.disjoint_left]
    intro n h11 h13
    exact h13.2.2.2.2 h11.1.1

lemma density_Afull : HasDensity Afull (1622144 / 5010005) := by
  have h := hasDensity_union (hasDensity_union (hasDensity_union (hasDensity_union
    density_A3 density_A5 disj_A3_A5) density_A7 disj_A35_A7) density_A11 disj_A357_A11)
    density_A13 disj_A35711_A13
  have e : (128 / 1001 + 384 / 5005 + 384 / 7007 + 384 / 11011 + 384 / 13013 : ℝ)
      = 1622144 / 5010005 := by norm_num
  rw [e] at h
  exact h

/-- The weight-one set for `S = {3,5,7,11,13}` is the union of the five pieces. -/
lemma level_eq_Afull : {n | w {3, 5, 7, 11, 13} n = 1} = Afull := by
  ext n
  simp only [Set.mem_setOf_eq, Afull, A3, A5, A7, A11, A13, Set.mem_union]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [w_zero, Q3, Q5, Q7, Q11, Q13, P]
  have hn0 : n ≠ 0 := hn.ne'
  have hw : w {3, 5, 7, 11, 13} n = n.factorization 3 + n.factorization 5 + n.factorization 7
      + n.factorization 11 + n.factorization 13 := by
    simp [w, Finset.sum_insert, add_assoc]
  rw [hw]
  have d3 := dvd_iff_le_factorization (by norm_num : Nat.Prime 3) hn0
  have d5 := dvd_iff_le_factorization (by norm_num : Nat.Prime 5) hn0
  have d7 := dvd_iff_le_factorization (by norm_num : Nat.Prime 7) hn0
  have d11 := dvd_iff_le_factorization (by norm_num : Nat.Prime 11) hn0
  have d13 := dvd_iff_le_factorization (by norm_num : Nat.Prime 13) hn0
  have s3 := dvd_pow_iff_le_factorization (by norm_num : Nat.Prime 3) hn0 2
  have s5 := dvd_pow_iff_le_factorization (by norm_num : Nat.Prime 5) hn0 2
  have s7 := dvd_pow_iff_le_factorization (by norm_num : Nat.Prime 7) hn0 2
  have s11 := dvd_pow_iff_le_factorization (by norm_num : Nat.Prime 11) hn0 2
  have s13 := dvd_pow_iff_le_factorization (by norm_num : Nat.Prime 13) hn0 2
  simp only [Q3, Q5, Q7, Q11, Q13, P, C, d3, d5, d7, d11, d13, s3, s5, s7, s11, s13]
  omega

theorem proof : ∃ A : Set ℕ, 0 ∉ A ∧ HasDensity A (1622144 / 5010005) ∧ IsMulCardSet A := by
  refine ⟨{n | w {3, 5, 7, 11, 13} n = 1}, ?_, ?_, isMulCardSet_level _⟩
  · simp [w_zero]
  · rw [level_eq_Afull]
    exact density_Afull

end Submissions.Erdos786SelfridgeFivePrimeDensity.Periodic
