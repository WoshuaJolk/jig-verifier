import Mathlib

/-! Erdős 884 complete disproof, ported to Lean 4.33.
Flattened from the published modular development without omitting any endpoint dependency. -/

/-! Flattened from Erdos884/SieveVendored.lean. -/
section

/-! ### Vendored from PrimeNumberTheoremAnd/Mathlib/NumberTheory/Sieve/AuxResults.lean -/
/-
Copyright (c) 2023 Arend Mellendijk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Arend Mellendijk

! This file was ported from Lean 3 source module aux_results
-/





noncomputable section

open scoped BigOperators ArithmeticFunction ArithmeticFunction.Moebius ArithmeticFunction.omega

open Nat ArithmeticFunction Finset


namespace ArithmeticFunction.IsMultiplicative

variable {R : Type*}

theorem prod_factors_of_mult (f : ArithmeticFunction ℝ)
    (h_mult : ArithmeticFunction.IsMultiplicative f) {l : ℕ} (hl : Squarefree l) :
    ∏ a ∈ l.primeFactors, f a = f l := by
  rw [←IsMultiplicative.map_prod_of_subset_primeFactors h_mult l _ Finset.Subset.rfl,
    Nat.prod_primeFactors_of_squarefree hl]

end ArithmeticFunction.IsMultiplicative

namespace Aux
theorem sum_over_dvd_ite {α : Type _} [Ring α] {P : ℕ} (hP : P ≠ 0) {n : ℕ} (hn : n ∣ P)
    {f : ℕ → α} : ∑ d ∈ n.divisors, f d = ∑ d ∈ P.divisors, if d ∣ n then f d else 0 :=
  by
  rw [←Finset.sum_filter, Nat.divisors_filter_dvd_of_dvd hP hn]

theorem ite_sum_zero {p : Prop} [Decidable p] (s : Finset ℕ) (f : ℕ → ℝ) :
    (if p then (∑ x ∈ s, f x) else 0) = ∑ x ∈ s, if p then f x else 0 := by
  split_ifs <;> simp

theorem conv_lambda_sq_larger_sum (f : ℕ → ℕ → ℕ → ℝ) (n : ℕ) :
    (∑ d ∈ n.divisors,
        ∑ d1 ∈ d.divisors,
          ∑ d2 ∈ d.divisors, if d = Nat.lcm d1 d2 then f d1 d2 d else 0) =
      ∑ d ∈ n.divisors,
        ∑ d1 ∈ n.divisors,
          ∑ d2 ∈ n.divisors, if d = Nat.lcm d1 d2 then f d1 d2 d else 0 := by
  apply sum_congr rfl; intro d hd
  rw [mem_divisors] at hd
  simp_rw [←Nat.divisors_filter_dvd_of_dvd hd.2 hd.1, sum_filter, ←ite_and, ite_sum_zero,
    ←ite_and]
  congr with d1
  congr with d2
  congr
  rw [eq_iff_iff]
  refine ⟨fun ⟨_, _, h⟩ ↦ h, ?_⟩
  rintro rfl
  exact ⟨Nat.dvd_lcm_left d1 d2, Nat.dvd_lcm_right d1 d2, rfl⟩

theorem moebius_inv_dvd_lower_bound (l m : ℕ) (hm : Squarefree m) :
    (∑ d ∈ m.divisors, if l ∣ d then (μ d:ℤ) else 0) = if l = m then (μ l:ℤ) else 0 := by
  have hm_pos : 0 < m := Nat.pos_of_ne_zero hm.ne_zero
  revert hm
  revert m
  apply (ArithmeticFunction.sum_eq_iff_sum_smul_moebius_eq_on
    {n | Squarefree n} (fun _ _ => Squarefree.squarefree_of_dvd)).mpr
  intro m hm_pos hm
  rw [sum_divisorsAntidiagonal' (f:= fun x y => μ x • if l=y then μ l else 0)]--
  by_cases hl : l ∣ m
  · rw [if_pos hl, sum_eq_single l]
    · have hmul : m / l * l = m := Nat.div_mul_cancel hl
      rw [if_pos rfl, smul_eq_mul, ←isMultiplicative_moebius.map_mul_of_coprime,
        hmul]

      apply coprime_of_squarefree_mul; rw [hmul]; exact hm
    · intro d _ hdl; rw [if_neg hdl.symm, smul_zero]
    · intro h; rw[mem_divisors] at h; exfalso; exact h ⟨hl, (Nat.ne_of_lt hm_pos).symm⟩
  · rw [if_neg hl, sum_eq_zero]; intro d hd
    rw [if_neg, smul_zero]
    by_contra h; rw [←h] at hd; exact hl (dvd_of_mem_divisors hd)


theorem moebius_inv_dvd_lower_bound' {P : ℕ} (hP : Squarefree P) (l m : ℕ) (hm : m ∣ P) :
    (∑ d ∈ P.divisors, if l ∣ d ∧ d ∣ m then μ d else 0) = if l = m then μ l else 0 := by
  rw [←moebius_inv_dvd_lower_bound _ _ (Squarefree.squarefree_of_dvd hm hP),
    sum_over_dvd_ite hP.ne_zero hm]
  simp_rw[ite_and, ←sum_filter, filter_comm]

theorem moebius_inv_dvd_lower_bound_real {P : ℕ} (hP : Squarefree P) (l m : ℕ) (hm : m ∣ P) :
    (∑ d ∈ P.divisors, if l ∣ d ∧ d ∣ m then (μ d : ℝ) else 0) =
      if l = m then (μ l : ℝ) else 0 := by
  norm_cast
  apply moebius_inv_dvd_lower_bound' hP l m hm

theorem multiplicative_zero_of_zero_dvd (f : ArithmeticFunction ℝ) (h_mult : IsMultiplicative f)
    {m n : ℕ} (h_sq : Squarefree n) (hmn : m ∣ n) (h_zero : f m = 0) : f n = 0 := by
  rcases hmn with ⟨k, rfl⟩
  simp only [MulZeroClass.zero_mul,
    h_mult.map_mul_of_coprime (coprime_of_squarefree_mul h_sq), h_zero]

theorem div_mult_of_dvd_squarefree (f : ArithmeticFunction ℝ) (h_mult : IsMultiplicative f)
    (l d : ℕ) (hdl : d ∣ l) (hl : Squarefree l) (hd : f d ≠ 0) : f l / f d = f (l / d) := by
  apply div_eq_of_eq_mul hd
  rw [← h_mult.right, Nat.div_mul_cancel hdl]
  apply coprime_of_squarefree_mul
  convert hl
  exact Nat.div_mul_cancel hdl

theorem inv_sub_antitoneOn_gt
    {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] (c : R) :
    AntitoneOn (fun x:R ↦ (x-c)⁻¹) (Set.Ioi c) := by
  refine antitoneOn_iff_forall_lt.mpr ?_
  intro a ha b hb hab
  rw [Set.mem_Ioi] at ha hb
  gcongr

theorem inv_sub_antitoneOn_Icc
    {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    (a b c : R) (ha : c < a) :
    AntitoneOn (fun x ↦ (x-c)⁻¹) (Set.Icc a b) := by
  by_cases hab : a ≤ b
  · exact inv_sub_antitoneOn_gt c |>.mono <| (Set.Icc_subset_Ioi_iff hab).mpr ha
  · simp [hab, Set.Subsingleton.antitoneOn]

theorem inv_antitoneOn_pos {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] :
    AntitoneOn (fun x:R ↦ x⁻¹) (Set.Ioi 0) := by
  convert inv_sub_antitoneOn_gt (R:=R) 0; ring

theorem inv_antitoneOn_Icc {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    (a b : R) (ha : 0 < a) :
    AntitoneOn (fun x ↦ x⁻¹) (Set.Icc a b) := by
  convert inv_sub_antitoneOn_Icc a b 0 ha; ring

theorem log_add_one_le_sum_inv (n : ℕ) :
    Real.log ↑(n+1) ≤ ∑ d ∈ Finset.Icc 1 n, (d:ℝ)⁻¹ := by
  calc _ = ∫ x in (1)..↑(n+1), x⁻¹ := ?_
       _ = ∫ x in (1:ℕ)..↑(n+1), x⁻¹ := ?_
       _ ≤ _ := ?_
  · rw[integral_inv (by simp[(show ¬ (1:ℝ) ≤ 0 by norm_num)] )]; congr; ring
  · congr; norm_num
  · apply AntitoneOn.integral_le_sum_Ico (by norm_num)
    apply inv_antitoneOn_Icc
    norm_num

theorem log_le_sum_inv (y : ℝ) (hy : 1 ≤ y) :
    Real.log y ≤ ∑ d ∈ Finset.Icc 1 (⌊y⌋₊), (d:ℝ)⁻¹ := by
  calc _ ≤ Real.log ↑(Nat.floor y + 1) := ?_
       _ ≤ _ := ?_
  · gcongr
    apply (le_ceil y).trans
    norm_cast
    exact ceil_le_floor_add_one y
  · apply log_add_one_le_sum_inv

theorem sum_inv_le_log (n : ℕ) (hn : 1 ≤ n) :
    ∑ d ∈ Finset.Icc 1 n, (d : ℝ)⁻¹ ≤ 1 + Real.log ↑n :=
  by
  rw [← Finset.sum_erase_add (Icc 1 n) _ (by simp [hn] : 1 ∈ Icc 1 n), add_comm]
  gcongr
  · norm_num
  simp only [Icc_erase_left]
  calc
    ∑ d ∈ Ico 2 (n + 1), (d : ℝ)⁻¹ = ∑ d ∈ Ico 2 (n + 1), (↑(d + 1) - 1)⁻¹ := ?_
    _ ≤ ∫ x in (2).. ↑(n + 1), (x - 1)⁻¹  := ?_
    _ = Real.log ↑n := ?_
  · congr; norm_num;
  · apply @AntitoneOn.sum_le_integral_Ico 2 (n + 1) fun x : ℝ => (x - 1)⁻¹
    · linarith [hn]
    apply inv_sub_antitoneOn_Icc; norm_num
  rw [intervalIntegral.integral_comp_sub_right _ 1, integral_inv]
  · norm_num
  norm_num; simp[hn, show (0:ℝ) < 1 by norm_num]

theorem sum_inv_le_log_real (y : ℝ) (hy : 1 ≤ y) :
    ∑ d ∈ Finset.Icc 1 (⌊y⌋₊), (d:ℝ)⁻¹ ≤ 1 + Real.log y := by
  trans (1 + Real.log (⌊y⌋₊))
  · apply sum_inv_le_log (⌊y⌋₊)
    apply le_floor; norm_cast
  gcongr
  · norm_cast; apply Nat.lt_of_succ_le; apply le_floor; norm_cast
  · apply floor_le; linarith

-- Lemma 3.1 in Heath-Brown's notes
theorem sum_pow_cardDistinctFactors_div_self_le_log_pow {P k : ℕ} (x : ℝ) (hx : 1 ≤ x)
    (hP : Squarefree P) :
    (∑ d ∈ P.divisors, if d ≤ x then (k:ℝ) ^ (ω d) / (d : ℝ) else (0 : ℝ))
    ≤ (1 + Real.log x) ^ k := by
  have hx_pos : 0 < x := by
    linarith
  calc
    _ = ∑ d ∈ P.divisors,
          ∑ a ∈ Fintype.piFinset fun _i : Fin k => P.divisors,
            if ∏ i, a i = d ∧ d ∣ P then if ↑d ≤ x then (d : ℝ)⁻¹ else 0 else 0 := ?_
    _ = ∑ a ∈ Fintype.piFinset fun _i : Fin k => P.divisors,
          if ∏ i, a i ∣ P then if ↑(∏ i, a i) ≤ x then ∏ i, (a i : ℝ)⁻¹ else 0 else 0 := ?_
    _ ≤ ∑ a ∈ Fintype.piFinset fun _i : Fin k => P.divisors,
          if ↑(∏ i, a i) ≤ x then ∏ i, (a i : ℝ)⁻¹ else 0 := ?_ -- do we need this one?
    _ ≤ ∑ a ∈ Fintype.piFinset fun _i : Fin k => P.divisors,
          ∏ i, if ↑(a i) ≤ x then (a i : ℝ)⁻¹ else 0 := ?_
    _ = ∏ _i : Fin k, ∑ d ∈ P.divisors, if ↑d ≤ x then (d : ℝ)⁻¹ else 0 := by rw [prod_univ_sum]
    _ = (∑ d ∈ P.divisors, if ↑d ≤ x then (d : ℝ)⁻¹ else 0) ^ k := by
      rw [prod_const, Finset.card_fin]
    _ ≤ (1 + Real.log x) ^ k := ?_

  · apply sum_congr rfl; intro d hd
    rw [mem_divisors] at hd
    simp_rw [ite_and];
    rw [← sum_filter, Finset.sum_const, ← finMulAntidiag_eq_piFinset_divisors_filter hd.1 hd.2,
      card_finMulAntidiag_of_squarefree <| hP.squarefree_of_dvd hd.1, if_pos hd.1]
    simp only [div_eq_mul_inv, nsmul_eq_mul, cast_pow, mul_ite, mul_zero]
  · rw [sum_comm]; apply sum_congr rfl; intro a _; rw [sum_eq_single (∏ i, a i)]
    · apply if_ctx_congr _ _ (fun _ => rfl)
      · rw [Iff.comm, iff_and_self]; exact fun _ => rfl
      · intro; rw [cast_prod, ← prod_inv_distrib]
    · exact fun d _ hd_ne ↦ if_neg fun h => hd_ne.symm h.1
    · exact fun h ↦ if_neg fun h' => h (mem_divisors.mpr ⟨h'.2, hP.ne_zero⟩)
  · apply sum_le_sum; intro a _
    by_cases h : (∏ i, a i ∣ P)
    · rw [if_pos h]
    rw [if_neg h]
    split_ifs with h'
    · apply prod_nonneg; intro i _; norm_num
    · rfl
  · apply sum_le_sum; intro a ha
    split_ifs with h
    · gcongr with i hi
      rw [if_pos]
      apply le_trans _ h
      norm_cast
      rw [←prod_erase_mul (a:=i) (h:= hi)]
      apply Nat.le_mul_of_pos_left
      rw [Fintype.mem_piFinset] at ha
      apply prod_pos; intro j _; apply pos_of_mem_divisors (ha j)
    · apply prod_nonneg; intro j _
      split_ifs
      · norm_num
      · rfl
  · rw [←sum_filter]
    gcongr
    trans (∑ d ∈ Icc 1 (floor x), (d:ℝ)⁻¹)
    · apply sum_le_sum_of_subset_of_nonneg
      · intro d; rw[mem_filter, mem_Icc]
        intro hd
        constructor
        · rw [Nat.succ_le_iff]; exact pos_of_mem_divisors hd.1
        · rw [le_floor_iff hx_pos.le]
          exact hd.2
      · norm_num
    apply sum_inv_le_log_real
    linarith

theorem sum_pow_cardDistinctFactors_le_self_mul_log_pow {P h : ℕ} (x : ℝ) (hx : 1 ≤ x)
    (hP : Squarefree P) :
    (∑ d ∈ P.divisors, if ↑d ≤ x then (h : ℝ) ^ ω d else (0 : ℝ)) ≤
      x * (1 + Real.log x) ^ h := by
  trans (∑ d ∈ P.divisors, x * if ↑d ≤ x then (h : ℝ) ^ ω d / d else (0 : ℝ))
  · simp_rw [mul_ite, mul_zero, ←sum_filter]
    gcongr with i hi
    rw [div_eq_mul_inv, mul_comm _ (i:ℝ)⁻¹, ←mul_assoc]
    trans (1*(h:ℝ)^ω i)
    · rw [one_mul]
    gcongr
    rw [mem_filter] at hi
    rw [←div_eq_mul_inv]
    apply one_le_div (by norm_cast; apply Nat.pos_of_mem_divisors hi.1) |>.mpr hi.2
  rw [←mul_sum];
  gcongr
  apply sum_pow_cardDistinctFactors_div_self_le_log_pow x hx hP


end Aux

/-! ### Vendored from PrimeNumberTheoremAnd/Mathlib/NumberTheory/Sieve/Basic.lean -/
/-
Copyright (c) 2023 Arend Mellendijk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Arend Mellendijk

! This file was ported from Lean 3 source module sieve
-/



noncomputable section

open scoped BigOperators ArithmeticFunction ArithmeticFunction.Moebius

open Finset Real Nat Aux BoundingSieve

namespace SelbergSieve

variable (s : BoundingSieve)
local notation3 "ν" => BoundingSieve.nu (self := s)
local notation3 "P" => BoundingSieve.prodPrimes (self := s)
local notation3 "a" => BoundingSieve.weights (self := s)
local notation3 "X" => BoundingSieve.totalMass (self := s)
local notation3 "A" => BoundingSieve.support (self := s)
local notation3 "𝒜" => BoundingSieve.multSum (s := s)
local notation3 "R" => BoundingSieve.rem (s := s)

-- S = ∑_{l|P, l≤√y} g(l)
-- Used in statement of the simple form of the selberg bound
def selbergTerms : ArithmeticFunction ℝ :=
  s.nu.pmul (.prodPrimeFactors fun p =>  1 / (1 - ν p))

local notation3 "g" => SelbergSieve.selbergTerms s

theorem selbergTerms_apply (d : ℕ) :
    g d = ν d * ∏ p ∈ d.primeFactors, 1/(1 - ν p) := by
  unfold selbergTerms
  by_cases h : d=0
  · rw [h]; simp
  rw [ArithmeticFunction.pmul_apply, ArithmeticFunction.prodPrimeFactors_apply h]

section UpperBoundSieve

structure UpperBoundSieve where mk ::
  μPlus : ℕ → ℝ
  hμPlus : IsUpperMoebius μPlus

instance ubToμPlus : CoeFun UpperBoundSieve fun _ => ℕ → ℝ where coe ub := ub.μPlus

def IsLowerMoebius (μMinus : ℕ → ℝ) : Prop :=
  ∀ n : ℕ, ∑ d ∈ n.divisors, μMinus d ≤ (if n=1 then 1 else 0)

structure LowerBoundSieve where mk ::
  μMinus : ℕ → ℝ
  hμMinus : IsLowerMoebius μMinus

instance lbToμMinus : CoeFun LowerBoundSieve fun _ => ℕ → ℝ where coe lb := lb.μMinus

end UpperBoundSieve

section SieveLemmas

theorem nu_ne_zero_of_mem_divisors_prodPrimes {d : ℕ} (hd : d ∈ divisors P) : ν d ≠ 0 := by
  apply _root_.ne_of_gt
  rw [mem_divisors] at hd
  apply nu_pos_of_dvd_prodPrimes hd.left

def delta (n : ℕ) : ℝ := if n=1 then 1 else 0

local notation "δ" => delta

theorem siftedSum_as_delta : siftedSum (s := s) = ∑ d ∈ s.support, a d * δ (Nat.gcd P d) :=
  by
  rw [siftedSum_eq_sum_support_mul_ite]
  simp only [delta]

-- Unused ?
theorem nu_lt_self_of_dvd_prodPrimes (d : ℕ) (hdP : d ∣ P) (hd_ne_one : d ≠ 1) : ν d < 1 :=
  nu_lt_one_of_dvd_prodPrimes hdP hd_ne_one

-- Facts about g
@[aesop safe]
theorem selbergTerms_pos (l : ℕ) (hl : l ∣ P) : 0 < g l := by
  rw [selbergTerms_apply]
  apply mul_pos
  · exact nu_pos_of_dvd_prodPrimes hl
  apply prod_pos
  intro p hp
  rw [one_div_pos]
  have hp_prime : p.Prime := prime_of_mem_primeFactors hp
  have hp_dvd : p ∣ P := (Nat.dvd_of_mem_primeFactors hp).trans hl
  linarith only [s.nu_lt_one_of_prime p hp_prime hp_dvd]

theorem selbergTerms_mult : ArithmeticFunction.IsMultiplicative g := by
  unfold selbergTerms
  arith_mult

theorem one_div_selbergTerms_eq_conv_moebius_nu (l : ℕ) (hl : Squarefree l)
    (hnu_nonzero : ν l ≠ 0) : 1 / g l = ∑ d ∈ l.divisors, (μ <| l / d) * (ν d)⁻¹ :=
  by
  rw [selbergTerms_apply]
  simp only [one_div, prod_inv_distrib, mul_inv, inv_inv]
  rw [(s.nu_mult).prodPrimeFactors_one_sub_of_squarefree _ hl]
  rw [mul_sum]
  apply symm
  rw [← Nat.sum_divisorsAntidiagonal' fun d e : ℕ => ↑(μ d) * (ν e)⁻¹]
  rw [Nat.sum_divisorsAntidiagonal fun d e : ℕ => ↑(μ d) * (ν e)⁻¹]
  apply sum_congr rfl; intro d hd
  have hd_dvd : d ∣ l := dvd_of_mem_divisors hd
  rw [←div_mult_of_dvd_squarefree ν s.nu_mult l d (dvd_of_mem_divisors hd) hl, inv_div]
  · ring
  revert hnu_nonzero; contrapose!
  exact multiplicative_zero_of_zero_dvd ν s.nu_mult hl hd_dvd

theorem nu_eq_conv_one_div_selbergTerms (d : ℕ) (hdP : d ∣ P) :
    (ν d)⁻¹ = ∑ l ∈ divisors P, if l ∣ d then 1 / g l else 0 := by
  apply symm
  rw [←sum_filter, Nat.divisors_filter_dvd_of_dvd prodPrimes_ne_zero hdP]
  have hd_pos : 0 < d := Nat.pos_of_ne_zero <| ne_zero_of_dvd_ne_zero prodPrimes_ne_zero hdP
  revert hdP; revert d
  apply (ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq_on _ (fun _ _ => Nat.dvd_trans)).mpr
  intro l _ hlP
  rw [sum_divisorsAntidiagonal' (f:=fun x y => (μ <| x) * (ν y)⁻¹) (n:=l)]
  apply symm
  exact one_div_selbergTerms_eq_conv_moebius_nu _ l
    (Squarefree.squarefree_of_dvd hlP s.prodPrimes_squarefree)
    (_root_.ne_of_gt <| nu_pos_of_dvd_prodPrimes hlP)

theorem conv_selbergTerms_eq_selbergTerms_mul_nu {d : ℕ} (hd : d ∣ P) :
    (∑ l ∈ divisors P, if l ∣ d then g l else 0) = g d * (ν d)⁻¹ := by
  calc
    (∑ l ∈ divisors P, if l ∣ d then g l else 0) =
        ∑ l ∈ divisors P, if l ∣ d then g (d / l) else 0 := by
      rw [← sum_over_dvd_ite prodPrimes_ne_zero hd,
        ← Nat.sum_divisorsAntidiagonal fun x _ => g x,
        Nat.sum_divisorsAntidiagonal' fun x _ => g x, sum_over_dvd_ite prodPrimes_ne_zero hd]
    _ = g d * ∑ l ∈ divisors P, if l ∣ d then 1 / g l else 0 := by
      rw [mul_sum]; apply sum_congr rfl; intro l hl
      rw [mul_ite_zero]; apply if_ctx_congr Iff.rfl _ (fun _ => rfl); intro h
      rw [← div_mult_of_dvd_squarefree g (selbergTerms_mult s) d l h]
      · ring
      · apply Squarefree.squarefree_of_dvd hd s.prodPrimes_squarefree
      · apply _root_.ne_of_gt; rw [mem_divisors] at hl; apply selbergTerms_pos; exact hl.left
    _ = g d * (ν d)⁻¹ := by rw [← nu_eq_conv_one_div_selbergTerms s d hd]

theorem upper_bound_of_UpperBoundSieve (μPlus : UpperBoundSieve) :
    siftedSum (s := s) ≤ ∑ d ∈ divisors P, μPlus d * multSum (s := s) d :=
  siftedSum_le_sum_of_upperMoebius _ μPlus.hμPlus

theorem siftedSum_le_mainSum_errSum_of_UpperBoundSieve (μPlus : UpperBoundSieve) :
    siftedSum (s := s) ≤ X * mainSum (s := s) μPlus + errSum (s := s) μPlus := by
  apply siftedSum_le_mainSum_errSum_of_upperMoebius _ μPlus.hμPlus

end SieveLemmas

-- Results about Lambda Squared Sieves
section LambdaSquared

def lambdaSquared (weights : ℕ → ℝ) : ℕ → ℝ := fun d =>
  ∑ d1 ∈ d.divisors, ∑ d2 ∈ d.divisors,
    if d = Nat.lcm d1 d2 then weights d1 * weights d2 else 0

private theorem lambdaSquared_eq_zero_of_support_wlog {w : ℕ → ℝ} {y : ℝ}
    (hw : ∀ (d : ℕ), ¬d ^ 2 ≤ y → w d = 0)
    {d : ℕ} (hd : ¬↑d ≤ y) (d1 : ℕ) (d2 : ℕ) (h : d = Nat.lcm d1 d2) (hle : d1 ≤ d2) :
    w d1 * w d2 = 0 := by
  rw [hw d2, mul_zero]
  by_contra hyp; apply hd
  apply le_trans _ hyp
  norm_cast
  calc _ ≤ (d1.lcm d2) := by rw [h]
      _ ≤ (d1*d2) := Nat.div_le_self _ _
      _ ≤ _       := ?_
  · rw [sq]; gcongr

theorem lambdaSquared_eq_zero_of_support (w : ℕ → ℝ) (y : ℝ)
    (hw : ∀ d : ℕ, ¬d ^ 2 ≤ y → w d = 0) (d : ℕ) (hd : ¬d ≤ y) :
    lambdaSquared w d = 0 := by
  dsimp only [lambdaSquared]
  by_cases hy : 0 ≤ y
  swap
  · push Not at hd hy
    have : ∀ d' : ℕ, w d' = 0 := by
      intro d'; apply hw
      have : (0:ℝ) ≤ (d') ^ 2 := by norm_num
      linarith
    apply sum_eq_zero; intro d1 _
    apply sum_eq_zero; intro d2 _
    rw [this d1, this d2]
    simp only [mul_zero, ite_self]
  apply sum_eq_zero; intro d1 _
  apply sum_eq_zero; intro d2 _
  split_ifs with h
  swap
  · rfl
  rcases Nat.le_or_le d1 d2 with hle | hle
  · apply lambdaSquared_eq_zero_of_support_wlog hw hd d1 d2 h hle
  · rw [mul_comm]
    apply lambdaSquared_eq_zero_of_support_wlog hw hd d2 d1
      (Nat.lcm_comm d1 d2 ▸ h) hle

theorem upperMoebius_of_lambda_sq (weights : ℕ → ℝ) (hw : weights 1 = 1) :
    IsUpperMoebius <| lambdaSquared weights := by
  dsimp [IsUpperMoebius, lambdaSquared]
  intro n
  have h_sq :
    (∑ d ∈ n.divisors, ∑ d1 ∈ d.divisors, ∑ d2 ∈ d.divisors,
      if d = Nat.lcm d1 d2 then weights d1 * weights d2 else 0) =
      (∑ d ∈ n.divisors, weights d) ^ 2 := by
    rw [sq, mul_sum, conv_lambda_sq_larger_sum _ n, sum_comm]
    apply sum_congr rfl; intro d1 hd1
    rw [sum_mul, sum_comm]
    apply sum_congr rfl; intro d2 hd2
    rw [sum_ite_eq_of_mem']
    · ring
    rw [mem_divisors, Nat.lcm_dvd_iff]
    exact ⟨⟨dvd_of_mem_divisors hd1, dvd_of_mem_divisors hd2⟩, (mem_divisors.mp hd1).2⟩
  rw [h_sq]
  split_ifs with hn
  · rw [hn]; simp [hw]
  · apply sq_nonneg

-- set_option quotPrecheck false
-- variable (s : Sieve)

-- local notation3 "ν" => Sieve.nu s
-- local notation3 "P" => Sieve.prodPrimes s
-- local notation3 "a" => Sieve.weights s
-- local notation3 "X" => Sieve.totalMass s
-- local notation3 "R" => Sieve.rem s
-- local notation3 "g" => Sieve.selbergTerms s

theorem lambdaSquared_mainSum_eq_quad_form (w : ℕ → ℝ) :
    mainSum (s := s) (lambdaSquared w) =
      ∑ d1 ∈ divisors P, ∑ d2 ∈ divisors P,
        ν d1 * w d1 * ν d2 * w d2 * (ν (d1.gcd d2))⁻¹ := by
  dsimp only [mainSum, lambdaSquared]
  trans (∑ d ∈ divisors P, ∑ d1 ∈ divisors d, ∑ d2 ∈ divisors d,
          if d = d1.lcm d2 then w d1 * w d2 * ν d else 0)
  · rw [sum_congr rfl]; intro d _
    rw [sum_mul, sum_congr rfl]; intro d1 _
    rw [sum_mul, sum_congr rfl]; intro d2 _
    rw [ite_zero_mul]

  trans (∑ d ∈ divisors P, ∑ d1 ∈ divisors P, ∑ d2 ∈ divisors P,
          if d = d1.lcm d2 then w d1 * w d2 * ν d else 0)
  · apply conv_lambda_sq_larger_sum
  rw [sum_comm, sum_congr rfl]; intro d1 hd1
  rw [sum_comm, sum_congr rfl]; intro d2 hd2
  have h : d1.lcm d2 ∣ P :=
    Nat.lcm_dvd_iff.mpr ⟨dvd_of_mem_divisors hd1, dvd_of_mem_divisors hd2⟩
  rw [sum_ite_eq_of_mem' (divisors P) (d1.lcm d2) _ (mem_divisors.mpr ⟨h, prodPrimes_ne_zero⟩)]
  rw [s.nu_mult.map_lcm]
  · ring
  refine _root_.ne_of_gt (nu_pos_of_dvd_prodPrimes ?_)
  trans d1
  · exact Nat.gcd_dvd_left d1 d2
  · exact dvd_of_mem_divisors hd1

theorem lambdaSquared_mainSum_eq_diag_quad_form (w : ℕ → ℝ) :
    mainSum (s := s) (lambdaSquared w) =
      ∑ l ∈ divisors P,
        1 / g l * (∑ d ∈ divisors P, if l ∣ d then ν d * w d else 0) ^ 2 :=
  by
  rw [lambdaSquared_mainSum_eq_quad_form s w]
  trans (∑ d1 ∈ divisors P, ∑ d2 ∈ divisors P, (∑ l ∈ divisors P,
          if l ∣ d1.gcd d2 then 1 / g l * (ν d1 * w d1) * (ν d2 * w d2) else 0))
  · apply sum_congr rfl; intro d1 hd1; apply sum_congr rfl; intro d2 _
    have hgcd_dvd: d1.gcd d2 ∣ P := Trans.trans (Nat.gcd_dvd_left d1 d2) (dvd_of_mem_divisors hd1)
    rw [nu_eq_conv_one_div_selbergTerms s _ hgcd_dvd, mul_sum]
    apply sum_congr rfl; intro l _
    rw [mul_ite_zero]; apply if_congr Iff.rfl _ rfl
    ring
  trans (∑ l ∈ divisors P, ∑ d1 ∈ divisors P, ∑ d2 ∈ divisors P,
        if l ∣ Nat.gcd d1 d2 then 1 / selbergTerms s l * (ν d1 * w d1) * (ν d2 * w d2) else 0)
  · apply symm; rw [sum_comm, sum_congr rfl]; intro d1 _
    rw [sum_comm]
  apply sum_congr rfl; intro l _
  rw [sq, sum_mul, mul_sum, sum_congr rfl]; intro d1 _
  rw [mul_sum, mul_sum, sum_congr rfl]; intro d2 _
  rw [ite_zero_mul_ite_zero, mul_ite_zero]
  apply if_congr (Nat.dvd_gcd_iff) _ rfl;
  ring

end LambdaSquared

end SelbergSieve

/-! ### Vendored from PrimeNumberTheoremAnd/Mathlib/NumberTheory/Sieve/Selberg.lean -/
/-
Copyright (c) 2023 Arend Mellendijk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Arend Mellendijk

! This file was ported from Lean 3 source module selberg
-/



/-!
# The Selberg Sieve

This file proves `selberg_bound_simple`, the main theorem of the Selberg.
-/

set_option lang.lemmaCmd true

noncomputable section

open scoped BigOperators Classical SelbergSieve ArithmeticFunction.Moebius ArithmeticFunction.omega

open Finset Real Nat SelbergSieve.UpperBoundSieve ArithmeticFunction SelbergSieve BoundingSieve

namespace SelbergSieve
set_option quotPrecheck false

variable (s : SelbergSieve)
local notation3 "ν" => BoundingSieve.nu (self := SelbergSieve.toBoundingSieve (self := s))
local notation3 "P" => BoundingSieve.prodPrimes (self := SelbergSieve.toBoundingSieve (self := s))
local notation3 "a" => BoundingSieve.weights (self := SelbergSieve.toBoundingSieve (self := s))
local notation3 "X" => BoundingSieve.totalMass (self := SelbergSieve.toBoundingSieve (self := s))
local notation3 "A" => BoundingSieve.support (self := SelbergSieve.toBoundingSieve (self := s))
local notation3 "𝒜" => BoundingSieve.multSum (s := SelbergSieve.toBoundingSieve (self := s))
local notation3 "R" => BoundingSieve.rem (s := SelbergSieve.toBoundingSieve (self := s))
local notation3 "g" => SelbergSieve.selbergTerms (SelbergSieve.toBoundingSieve (self := s))
local notation3 "y" => SelbergSieve.level (self := s)
local notation3 "hy" => SelbergSieve.one_le_level (self := s)

@[simp]
def selbergBoundingSum : ℝ :=
  ∑ l ∈ divisors P, if l ^ 2 ≤ y then g l else 0

set_option quotPrecheck false
local notation3 "S" => SelbergSieve.selbergBoundingSum s

theorem selbergBoundingSum_pos :
    0 < S := by
  dsimp only [selbergBoundingSum]
  rw [← sum_filter]
  apply sum_pos;
  · intro l hl
    rw [mem_filter, mem_divisors] at hl
    · apply selbergTerms_pos _ _ (hl.1.1)
  · simp_rw [Finset.Nonempty, mem_filter]; use 1
    constructor
    · apply one_mem_divisors.mpr prodPrimes_ne_zero
    rw [cast_one, one_pow]
    exact s.one_le_level

theorem selbergBoundingSum_ne_zero : S ≠ 0 := by
  apply _root_.ne_of_gt
  exact s.selbergBoundingSum_pos

theorem selbergBoundingSum_nonneg : 0 ≤ S := _root_.le_of_lt s.selbergBoundingSum_pos

def selbergWeights : ℕ → ℝ := fun d =>
  if d ∣ P then
    (ν d)⁻¹ * g d * μ d * S⁻¹ *
      ∑ m ∈ divisors P, if (d * m) ^ 2 ≤ y ∧ m.Coprime d then g m else 0
  else 0

-- This notation traditionally uses λ, which is unavailable in lean
set_option quotPrecheck false
local notation3 "γ" => SelbergSieve.selbergWeights s

theorem selbergWeights_eq_zero_of_not_dvd {d : ℕ} (hd : ¬ d ∣ P) :
    γ d = 0 := by
  rw [selbergWeights, if_neg hd]

theorem selbergWeights_eq_zero (d : ℕ) (hd : ¬d ^ 2 ≤ y) :
    γ d = 0 := by
  dsimp only [selbergWeights]
  split_ifs with h
  · rw [mul_eq_zero_of_right _]
    apply Finset.sum_eq_zero
    refine fun m hm => if_neg ?_
    intro hyp
    have : (d^2:ℝ) ≤ (d*m)^2 := by
      norm_cast;
      refine Nat.pow_le_pow_left ?h 2
      exact Nat.le_mul_of_pos_right _ (Nat.pos_of_mem_divisors hm)
    linarith [hyp.1]
  · rfl

@[aesop safe]
theorem selbergWeights_mul_mu_nonneg (d : ℕ) (hdP : d ∣ P) :
    0 ≤ γ d * μ d := by
  dsimp only [selbergWeights]
  rw [if_pos hdP, mul_assoc]
  trans ((μ d :ℝ)^2 * (ν d)⁻¹ * g d * S⁻¹ * ∑ m ∈ divisors P,
          if (d * m) ^ 2 ≤ y ∧ Coprime m d then g m else 0)
  swap
  · apply le_of_eq; ring
  refine mul_nonneg (div_nonneg (mul_nonneg (mul_nonneg ?_ ?_) ?_) ?_) ?_
  · apply sq_nonneg
  · rw [inv_nonneg]
    exact le_of_lt <| nu_pos_of_dvd_prodPrimes hdP
  · exact le_of_lt <| selbergTerms_pos _ d hdP
  · exact s.selbergBoundingSum_nonneg
  apply sum_nonneg; intro m hm
  split_ifs with h
  · exact le_of_lt <| selbergTerms_pos _ m (dvd_of_mem_divisors hm)
  · rfl

lemma sum_mul_subst (k n : ℕ) {f : ℕ → ℝ} (h : ∀ l, l ∣ n → ¬ k ∣ l → f l = 0) :
      ∑ l ∈ n.divisors, f l
    = ∑ m ∈ n.divisors, if k*m ∣ n then f (k*m) else 0 := by
  by_cases hn: n = 0
  · simp [hn]
  by_cases hkn : k ∣ n
  swap
  · rw [sum_eq_zero, sum_eq_zero]
    · rintro m _
      rw [if_neg]
      rintro h
      apply hkn
      exact (Nat.dvd_mul_right k m).trans h
    · intro l hl; apply h l (dvd_of_mem_divisors hl)
      apply fun hkl => hkn <| hkl.trans (dvd_of_mem_divisors hl)
  trans (∑ l ∈ n.divisors, ∑ m ∈ n.divisors, if l=k*m then f l else 0)
  · rw [sum_congr rfl]; intro l hl
    by_cases hkl : k ∣ l
    swap
    · rw [h l (dvd_of_mem_divisors hl) hkl, sum_eq_zero];
      intro m _; rw [ite_id]
    rw [sum_eq_single (l/k)]
    · rw[if_pos]; rw [Nat.mul_div_cancel' hkl]
    · intro m _ hmlk
      apply if_neg; revert hmlk; contrapose!; intro hlkm
      rw [hlkm, mul_comm, Nat.mul_div_cancel];
      apply Nat.pos_of_dvd_of_pos hkn (Nat.pos_of_ne_zero hn)
    · contrapose!; intro _
      rw [mem_divisors]
      exact ⟨Trans.trans (Nat.div_dvd_of_dvd hkl) (dvd_of_mem_divisors hl), hn⟩
  · rw [sum_comm, sum_congr rfl]; intro m _
    split_ifs with hdvd
    · rw [sum_ite_eq_of_mem']
      simp only [mem_divisors, hdvd, ne_eq, hn, not_false_eq_true, and_self]
    · apply sum_eq_zero; intro l hl
      apply if_neg;
      rintro rfl
      simp only [mem_divisors, ne_eq] at hl
      exact hdvd hl.1

--Important facts about the selberg weights
theorem selbergWeights_eq_dvds_sum (d : ℕ) :
    ν d * γ d =
      S⁻¹ * μ d *
        ∑ l ∈ divisors P, if d ∣ l ∧ l ^ 2 ≤ y then g l else 0 := by
  by_cases h_dvd : d ∣ P
  swap
  · dsimp only [selbergWeights]; rw [if_neg h_dvd]
    rw [sum_eq_zero]
    · ring
    intro l hl; rw [mem_divisors] at hl
    rw [if_neg]; push Not; intro h
    exfalso; exact h_dvd (dvd_trans h hl.left)
  dsimp only [selbergWeights]
  rw [if_pos h_dvd]
  repeat rw [mul_sum]
  -- change of variables l=m*d
  apply symm
  rw [sum_mul_subst d P]
  · apply sum_congr rfl
    intro m hm
    rw [mul_ite_zero, ←ite_and, mul_ite_zero, mul_ite_zero]
    apply if_ctx_congr _ _ fun _ => rfl
    · rw [coprime_comm]
      constructor
      · intro h
        push_cast at h
        exact ⟨h.2.2, coprime_of_squarefree_mul
          <| Squarefree.squarefree_of_dvd h.1 s.prodPrimes_squarefree⟩
      · intro h
        push_cast
        exact ⟨ Coprime.mul_dvd_of_dvd_of_dvd h.2 h_dvd (dvd_of_mem_divisors hm),
          Nat.dvd_mul_right d m, h.1⟩
    · intro h
      trans ((ν d)⁻¹ * (ν d) * g d * μ d / S * g m)
      · rw [inv_mul_cancel₀ (nu_ne_zero h_dvd),
          (selbergTerms_mult _).map_mul_of_coprime <| coprime_comm.mp h.2]
        ring
      ring
  · intro l _ hdl
    rw [if_neg, mul_zero]
    push Not; intro h; contradiction

theorem selbergWeights_diagonalisation (l : ℕ) (hl : l ∈ divisors P) :
    (∑ d ∈ divisors P, if l ∣ d then ν d * γ d else 0) =
      if l ^ 2 ≤ y then g l * μ l * S⁻¹ else 0 := by
  calc
    (∑ d ∈ divisors P, if l ∣ d then ν d * γ d else 0) =
        ∑ d ∈ divisors P, ∑ k ∈ divisors P,
          if l ∣ d ∧ d ∣ k ∧ k ^ 2 ≤ y then g k * S⁻¹ * (μ d:ℝ) else 0 := by
      apply sum_congr rfl; intro d _
      rw [selbergWeights_eq_dvds_sum, ← boole_mul, mul_sum, mul_sum]
      apply sum_congr rfl; intro k _
      rw [mul_ite_zero, ite_zero_mul_ite_zero]
      apply if_ctx_congr Iff.rfl _ (fun _ => rfl);
      intro _; ring
    _ = ∑ k ∈ divisors P, if k ^ 2 ≤ y then
            (∑ d ∈ divisors P, if l ∣ d ∧ d ∣ k then (μ d:ℝ) else 0) * g k * S⁻¹
          else 0 := by
      rw [sum_comm]; apply sum_congr rfl; intro k _
      apply symm
      rw [← boole_mul, sum_mul, sum_mul, mul_sum, sum_congr rfl]
      intro d _
      rw [ite_zero_mul, ite_zero_mul, ite_zero_mul, one_mul, ←ite_and]
      apply if_ctx_congr _ _ (fun _ => rfl)
      · tauto
      intro _; ring
    _ = if l ^ 2 ≤ y then g l * μ l * S⁻¹ else 0 := by
      rw [← sum_ite_eq_of_mem' (divisors P) l (fun _ => if l^2 ≤ y then g l * μ l * S⁻¹ else 0) hl]
      apply sum_congr rfl; intro k hk
      rw [Aux.moebius_inv_dvd_lower_bound_real s.prodPrimes_squarefree l _ (dvd_of_mem_divisors hk),
        ←ite_and, ite_zero_mul, ite_zero_mul, ← ite_and]
      apply if_ctx_congr _ _ fun _ => rfl
      · rw [and_comm, eq_comm]; apply and_congr_right
        intro heq; rw [heq]
      · intro h; rw [h.1]; ring

def selbergMuPlus : ℕ → ℝ :=
  lambdaSquared γ

set_option quotPrecheck false
local notation3 "μ⁺" => SelbergSieve.selbergMuPlus s

theorem weight_one_of_selberg : γ 1 = 1 := by
  dsimp only [selbergWeights]
  rw [if_pos (one_dvd P), s.nu_mult.left, (selbergTerms_mult _).map_one]
  simp only [inv_one, mul_one, isUnit_one, IsUnit.squarefree, moebius_apply_of_squarefree,
    cardFactors_one, _root_.pow_zero, Int.cast_one, selbergBoundingSum, one_mul,
    coprime_one_right_eq_true, and_true, cast_one]
  rw [inv_mul_cancel₀]
  convert! s.selbergBoundingSum_ne_zero

theorem selbergμPlus_eq_zero (d : ℕ) (hd : ¬d ≤ y) : μ⁺ d = 0 := by
  apply lambdaSquared_eq_zero_of_support _ y _ d hd
  apply s.selbergWeights_eq_zero

def selbergUbSieve : UpperBoundSieve :=
  ⟨μ⁺, upperMoebius_of_lambda_sq γ (s.weight_one_of_selberg)⟩

-- proved for general lambda squared sieves
theorem mainSum_eq_diag_quad_form :
    mainSum (s := s.toBoundingSieve) μ⁺ =
      ∑ l ∈ divisors P,
        1 / g l *
          (∑ d ∈ divisors P, if l ∣ d then ν d * γ d else 0) ^ 2 :=
  by apply lambdaSquared_mainSum_eq_diag_quad_form

theorem selberg_bound_simple_mainSum :
    mainSum (s := s.toBoundingSieve) μ⁺ = S⁻¹ := by
  rw [mainSum_eq_diag_quad_form]
  trans (∑ l ∈ divisors P, (if l ^ 2 ≤ y then g l * (S⁻¹) ^ 2 else 0))
  · apply sum_congr rfl; intro l hl
    rw [s.selbergWeights_diagonalisation l hl, ite_pow, zero_pow two_ne_zero, mul_ite_zero]
    apply if_congr Iff.rfl _ rfl
    trans (1/g l * g l * g l * (μ l:ℝ)^2  * (S⁻¹) ^ 2)
    · ring
    norm_cast; rw [moebius_sq_eq_one_of_squarefree <| squarefree_of_mem_divisors_prodPrimes hl]
    rw [one_div_mul_cancel <| _root_.ne_of_gt <| selbergTerms_pos _ l <| dvd_of_mem_divisors hl]
    ring
  conv => {lhs; congr; {skip}; {ext i; rw [← ite_zero_mul]}}
  dsimp only [selbergBoundingSum]
  rw [←sum_mul, sq, ←mul_assoc, mul_inv_cancel₀]
  · ring
  · apply _root_.ne_of_gt; apply selbergBoundingSum_pos

lemma eq_gcd_mul_of_dvd_of_coprime {k d m : ℕ} (hkd : k ∣ d) (hmd : Coprime m d) (hk : k ≠ 0) :
    k = d.gcd (k*m) := by
  obtain ⟨r, hr⟩ := hkd
  have hrdvd : r ∣ d := by use k; rw [mul_comm]; exact hr
  apply symm; rw [hr, Nat.gcd_mul_left, mul_eq_left₀ hk, Nat.gcd_comm]
  apply Coprime.coprime_dvd_right hrdvd hmd

private lemma _helper {k m d : ℕ} (hkd : k ∣ d) (hk : k ∈ divisors P) (hm : m ∈ divisors P) :
    k * m ∣ P ∧ k = Nat.gcd d (k * m) ∧ (k * m) ^ 2 ≤ y ↔
    (k * m) ^ 2 ≤ y ∧ Coprime m d := by
  constructor
  · intro h
    constructor
    · exact h.2.2
    · obtain ⟨r, hr⟩ := hkd
      rw [hr, Nat.gcd_mul_left, eq_comm, mul_eq_left₀ (by rintro rfl; simp at hk ⊢)] at h
      rw [hr, coprime_comm]; apply Coprime.mul_left
      · apply coprime_of_squarefree_mul <| Squarefree.squarefree_of_dvd h.1 s.prodPrimes_squarefree
      · exact h.2.1
  · intro h
    constructor
    · apply Nat.Coprime.mul_dvd_of_dvd_of_dvd
      · rw [coprime_comm]; exact Coprime.coprime_dvd_right hkd h.2
      · exact dvd_of_mem_divisors hk
      · exact dvd_of_mem_divisors hm
    constructor
    · exact eq_gcd_mul_of_dvd_of_coprime hkd h.2 (by rintro rfl; simp at hk ⊢)
    · exact h.1

theorem selbergBoundingSum_ge {d : ℕ} (hdP : d ∣ P) :
    S ≥ γ d * ↑(μ d) * S := by
  calc
  _ = (∑ k ∈ divisors P, ∑ l ∈ divisors P, if k = d.gcd l ∧ l ^ 2 ≤ y then g l else 0) := by
    dsimp only [selbergBoundingSum]
    rw [sum_comm, sum_congr rfl]; intro l _
    simp_rw [ite_and]
    rw [sum_ite_eq_of_mem']
    · rw [mem_divisors]
      exact ⟨(Nat.gcd_dvd_left d l).trans (hdP), prodPrimes_ne_zero⟩
  _ = (∑ k ∈ divisors P,
          if k ∣ d then
            g k * ∑ m ∈ divisors P, if (k * m) ^ 2 ≤ y ∧ m.Coprime d then g m else 0
          else 0) := by
    apply sum_congr rfl; intro k hk
    rw [mul_sum]
    split_ifs with hkd
    swap
    · rw [sum_eq_zero]; intro l _
      rw [if_neg]
      push Not; intro h; exfalso
      rw [h] at hkd
      exact hkd <| Nat.gcd_dvd_left d l
    rw [sum_mul_subst k P, sum_congr rfl]
    · intro m hm
      rw [mul_ite_zero, ← ite_and]
      apply if_ctx_congr _ _ fun _ => rfl
      · exact_mod_cast s._helper hkd hk hm
      · intro h
        apply (selbergTerms_mult _).map_mul_of_coprime
        rw [gcd_comm]; apply h.2.coprime_dvd_right hkd
    · intro l _ hkl; apply if_neg
      push Not; intro h; exfalso
      rw [h] at hkl; exact hkl (Nat.gcd_dvd_right d l)
  _ ≥ (∑ k ∈ divisors P, if k ∣ d
          then g k * ∑ m ∈ divisors P, if (d * m) ^ 2 ≤ y ∧ m.Coprime d then g m else 0
          else 0 ) := by
    apply sum_le_sum; intro k _
    split_ifs with hkd
    swap
    · rfl
    apply mul_le_mul le_rfl _ _ (le_of_lt <| selbergTerms_pos _ k <| hkd.trans hdP)
    · apply sum_le_sum; intro m hm
      split_ifs with h h' h'
      · rfl
      · exfalso; apply h'
        refine ⟨?_, h.2⟩
        · trans ((d*m)^2:ℝ)
          · norm_cast; gcongr
            refine Nat.le_of_dvd ?_ hkd
            apply Nat.pos_of_ne_zero; apply ne_zero_of_dvd_ne_zero prodPrimes_ne_zero hdP
          exact h.1
      · refine le_of_lt <| selbergTerms_pos _ m <| dvd_of_mem_divisors hm
      · rfl
    apply sum_nonneg; intro m hm
    split_ifs
    · apply le_of_lt <| selbergTerms_pos _ m <| dvd_of_mem_divisors hm
    · rfl
  _ = _ := by
    conv => enter [1, 2, k]; rw [← ite_zero_mul]
    rw [←sum_mul, conv_selbergTerms_eq_selbergTerms_mul_nu _ hdP]
    trans (S * S⁻¹ * (μ d:ℝ)^2 * (ν d)⁻¹ * g d * (∑ m ∈ divisors P, if (d*m) ^ 2 ≤ y ∧
      Coprime m d then g m else 0))
    · rw [mul_inv_cancel₀, ←Int.cast_pow, moebius_sq_eq_one_of_squarefree]
      · ring
      · exact Squarefree.squarefree_of_dvd hdP s.prodPrimes_squarefree
      · exact _root_.ne_of_gt <| s.selbergBoundingSum_pos
    dsimp only [selbergWeights]; rw [if_pos hdP]
    ring

theorem selberg_bound_weights (d : ℕ) : |γ d| ≤ 1 := by
  by_cases hdP : d ∣ P
  swap
  · rw [s.selbergWeights_eq_zero_of_not_dvd hdP]; simp only [zero_le_one, abs_zero]
  have : 1*S ≥ γ d * ↑(μ d) * S := by
    rw[one_mul]
    exact s.selbergBoundingSum_ge hdP
  replace this : γ d * μ d ≤ 1 := by
    apply le_of_mul_le_mul_of_pos_right this (s.selbergBoundingSum_pos)
  convert this using 1
  rw [← abs_of_nonneg <| s.selbergWeights_mul_mu_nonneg d hdP,
    abs_mul, ←Int.cast_abs, abs_moebius_eq_one_of_squarefree <|
    (s.prodPrimes_squarefree.squarefree_of_dvd hdP), Int.cast_one, mul_one]


theorem selberg_bound_muPlus (n : ℕ) (hn : n ∈ divisors P) :
    |μ⁺ n| ≤ (3:ℝ) ^ ω n := by
  let f : ℕ → ℕ → ℝ := fun x z : ℕ => if n = x.lcm z then 1 else 0
  dsimp only [selbergMuPlus, lambdaSquared]
  calc
    |∑ d1 ∈ n.divisors, ∑ d2 ∈ n.divisors, if n = d1.lcm d2 then γ d1 * γ d2 else 0| ≤
        ∑ d1 ∈ n.divisors, |∑ d2 ∈ n.divisors, if n = d1.lcm d2 then γ d1 * γ d2 else 0| := ?_
    _ ≤ ∑ d1 ∈ n.divisors, ∑ d2 ∈ n.divisors, |if n = d1.lcm d2 then γ d1 * γ d2 else 0| := ?_
    _ ≤ ∑ d1 ∈ n.divisors, ∑ d2 ∈ n.divisors, f d1 d2 := ?_
    _ = (n.divisors ×ˢ n.divisors).sum fun p => f p.fst p.snd := ?_
    _ = Finset.card ((n.divisors ×ˢ n.divisors).filter fun p : ℕ × ℕ => n = p.fst.lcm p.snd) := ?_
    _ = (3:ℕ) ^ ω n := ?_
    _ = (3:ℝ) ^ ω n := ?_
  · apply abs_sum_le_sum_abs
  · gcongr; apply abs_sum_le_sum_abs
  · gcongr with d1 _ d2
    rw [apply_ite abs, abs_zero, abs_mul]
    simp only [f]
    by_cases h : n = d1.lcm d2
    · rw [if_pos h, if_pos h]
      apply mul_le_one₀ (s.selberg_bound_weights d1) (abs_nonneg <| γ d2)
        (s.selberg_bound_weights d2)
    rw [if_neg h, if_neg h]
  · rw [← Finset.sum_product']
  · rw [← sum_filter, Finset.sum_const, smul_one_eq_cast]
  · norm_cast
    simp [← card_pair_lcm_eq (squarefree_of_mem_divisors_prodPrimes hn), eq_comm]
  norm_num

theorem selberg_bound_simple_errSum :
    errSum (s := s.toBoundingSieve) μ⁺ ≤
      ∑ d ∈ divisors P, if (d : ℝ) ≤ y then (3:ℝ) ^ ω d * |R d| else 0 := by
  dsimp only [errSum]
  gcongr with d hd
  split_ifs with h
  · apply mul_le_mul _ le_rfl (abs_nonneg <| R d) (pow_nonneg _ <| ω d)
    · apply s.selberg_bound_muPlus d hd
    · norm_num
  · rw [s.selbergμPlus_eq_zero d h, abs_zero, zero_mul]

theorem selberg_bound_simple :
    siftedSum (s := s.toBoundingSieve) ≤
      X / S +
        ∑ d ∈ divisors P, if (d : ℝ) ≤ y then (3:ℝ) ^ ω d * |R d| else 0 := by
  let μPlus := s.selbergUbSieve
  calc
    siftedSum ≤ X * mainSum μPlus + errSum μPlus :=
      siftedSum_le_mainSum_errSum_of_UpperBoundSieve _ μPlus
    _ ≤ _ := ?_
  gcongr
  · erw [s.selberg_bound_simple_mainSum, div_eq_mul_inv]
  · apply s.selberg_bound_simple_errSum

end SelbergSieve

/-! ### Vendored from PrimeNumberTheoremAnd/Mathlib/NumberTheory/Sieve/SelbergBounds.lean -/
/-
Copyright (c) 2023 Arend Mellendijk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Arend Mellendijk
-/





/-!
# Bounds for the Selberg sieve
This file proves a number of results to help bound `Sieve.selbergSum`

## Main Results
* `selbergBoundingSum_ge_sum_div`: If `ν` is completely multiplicative then `S ≥ ∑_{n ≤ √y}, ν n`
* `boundingSum_ge_log`: If `ν n = 1 / n` then `S ≥ log y / 2`
* `rem_sum_le_of_const`: If `R_d ≤ C` then the error term is at most `C * y * (1 + log y)^3`
-/

set_option lang.lemmaCmd true

open scoped Nat ArithmeticFunction BigOperators Classical ArithmeticFunction.zeta
  ArithmeticFunction.omega
open BoundingSieve SelbergSieve

noncomputable section
namespace Sieve

lemma prodDistinctPrimes_squarefree (s : Finset ℕ) (h : ∀ p ∈ s, p.Prime) :
    Squarefree (∏ p ∈ s, p) := by
  refine Iff.mpr Nat.squarefree_iff_prime_squarefree ?_
  intro p hp; by_contra h_dvd
  by_cases hps : p ∈ s
  · rw [←Finset.mul_prod_erase (a:=p) (h := hps), mul_dvd_mul_iff_left (Nat.Prime.ne_zero hp)]
      at h_dvd
    obtain ⟨q, hq⟩ := hp.prime.exists_mem_finset_dvd h_dvd
    rw [Finset.mem_erase] at hq
    exact hq.1.1 <| symm <| (Nat.prime_dvd_prime_iff_eq hp (h q hq.1.2)).mp hq.2
  · have : p ∣ ∏ p ∈ s, p := Trans.trans (dvd_mul_right p p) h_dvd
    obtain ⟨q, hq⟩ := hp.prime.exists_mem_finset_dvd this
    have heq : p = q := by
      rw [←Nat.prime_dvd_prime_iff_eq hp (h q hq.1)]
      exact hq.2
    rw [heq] at hps; exact hps hq.1

lemma primorial_squarefree (n : ℕ) : Squarefree (primorial n) := by
  apply prodDistinctPrimes_squarefree
  simp_rw [Finset.mem_filter];
  exact fun _ h => h.2

theorem zeta_pos_of_prime : ∀ (p : ℕ), Nat.Prime p → (0:ℝ) < (↑ζ:ArithmeticFunction ℝ) p := by
  intro p hp
  rw [ArithmeticFunction.natCoe_apply, ArithmeticFunction.zeta_apply, if_neg (Nat.Prime.ne_zero hp)]
  norm_num

theorem zeta_lt_self_of_prime : ∀ (p : ℕ), Nat.Prime p → (↑ζ:ArithmeticFunction ℝ) p < (p:ℝ) := by
  intro p hp
  rw [ArithmeticFunction.natCoe_apply, ArithmeticFunction.zeta_apply, if_neg (Nat.Prime.ne_zero hp)]
  norm_num;
  exact Nat.succ_le_iff.mp (Nat.Prime.two_le hp)

theorem prime_dvd_primorial_iff (n p : ℕ) (hp : p.Prime) :
    p ∣ primorial n ↔ p ≤ n := by
  unfold primorial
  constructor
  · intro h
    obtain ⟨q, hq⟩ : ∃ i, i ∈ Finset.filter Nat.Prime (Finset.range (n + 1)) ∧ p ∣ i :=
      hp.prime.exists_mem_finset_dvd h
    rw [Finset.mem_filter, Finset.mem_range] at hq
    rw [prime_dvd_prime_iff_eq (Nat.Prime.prime hp) (Nat.Prime.prime hq.1.2)] at hq
    rw [hq.2]
    exact Nat.lt_succ_iff.mp hq.1.1
  · intro h
    apply Finset.dvd_prod_of_mem
    rw [Finset.mem_filter, Finset.mem_range]
    exact ⟨Nat.lt_succ_iff.mpr h, hp⟩

theorem siftedSum_eq (s : SelbergSieve) (hw : ∀ i ∈ s.support, s.weights i = 1) (z : ℝ)
    (hz : 1 ≤ z) (hP : s.prodPrimes = primorial (Nat.floor z)) :
    siftedSum (s := s.toBoundingSieve) =
    (s.support.filter (fun d => ∀ p:ℕ, p.Prime → p ≤ z → ¬p ∣ d)).card := by
  dsimp only [siftedSum]
  rw [Finset.card_eq_sum_ones, ←Finset.sum_filter, Nat.cast_sum]
  apply Finset.sum_congr
  · rw [hP]
    ext d; constructor
    · intro hd
      rw [Finset.mem_filter] at *
      constructor
      · exact hd.1
      · intro p hpp hpy
        rw [←Nat.Prime.coprime_iff_not_dvd hpp]
        apply Nat.Coprime.coprime_dvd_left _ hd.2
        rw [prime_dvd_primorial_iff _ _ hpp]
        apply Nat.le_floor hpy
    · intro h
      rw [Finset.mem_filter] at *
      constructor
      · exact h.1
      refine Nat.coprime_of_dvd ?_
      intro p hp
      erw [prime_dvd_primorial_iff _ _ hp]
      intro hpy
      apply h.2 p hp
      trans ↑(Nat.floor z)
      · norm_cast
      · apply Nat.floor_le
        linarith only [hz]
  simp_rw [Nat.cast_one]
  intro x hx
  simp only [Finset.mem_filter] at hx
  apply hw x hx.1

def CompletelyMultiplicative (f : ArithmeticFunction ℝ) : Prop :=
  f 1 = 1 ∧ ∀ a b, f (a*b) = f a * f b

namespace CompletelyMultiplicative
open ArithmeticFunction
theorem zeta : CompletelyMultiplicative ζ := by
  unfold CompletelyMultiplicative
  simp_rw [ArithmeticFunction.natCoe_apply, ArithmeticFunction.zeta_apply, one_ne_zero, ite_false,
    mul_eq_zero, Nat.cast_ite, Nat.cast_one, CharP.cast_eq_zero, mul_ite, mul_zero, mul_one,
    true_and, ← ite_or, or_comm, implies_true]

theorem id : CompletelyMultiplicative ArithmeticFunction.id := by
    constructor <;> simp

theorem pmul (f g : ArithmeticFunction ℝ) (hf : CompletelyMultiplicative f)
    (hg : CompletelyMultiplicative g) :
    CompletelyMultiplicative (ArithmeticFunction.pmul f g) := by
  constructor
  · rw [pmul_apply, hf.1, hg.1, mul_one]
  intro a b
  simp_rw [pmul_apply, hf.2, hg.2]; ring

theorem pdiv {f g : ArithmeticFunction ℝ} (hf : CompletelyMultiplicative f)
    (hg : CompletelyMultiplicative g) :
    CompletelyMultiplicative (ArithmeticFunction.pdiv f g) := by
  constructor
  · rw [pdiv_apply, hf.1, hg.1, div_one]
  intro a b
  simp_rw [pdiv_apply, hf.2, hg.2]; ring

theorem isMultiplicative {f : ArithmeticFunction ℝ} (hf : CompletelyMultiplicative f) :
    ArithmeticFunction.IsMultiplicative f :=
  ⟨hf.1, fun _ => hf.2 _ _⟩

theorem apply_pow (f : ArithmeticFunction ℝ) (hf : CompletelyMultiplicative f) (a n : ℕ) :
    f (a^n) = f a ^ n := by
  induction n with
  | zero => simp_rw [pow_zero, hf.1]
  | succ n' ih => simp_rw [pow_succ, hf.2, ih]

end CompletelyMultiplicative

theorem prod_factors_one_div_compMult_ge (M : ℕ) (f : ArithmeticFunction ℝ)
    (hf : CompletelyMultiplicative f) (hf_nonneg : ∀ n, 0 ≤ f n) (d : ℕ) (hd : Squarefree d)
    (hf_size : ∀ n, n.Prime → n ∣ d → f n < 1) :
    f d * ∏ p ∈ d.primeFactors, 1 / (1 - f p)
    ≥ ∏ p ∈ d.primeFactors, ∑ n ∈ Finset.Icc 1 M, f (p^n) := by
  calc f d * ∏ p ∈ d.primeFactors, 1 / (1 - f p)
    = ∏ p ∈ d.primeFactors, f p / (1 - f p)                 := by
        conv => { lhs; congr; rw [←Nat.prod_primeFactors_of_squarefree hd] }
        rw [hf.isMultiplicative.map_prod_of_subset_primeFactors _ _ subset_rfl,
          ←Finset.prod_mul_distrib]
        simp_rw[one_div, div_eq_mul_inv]
  _ ≥ ∏ p ∈ d.primeFactors, ∑ n ∈ Finset.Icc 1 M, (f p)^n  := by
    gcongr with p hp
    · exact fun p _ => Finset.sum_nonneg fun n _ => pow_nonneg (hf_nonneg p) n
    rw [Nat.mem_primeFactors_of_ne_zero hd.ne_zero] at hp
    rw [← Finset.Ico_add_one_right_eq_Icc, geom_sum_Ico,
      ← mul_div_mul_left (c := (-1 : ℝ)) (f p ^ (M + 1) - f p ^ 1)]
    · gcongr
      · apply hf_nonneg
      · linarith [hf_size p hp.1 hp.2]
      · rw [pow_one]
        have : 0 ≤ f p ^ (M + 1) := by
          apply pow_nonneg
          apply hf_nonneg
        linarith only [this]
      · linarith only
    · norm_num
    · apply ne_of_lt <| hf_size p hp.1 hp.2
    · apply Nat.succ_le_iff.mpr (Nat.succ_pos _)

  _ = ∏ p ∈ d.primeFactors, ∑ n ∈ Finset.Icc 1 M, f (p^n)  := by
     simp_rw [hf.apply_pow]

theorem prod_factors_sum_pow_compMult (M : ℕ) (hM : M ≠ 0) (f : ArithmeticFunction ℝ)
    (hf : CompletelyMultiplicative f) (d : ℕ) (hd : Squarefree d) :
    ∏ p ∈ d.primeFactors, ∑ n ∈ Finset.Icc 1 M, f (p^n)
    = ∑ m ∈ (d^M).divisors.filter (d ∣ ·), f m := by
  rw [Finset.prod_sum]
  let i : (a:_) → (ha : a ∈ Finset.pi d.primeFactors fun p => Finset.Icc 1 M) → ℕ :=
    fun a _ => ∏ p ∈ d.primeFactors.attach, p.1 ^ (a p p.2)
  have hfact_i : ∀ a ha,
      ∀ p , Nat.factorization (i a ha) p = if hp : p ∈ d.primeFactors then a p hp else 0 := by
    intro a ha p
    by_cases hp : p ∈ d.primeFactors
    · rw [dif_pos hp, Nat.factorization_prod, Finset.sum_apply',
        Finset.sum_eq_single ⟨p, hp⟩, Nat.factorization_pow, Finsupp.smul_apply,
        Nat.Prime.factorization_self (Nat.prime_of_mem_primeFactorsList <| List.mem_toFinset.mp hp)]
      · ring
      · intro q _ hq
        rw [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_zero]; right
        apply Nat.factorization_eq_zero_of_not_dvd
        rw [Nat.Prime.dvd_iff_eq, ← exists_eq_subtype_mk_iff]
        · push Not
          exact fun _ => hq
        · exact Nat.prime_of_mem_primeFactorsList <| List.mem_toFinset.mp q.2
        · exact (Nat.prime_of_mem_primeFactorsList <| List.mem_toFinset.mp hp).ne_one
      · intro h
        exfalso
        exact h (Finset.mem_attach _ _)
      · exact fun q _ => pow_ne_zero _ (_root_.ne_of_gt (Nat.pos_of_mem_primeFactorsList
          (List.mem_toFinset.mp q.2)))
    · rw [dif_neg hp]
      by_cases hpp : p.Prime
      swap
      · apply Nat.factorization_eq_zero_of_not_prime _ hpp
      apply Nat.factorization_eq_zero_of_not_dvd
      intro hp_dvd
      obtain ⟨⟨q, hq⟩, _, hp_dvd_pow⟩ := Prime.exists_mem_finset_dvd hpp.prime hp_dvd
      apply hp
      rw [Nat.mem_primeFactors]
      constructor
      · exact hpp
      refine ⟨?_, hd.ne_zero⟩
      trans q
      · apply Nat.Prime.dvd_of_dvd_pow hpp hp_dvd_pow
      · apply Nat.dvd_of_mem_primeFactorsList <| List.mem_toFinset.mp hq

  have hi_ne_zero : ∀ (a : _) (ha : a ∈ Finset.pi d.primeFactors fun _p => Finset.Icc 1 M),
      i a ha ≠ 0 := by
    intro a ha
    erw [Finset.prod_ne_zero_iff]
    exact fun p _ => pow_ne_zero _ (_root_.ne_of_gt (Nat.pos_of_mem_primeFactorsList
      (List.mem_toFinset.mp p.property)))
  have hi : ∀ (a : _) (ha : a ∈ Finset.pi d.primeFactors fun _p => Finset.Icc 1 M),
      i a ha ∈ (d^M).divisors.filter (d ∣ ·) := by
    intro a ha
    rw [Finset.mem_filter, Nat.mem_divisors, ←Nat.factorization_le_iff_dvd hd.ne_zero
      (hi_ne_zero a ha),← Nat.factorization_le_iff_dvd (hi_ne_zero a ha) (pow_ne_zero _ hd.ne_zero)]
    constructor; constructor
    · rw [Finsupp.le_iff]; intro p _
      rw [hfact_i a ha]
      by_cases hp : p ∈ d.primeFactors
      · rw [dif_pos hp]
        rw [Nat.factorization_pow, Finsupp.smul_apply]
        simp_rw [Finset.mem_pi, Finset.mem_Icc] at ha
        trans (M • 1)
        · norm_num
          exact (ha p hp).2
        · gcongr
          rw [Nat.mem_primeFactors_of_ne_zero hd.ne_zero] at hp
          rw [←Nat.Prime.dvd_iff_one_le_factorization hp.1 hd.ne_zero]
          exact hp.2
      · rw [dif_neg hp]; norm_num
    · apply pow_ne_zero _ hd.ne_zero
    · rw [Finsupp.le_iff]; intro p hp
      rw [Nat.support_factorization] at hp
      rw [hfact_i a ha]
      rw [dif_pos hp]
      trans 1
      · exact hd.natFactorization_le_one p
      simp_rw [Finset.mem_pi, Finset.mem_Icc] at ha
      exact (ha p hp).1

  have h : ∀ (a : _) (ha : a ∈ Finset.pi d.primeFactors fun _p => Finset.Icc 1 M),
      ∏ p ∈ d.primeFactors.attach, f (p.1 ^ (a p p.2)) = f (i a ha) := by
    intro a ha
    apply symm
    apply hf.isMultiplicative.map_prod
    intro x _ y _ hxy
    simp_rw [Finset.mem_pi, Finset.mem_Icc, Nat.succ_le_iff] at ha
    apply (Nat.coprime_pow_left_iff (ha x x.2).1 ..).mpr
    apply (Nat.coprime_pow_right_iff (ha y y.2).1 ..).mpr
    have hxp := Nat.prime_of_mem_primeFactorsList (List.mem_toFinset.mp x.2)
    rw [Nat.Prime.coprime_iff_not_dvd hxp]
    rw [Nat.prime_dvd_prime_iff_eq hxp <| Nat.prime_of_mem_primeFactorsList
      (List.mem_toFinset.mp y.2)]
    exact fun hc => hxy (Subtype.ext hc)

  have i_inj : ∀ a ha b hb, i a ha = i b hb → a = b := by
    intro a ha b hb hiab
    apply_fun Nat.factorization at hiab
    ext p hp
    obtain hiabp := DFunLike.ext_iff.mp hiab p
    rw [hfact_i a ha, hfact_i b hb, dif_pos hp, dif_pos hp] at hiabp
    exact hiabp

  have i_surj : ∀ (b : ℕ), b ∈ (d^M).divisors.filter (d ∣ ·) → ∃ a ha, i a ha = b := by
    intro b hb
    have h : (fun p _ => b.factorization p) ∈ Finset.pi d.primeFactors fun p => Finset.Icc 1 M := by
      rw [Finset.mem_pi]; intro p hp
      rw [Finset.mem_Icc]
      rw [Finset.mem_filter] at hb
      have hb_ne_zero : b ≠ 0 := _root_.ne_of_gt <| Nat.pos_of_mem_divisors hb.1
      have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
      constructor
      · rw [←Nat.Prime.dvd_iff_one_le_factorization hpp hb_ne_zero]
        · exact Trans.trans (Nat.dvd_of_mem_primeFactors hp) hb.2
      · rw [Nat.mem_divisors] at hb
        trans Nat.factorization (d^M) p
        · exact (Nat.factorization_le_iff_dvd hb_ne_zero hb.left.right).mpr hb.left.left p
        rw [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul]
        have : d.factorization p ≤ 1 := by
          apply hd.natFactorization_le_one
        exact (mul_le_iff_le_one_right (Nat.pos_of_ne_zero hM)).mpr this
    use (fun p _ => Nat.factorization b p)
    use h
    apply Nat.eq_of_factorization_eq
    · apply hi_ne_zero _ h
    · exact _root_.ne_of_gt <| Nat.pos_of_mem_divisors (Finset.mem_filter.mp hb).1
    intro p
    rw [hfact_i (fun p _ => (Nat.factorization b) p) h p]
    rw [Finset.mem_filter, Nat.mem_divisors] at hb
    by_cases hp : p ∈ d.primeFactors
    · rw [dif_pos hp]
    · rw [dif_neg hp, eq_comm, Nat.factorization_eq_zero_iff, ←or_assoc]
      rw [Nat.mem_primeFactors] at hp
      left
      push Not at hp
      by_cases hpp : p.Prime
      · right; intro h
        apply absurd (hp hpp)
        push Not
        exact ⟨hpp.dvd_of_dvd_pow (h.trans hb.1.1), hd.ne_zero⟩
      · left; exact hpp

  exact Finset.sum_bij i hi i_inj i_surj h

theorem prod_primes_dvd_of_dvd (P : ℕ) {s : Finset ℕ} (h : ∀ p ∈ s, p ∣ P) (h' : ∀ p ∈ s, p.Prime) :
    ∏ p ∈ s, p ∣ P := by
  simp_rw [Nat.prime_iff] at h'
  apply Finset.prod_primes_dvd _ h' h

lemma sqrt_le_self (x : ℝ) (hx : 1 ≤ x) : Real.sqrt x ≤ x := by
  refine Iff.mpr Real.sqrt_le_iff ?_
  constructor
  · linarith
  refine le_self_pow₀ hx ?right.h
  norm_num

lemma Nat.squarefree_dvd_pow (a b N : ℕ) (ha : Squarefree a) (hab : a ∣ b ^ N) : a ∣ b := by
  by_cases hN : N=0
  · rw [hN, pow_zero, Nat.dvd_one] at hab
    rw [hab]; simp
  rw [Squarefree.dvd_pow_iff_dvd ha hN] at hab
  exact hab

/-
Proposed generalisation :

theorem selbergBoundingSum_ge_sum_div (s : SelbergSieve)
    (hnu : CompletelyMultiplicative s.nuDivSelf) (hnu_nonneg : ∀ n, 0 ≤ s.nuDivSelf n)
    (hnu_lt : ∀ p, p.Prime → p ∣ s.prodPrimes → s.nuDivSelf p < 1):
    s.selbergBoundingSum ≥ ∑ m in
      (Finset.Icc 1 (Nat.floor <| Real.sqrt s.level)).filter (fun m => ∀ p, p.Prime → p ∣ m → p ∣ s.prodPrimes),
      s.nu m
-/

theorem selbergBoundingSum_ge_sum_div (s : SelbergSieve) (hP : ∀ p:ℕ, p.Prime → (p:ℝ) ≤ s.level → p ∣ s.prodPrimes)
  (hnu : CompletelyMultiplicative s.nu) (hnu_nonneg : ∀ n, 0 ≤ s.nu n) (hnu_lt : ∀ p, p.Prime → p ∣ s.prodPrimes → s.nu p < 1):
    s.selbergBoundingSum ≥ ∑ m ∈ Finset.Icc 1 (Nat.floor <| Real.sqrt s.level), s.nu m := by
  unfold selbergBoundingSum
  calc ∑ l ∈ s.prodPrimes.divisors, (if l ^ 2 ≤ s.level then selbergTerms _ l else 0)
     ≥ ∑ l ∈ s.prodPrimes.divisors.filter (fun (l:ℕ) => l^2 ≤ s.level),
        ∑ m ∈ (l^(Nat.floor s.level)).divisors.filter (l ∣ ·), s.nu m         := ?_
   _ ≥ ∑ m ∈ Finset.Icc 1 (Nat.floor <| Real.sqrt s.level), s.nu m           := ?_
  · rw [←Finset.sum_filter]; apply Finset.sum_le_sum; intro l hl
    rw [Finset.mem_filter, Nat.mem_divisors] at hl
    have hlsq : Squarefree l := Squarefree.squarefree_of_dvd hl.1.1 s.prodPrimes_squarefree
    trans (∏ p ∈ l.primeFactors, ∑ n ∈ Finset.Icc 1 (Nat.floor s.level), s.nu (p^n))
    · rw [prod_factors_sum_pow_compMult (Nat.floor s.level) _ s.nu]
      · exact hnu
      · exact hlsq
      · rw [ne_eq, Nat.floor_eq_zero, not_lt]
        exact s.one_le_level
    rw [selbergTerms_apply _ l]
    apply prod_factors_one_div_compMult_ge _ _ hnu _ _ hlsq
    · intro p hpp hpl
      apply hnu_lt p hpp (Trans.trans hpl hl.1.1)
    · exact hnu_nonneg

  rw [←Finset.sum_biUnion]
  · apply Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => hnu_nonneg _)
    intro m hm
    have hprod_pos : 0 < (∏ p ∈ m.primeFactors, p) := by
      apply Finset.prod_pos;
      intro p hp; exact Nat.pos_of_mem_primeFactorsList <| List.mem_toFinset.mp hp
    have hprod_ne_zero :  (∏ p ∈ m.primeFactors, p) ^ ⌊s.level⌋₊ ≠ 0 := by
      apply pow_ne_zero; apply _root_.ne_of_gt; apply hprod_pos
    rw [Finset.mem_biUnion]; simp_rw [Finset.mem_filter, Nat.mem_divisors]
    rw [Finset.mem_Icc, Nat.le_floor_iff] at hm
    · have hm_ne_zero : m ≠ 0 := by
        exact _root_.ne_of_gt <| Nat.succ_le_iff.mp hm.1
      use ∏ p ∈ m.primeFactors, p
      constructor; constructor; constructor
      · apply prod_primes_dvd_of_dvd <;> intro p hp
        · apply hP p <| Nat.prime_of_mem_primeFactors hp
          trans (m:ℝ)
          · exact_mod_cast Nat.le_of_mem_primeFactors hp
          trans (Real.sqrt s.level)
          · exact hm.2
          apply sqrt_le_self s.level s.one_le_level
        exact Nat.prime_of_mem_primeFactors hp
      · exact prodPrimes_ne_zero
      · rw [←Real.sqrt_le_sqrt_iff (by linarith only [s.one_le_level]), Real.sqrt_sq]
        · trans (m:ℝ)
          · norm_cast; apply Nat.le_of_dvd (Nat.succ_le_iff.mp hm.1)
            exact Nat.prod_primeFactors_dvd m
          exact hm.2
        apply le_of_lt; norm_cast
      constructor; constructor
      · rw [←Nat.factorization_le_iff_dvd _ hprod_ne_zero, Nat.factorization_pow]
        · intro p
          have hy_mul_prod_nonneg : 0 ≤ ⌊s.level⌋₊ * (Nat.factorization (∏ p ∈ m.primeFactors, p)) p := by
            apply mul_nonneg
            · apply Nat.le_floor; norm_cast; linarith only [s.one_le_level]
            · norm_num
          trans (Nat.factorization m) p * 1
          · rw [mul_one]
          rw [Finsupp.smul_apply, smul_eq_mul]
          by_cases hpp : p.Prime
          swap
          · rw [Nat.factorization_eq_zero_of_not_prime _ hpp, zero_mul]; exact hy_mul_prod_nonneg
          by_cases hpdvd : p ∣ m
          swap
          · rw [Nat.factorization_eq_zero_of_not_dvd hpdvd, zero_mul]; exact hy_mul_prod_nonneg
          apply mul_le_mul
          · trans m
            · apply le_of_lt <| Nat.factorization_lt _ _
              apply hm_ne_zero
            apply Nat.le_floor
            refine le_trans hm.2 ?_
            apply sqrt_le_self _ s.one_le_level
          · rw [←Nat.Prime.pow_dvd_iff_le_factorization hpp <| _root_.ne_of_gt hprod_pos, pow_one]
            apply Finset.dvd_prod_of_mem
            rw [Nat.mem_primeFactors]
            exact ⟨hpp, hpdvd, hm_ne_zero⟩
          · norm_num
          · norm_num
        exact hm_ne_zero
      · exact hprod_ne_zero
      · exact Nat.prod_primeFactors_dvd m
    · apply Real.sqrt_nonneg
  · intro i hi j hj hij t hti htj x hx
    simp only [Finset.bot_eq_empty, Finset.notMem_empty]
    specialize hti hx
    specialize htj hx
    simp_rw [Finset.mem_coe, Finset.mem_filter, Nat.mem_divisors] at *
    have h : ∀ i j {n}, i ∣ s.prodPrimes → i ∣ x → x ∣ j ^ n → i ∣ j := by
      intro i j n hiP hix hij
      apply Nat.squarefree_dvd_pow i j n (squarefree_of_dvd_prodPrimes hiP)
      exact Trans.trans hix hij
    have hidvdj : i ∣ j := by
      apply h i j hi.1.1 hti.2 htj.1.1
    have hjdvdi : j ∣ i := by
      apply h j i hj.1.1 htj.2 hti.1.1
    exact hij <| Nat.dvd_antisymm hidvdj hjdvdi

theorem boundingSum_ge_sum (s : SelbergSieve) (hnu : s.nu = (ζ : ArithmeticFunction ℝ).pdiv .id)
  (hP : ∀ p:ℕ, p.Prime → (p:ℝ) ≤ s.level → p ∣ s.prodPrimes) :
    s.selbergBoundingSum ≥ ∑ m ∈ Finset.Icc 1 (Nat.floor <| Real.sqrt s.level), 1 / (m:ℝ) := by
  trans ∑ m ∈ Finset.Icc 1 (Nat.floor <| Real.sqrt s.level), (ζ : ArithmeticFunction ℝ).pdiv .id m
  · rw[←hnu]
    apply selbergBoundingSum_ge_sum_div
    · intro p hpp hple
      apply hP p hpp hple
    · rw[hnu]
      exact CompletelyMultiplicative.zeta.pdiv CompletelyMultiplicative.id
    · intro n
      rw[hnu]
      apply div_nonneg
      · by_cases h : n = 0 <;> simp[h]
      simp
    · intro p hpp _
      rw[hnu]
      simp only [ArithmeticFunction.pdiv_apply, ArithmeticFunction.natCoe_apply,
        ArithmeticFunction.zeta_apply, Nat.cast_ite, CharP.cast_eq_zero, Nat.cast_one,
        ArithmeticFunction.id_apply]
      rw [if_neg, one_div]
      · apply inv_lt_one_of_one_lt₀; norm_cast
        exact hpp.one_lt
      exact hpp.ne_zero
  apply le_of_eq
  apply Finset.sum_congr rfl
  intro m hm
  rw [Finset.mem_Icc] at hm
  simp only [one_div, ArithmeticFunction.pdiv_apply, ArithmeticFunction.natCoe_apply,
    ArithmeticFunction.zeta_apply_ne (show m ≠ 0 by omega), Nat.cast_one,
    ArithmeticFunction.id_apply];

theorem boundingSum_ge_log (s : SelbergSieve) (hnu : s.nu = (ζ : ArithmeticFunction ℝ).pdiv .id)
  (hP : ∀ p:ℕ, p.Prime → (p:ℝ) ≤ s.level → p ∣ s.prodPrimes)  :
    s.selbergBoundingSum ≥ Real.log (s.level) / 2 := by
  trans (∑ m ∈ Finset.Icc 1 (Nat.floor <| Real.sqrt s.level), 1 / (m:ℝ))
  · exact boundingSum_ge_sum s hnu hP
  trans (Real.log <| Real.sqrt s.level)
  · rw [ge_iff_le]; simp_rw[one_div]
    apply Aux.log_le_sum_inv (Real.sqrt s.level)
    rw [Real.le_sqrt] <;> linarith[s.one_le_level]
  · apply ge_of_eq
    refine Real.log_sqrt ?h.hx
    linarith[s.one_le_level]

open ArithmeticFunction

theorem rem_sum_le_of_const (s : SelbergSieve) (C : ℝ) (hrem : ∀ d > 0, |rem (s := s.toBoundingSieve) d| ≤ C) :
    ∑ d ∈ s.prodPrimes.divisors, (if (d : ℝ) ≤ s.level then (3:ℝ) ^ ω d * |rem (s := s.toBoundingSieve) d| else 0)
      ≤ C * s.level * (1+Real.log s.level)^3 := by
  rw [←Finset.sum_filter]
  trans (∑ d ∈  Finset.filter (fun d:ℕ => ↑d ≤ s.level) (s.prodPrimes.divisors),  3 ^ ω d * C )
  · gcongr with d hd
    rw [Finset.mem_filter, Nat.mem_divisors] at hd
    apply hrem d
    apply Nat.pos_of_ne_zero
    apply ne_zero_of_dvd_ne_zero hd.1.2 hd.1.1
  rw [←Finset.sum_mul, mul_comm, mul_assoc]
  gcongr
  · linarith [abs_nonneg <| rem (s := s.toBoundingSieve) 1, hrem 1 (by norm_num)]
  rw [Finset.sum_filter]
  apply Aux.sum_pow_cardDistinctFactors_le_self_mul_log_pow (hx := s.one_le_level)
  apply prodPrimes_squarefree

end Sieve
end

end
end
end
end

/-! Flattened from Erdos884/Prelude884.lean. -/
section


/-!
# Erdős Problem 884 — shared definitions and basic lemmas

For a finite set `A ⊆ ℕ` we study
* `pairSum A`  — the sum of `1/(b-a)` over all pairs `a < b` in `A`  (written `T(A)` in the papers)
* `gapSum A`   — the sum of `1/(b-a)` over *consecutive* pairs of `A` (written `S(A)`)

`pairSumOn A C` restricts the pair sum to pairs satisfying a predicate `C`; `gapSum` is by
definition the pair sum over consecutive pairs.  This makes "bound the consecutive sum class by
class, where each class is estimated by its full pair sum" a one-liner (`pairSumOn_mono_pred`).
-/

open Finset

namespace Erdos884

/-- The reciprocal `1/(b - a)` of a gap, as a real number. -/
noncomputable abbrev invGap (a b : ℕ) : ℝ := ((b : ℝ) - (a : ℝ))⁻¹

/-- Sum of `1/(b-a)` over pairs `a < b` in `A` with `C a b`. -/
noncomputable def pairSumOn (A : Finset ℕ) (C : ℕ → ℕ → Prop) : ℝ :=
  letI : DecidablePred fun p : ℕ × ℕ => p.1 < p.2 ∧ C p.1 p.2 :=
    fun _ => Classical.propDecidable _
  ∑ p ∈ (A ×ˢ A).filter (fun p : ℕ × ℕ => p.1 < p.2 ∧ C p.1 p.2), invGap p.1 p.2

/-- `T(A)`: sum of reciprocals of all pairwise gaps of `A`. -/
noncomputable def pairSum (A : Finset ℕ) : ℝ := pairSumOn A fun _ _ => True

/-- `a` and `b` are consecutive elements of `A`: both belong to `A`, `a < b`, and no element
of `A` lies strictly between them. -/
def IsConsecutive (A : Finset ℕ) (a b : ℕ) : Prop :=
  a ∈ A ∧ b ∈ A ∧ a < b ∧ ∀ c ∈ A, ¬ (a < c ∧ c < b)

/-- `S(A)`: sum of reciprocals of consecutive gaps of `A`. -/
noncomputable def gapSum (A : Finset ℕ) : ℝ := pairSumOn A (IsConsecutive A)

/-! ## Basic properties (to be proved in `Basic884`) -/

lemma invGap_pos {a b : ℕ} (h : a < b) : 0 < invGap a b := by
  have : (1 : ℝ) ≤ (b : ℝ) - a := by
    have : (a : ℝ) + 1 ≤ b := by exact_mod_cast h
    linarith
  positivity

lemma invGap_le_one {a b : ℕ} (h : a < b) : invGap a b ≤ 1 := by
  have h1 : (1 : ℝ) ≤ (b : ℝ) - a := by
    have : (a : ℝ) + 1 ≤ b := by exact_mod_cast h
    linarith
  calc invGap a b ≤ (1 : ℝ)⁻¹ := by unfold invGap; gcongr
    _ = 1 := by norm_num

/-- If the (real) gap exceeds `N > 0` then the reciprocal gap is at most `1/N`. -/
lemma invGap_le {a b : ℕ} {N : ℝ} (hN : 0 < N) (h : N < (b : ℝ) - a) :
    invGap a b ≤ N⁻¹ := by
  unfold invGap
  gcongr


lemma pairSumOn_nonneg (A : Finset ℕ) (C : ℕ → ℕ → Prop) : 0 ≤ pairSumOn A C := by
  have memf : ∀ {q : ℕ × ℕ → Prop} {inst : DecidablePred q} {s : Finset (ℕ × ℕ)} {x : ℕ × ℕ},
      x ∈ @Finset.filter _ q inst s ↔ x ∈ s ∧ q x := by
    intro q inst s x
    letI := inst
    exact Finset.mem_filter
  unfold pairSumOn
  refine Finset.sum_nonneg fun p hp => ?_
  exact (invGap_pos (memf.mp hp).2.1).le

lemma pairSum_nonneg (A : Finset ℕ) : 0 ≤ pairSum A := pairSumOn_nonneg A _

lemma gapSum_nonneg (A : Finset ℕ) : 0 ≤ gapSum A := pairSumOn_nonneg A _

/-- Enlarging the predicate (on pairs of elements of `A`) enlarges the sum. -/
lemma pairSumOn_mono_pred {A : Finset ℕ} {C C' : ℕ → ℕ → Prop}
    (h : ∀ a b, a ∈ A → b ∈ A → a < b → C a b → C' a b) :
    pairSumOn A C ≤ pairSumOn A C' := by
  have memf : ∀ {q : ℕ × ℕ → Prop} {inst : DecidablePred q} {s : Finset (ℕ × ℕ)} {x : ℕ × ℕ},
      x ∈ @Finset.filter _ q inst s ↔ x ∈ s ∧ q x := by
    intro q inst s x
    letI := inst
    exact Finset.mem_filter
  unfold pairSumOn
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
  · intro p hp
    have hp' := memf.mp hp
    have hpA := Finset.mem_product.mp hp'.1
    exact memf.mpr ⟨hp'.1, hp'.2.1, h p.1 p.2 hpA.1 hpA.2 hp'.2.1 hp'.2.2⟩
  · intro p hp _
    exact (invGap_pos (memf.mp hp).2.1).le

/-- A pair sum over a disjunction of predicates is at most the sum of the pair sums. -/
lemma pairSumOn_or_le (A : Finset ℕ) (C₁ C₂ : ℕ → ℕ → Prop) :
    pairSumOn A (fun a b => C₁ a b ∨ C₂ a b) ≤ pairSumOn A C₁ + pairSumOn A C₂ := by
  classical
  have memf : ∀ {q : ℕ × ℕ → Prop} {inst : DecidablePred q} {s : Finset (ℕ × ℕ)} {x : ℕ × ℕ},
      x ∈ @Finset.filter _ q inst s ↔ x ∈ s ∧ q x := by
    intro q inst s x
    letI := inst
    exact Finset.mem_filter
  have key : ∀ (u s₁ s₂ : Finset (ℕ × ℕ)), u ⊆ s₁ ∪ s₂ →
      (∀ p ∈ s₁, (0:ℝ) ≤ invGap p.1 p.2) → (∀ p ∈ s₂, (0:ℝ) ≤ invGap p.1 p.2) →
      ∑ p ∈ u, invGap p.1 p.2 ≤ ∑ p ∈ s₁, invGap p.1 p.2 + ∑ p ∈ s₂, invGap p.1 p.2 := by
    intro u s₁ s₂ hu h1 h2
    calc ∑ p ∈ u, invGap p.1 p.2 ≤ ∑ p ∈ s₁ ∪ s₂, invGap p.1 p.2 := by
          refine Finset.sum_le_sum_of_subset_of_nonneg hu fun p hp _ => ?_
          rcases Finset.mem_union.mp hp with hm | hm
          · exact h1 p hm
          · exact h2 p hm
      _ ≤ ∑ p ∈ s₁, invGap p.1 p.2 + ∑ p ∈ s₂, invGap p.1 p.2 := by
          have h0 : (0:ℝ) ≤ ∑ p ∈ s₁ ∩ s₂, invGap p.1 p.2 :=
            Finset.sum_nonneg fun p hp => h1 p (Finset.mem_inter.mp hp).1
          rw [← Finset.sum_union_inter]
          exact le_add_of_nonneg_right h0
  unfold pairSumOn
  refine key _ _ _ ?_ ?_ ?_
  · intro p hp
    have hp' := memf.mp hp
    rcases hp'.2.2 with hc | hc
    · exact Finset.mem_union_left _ (memf.mpr ⟨hp'.1, hp'.2.1, hc⟩)
    · exact Finset.mem_union_right _ (memf.mpr ⟨hp'.1, hp'.2.1, hc⟩)
  · intro p hp
    exact (invGap_pos (memf.mp hp).2.1).le
  · intro p hp
    exact (invGap_pos (memf.mp hp).2.1).le

lemma pairSumOn_le_pairSum (A : Finset ℕ) (C : ℕ → ℕ → Prop) :
    pairSumOn A C ≤ pairSum A :=
  pairSumOn_mono_pred fun _ _ _ _ _ _ => trivial

/-- Consecutive pairs of a subset: if `B ⊆ A` and `a, b ∈ B` are consecutive in `A`,
they are consecutive in `B`. -/
lemma IsConsecutive.of_subset {A B : Finset ℕ} {a b : ℕ} (hBA : B ⊆ A)
    (ha : a ∈ B) (hb : b ∈ B) (h : IsConsecutive A a b) : IsConsecutive B a b := by
  exact ⟨ha, hb, h.2.2.1, fun c hc => h.2.2.2 c (hBA hc)⟩

/-- Bounding the gap sum by classes: if every consecutive pair of `A` satisfies `C`,
then `gapSum A ≤ pairSumOn A C`. -/
lemma gapSum_le_pairSumOn {A : Finset ℕ} {C : ℕ → ℕ → Prop}
    (h : ∀ a b, IsConsecutive A a b → C a b) :
    gapSum A ≤ pairSumOn A C :=
  pairSumOn_mono_pred fun a b _ _ _ hc => h a b hc

/-- Superadditivity of the pair sum over disjoint subsets. -/
lemma sum_pairSum_le_pairSum {ι : Type*} {I : Finset ι} {B : ι → Finset ℕ} {A : Finset ℕ}
    (hBA : ∀ i ∈ I, B i ⊆ A)
    (hdisj : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → Disjoint (B i) (B j)) :
    ∑ i ∈ I, pairSum (B i) ≤ pairSum A := by
  classical
  have memf : ∀ {q : ℕ × ℕ → Prop} {inst : DecidablePred q} {s : Finset (ℕ × ℕ)} {x : ℕ × ℕ},
      x ∈ @Finset.filter _ q inst s ↔ x ∈ s ∧ q x := by
    intro q inst s x
    letI := inst
    exact Finset.mem_filter
  have key : ∀ (s : Finset (ℕ × ℕ)) (F : ι → Finset (ℕ × ℕ)),
      (∀ i ∈ I, F i ⊆ s) →
      (∀ i ∈ I, ∀ j ∈ I, i ≠ j → Disjoint (F i) (F j)) →
      (∀ p ∈ s, (0:ℝ) ≤ invGap p.1 p.2) →
      ∑ i ∈ I, ∑ p ∈ F i, invGap p.1 p.2 ≤ ∑ p ∈ s, invGap p.1 p.2 := by
    intro s F hFs hFd hnn
    have hpd : Set.PairwiseDisjoint (↑I : Set ι) F := by
      intro i hi j hj hij
      exact hFd i hi j hj hij
    calc ∑ i ∈ I, ∑ p ∈ F i, invGap p.1 p.2
        = ∑ p ∈ I.biUnion F, invGap p.1 p.2 := (Finset.sum_biUnion hpd).symm
      _ ≤ ∑ p ∈ s, invGap p.1 p.2 := by
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun p hp _ => hnn p hp
          intro p hp
          obtain ⟨i, hi, hpi⟩ := Finset.mem_biUnion.mp hp
          exact hFs i hi hpi
  unfold pairSum pairSumOn
  refine key _ _ ?_ ?_ ?_
  · intro i hi p hp
    have hp' := memf.mp hp
    have hpq := Finset.mem_product.mp hp'.1
    exact memf.mpr
      ⟨Finset.mem_product.mpr ⟨hBA i hi hpq.1, hBA i hi hpq.2⟩, hp'.2⟩
  · intro i hi j hj hij
    rw [Finset.disjoint_left]
    intro p hpi hpj
    have h1 := Finset.mem_product.mp (memf.mp hpi).1
    have h2 := Finset.mem_product.mp (memf.mp hpj).1
    exact (Finset.disjoint_left.mp (hdisj i hi j hj hij)) h1.1 h2.1
  · intro p hp
    exact (invGap_pos (memf.mp hp).2.1).le

/-- The number of consecutive pairs is less than the cardinality: the map to the left
endpoint is injective. Combined with a uniform gap bound this bounds `gapSum`. -/
lemma gapSum_le_of_separated {A : Finset ℕ} {N : ℕ} (hN : 0 < N)
    (h : ∀ a ∈ A, ∀ b ∈ A, a < b → N < b - a) :
    gapSum A ≤ ((A.card - 1 : ℕ) : ℝ) / N := by
  classical
  have memf : ∀ {q : ℕ × ℕ → Prop} {inst : DecidablePred q} {s : Finset (ℕ × ℕ)} {x : ℕ × ℕ},
      x ∈ @Finset.filter _ q inst s ↔ x ∈ s ∧ q x := by
    intro q inst s x
    letI := inst
    exact Finset.mem_filter
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have key : ∀ S : Finset (ℕ × ℕ),
      (∀ p ∈ S, p.1 ∈ A ∧ p.2 ∈ A ∧ p.1 < p.2 ∧ IsConsecutive A p.1 p.2) →
      ∑ p ∈ S, invGap p.1 p.2 ≤ ((A.card - 1 : ℕ) : ℝ) / N := by
    intro S hS
    rcases S.eq_empty_or_nonempty with rfl | hSne
    · have h0 : (0:ℝ) ≤ ((A.card - 1 : ℕ) : ℝ) / N := by positivity
      simpa using h0
    · have hAne : A.Nonempty := by
        obtain ⟨p, hp⟩ := hSne
        exact ⟨p.1, (hS p hp).1⟩
      have hterm : ∀ p ∈ S, invGap p.1 p.2 ≤ (N : ℝ)⁻¹ := by
        intro p hp
        obtain ⟨h1, h2, hlt, -⟩ := hS p hp
        refine invGap_le hN' ?_
        have hgap := h p.1 h1 p.2 h2 hlt
        have hgap' : N + p.1 < p.2 := by omega
        have hgapR : (N : ℝ) + p.1 < p.2 := by exact_mod_cast hgap'
        linarith
      have hcard : S.card ≤ A.card - 1 := by
        have hinj : S.card ≤ (A.erase (A.max' hAne)).card := by
          apply Finset.card_le_card_of_injOn (fun p => p.1)
          · intro p hp
            obtain ⟨h1, h2, hlt, -⟩ := hS p hp
            refine Finset.mem_erase.mpr ⟨?_, h1⟩
            intro hpM
            have hpM' : p.1 = A.max' hAne := hpM
            have hle : p.2 ≤ A.max' hAne := A.le_max' p.2 h2
            omega
          · intro p hp q hq hpq
            simp only [Finset.mem_coe] at hp hq
            have hpq' : p.1 = q.1 := hpq
            obtain ⟨hp1, hp2, hplt, hpc⟩ := hS p hp
            obtain ⟨hq1, hq2, hqlt, hqc⟩ := hS q hq
            have h2eq : p.2 = q.2 := by
              by_contra hne
              rcases Nat.lt_or_ge p.2 q.2 with hlt2 | hge2
              · exact hqc.2.2.2 p.2 hp2 ⟨by omega, hlt2⟩
              · have hlt2 : q.2 < p.2 := by omega
                exact hpc.2.2.2 q.2 hq2 ⟨by omega, hlt2⟩
            exact Prod.ext hpq' h2eq
        rwa [Finset.card_erase_of_mem (A.max'_mem hAne)] at hinj
      calc ∑ p ∈ S, invGap p.1 p.2
          ≤ ∑ _p ∈ S, (N : ℝ)⁻¹ := Finset.sum_le_sum hterm
        _ = (S.card : ℝ) * (N : ℝ)⁻¹ := by rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ ((A.card - 1 : ℕ) : ℝ) * (N : ℝ)⁻¹ := by
            have hc : (S.card : ℝ) ≤ ((A.card - 1 : ℕ) : ℝ) := by exact_mod_cast hcard
            gcongr
        _ = ((A.card - 1 : ℕ) : ℝ) / N := by rw [div_eq_mul_inv]
  unfold gapSum pairSumOn
  refine key _ fun p hp => ?_
  have hp' := memf.mp hp
  have hpq := Finset.mem_product.mp hp'.1
  exact ⟨hpq.1, hpq.2, hp'.2.1, hp'.2.2⟩

end Erdos884
end

/-! Flattened from Erdos884/DivisorsProd884.lean. -/
section

/-
  DivisorsProd884.lean — divisors of products of distinct primes,
  for the formalization of Larsen's disproof of Erdős problem #884.

  Exports:
    primeFactors_prodPrimes, squarefree_prodPrimes, divisors_prodPrimes,
    prodPrimes_injOn, card_divisors_prodPrimes,
    sum_inv_divisors_erase_one_le, sum_inv_divisors_le,
    prod_gcd_of_dvd_prod, card_primeFactors_eq_sum_gcd
-/

namespace Erdos884

open Function

theorem primeFactors_prodPrimes {s : Finset ℕ} (hs : ∀ p ∈ s, p.Prime) :
    (∏ p ∈ s, p).primeFactors = s :=
  Nat.primeFactors_prod hs

theorem squarefree_prodPrimes {s : Finset ℕ} (hs : ∀ p ∈ s, p.Prime) :
    Squarefree (∏ p ∈ s, p) := by
  refine Nat.squarefree_iff_prime_squarefree.mpr ?_
  intro p hp h_dvd
  by_cases hps : p ∈ s
  · rw [← Finset.mul_prod_erase s (fun p => p) hps,
      mul_dvd_mul_iff_left hp.ne_zero] at h_dvd
    obtain ⟨q, hq, hpq⟩ := hp.prime.exists_mem_finset_dvd h_dvd
    rw [Finset.mem_erase] at hq
    exact hq.1 ((Nat.prime_dvd_prime_iff_eq hp (hs q hq.2)).mp hpq).symm
  · obtain ⟨q, hq, hpq⟩ := hp.prime.exists_mem_finset_dvd ((dvd_mul_right p p).trans h_dvd)
    have heq : p = q := (Nat.prime_dvd_prime_iff_eq hp (hs q hq)).mp hpq
    subst heq
    exact hps hq

theorem divisors_prodPrimes {B : Finset ℕ} (hB : ∀ p ∈ B, p.Prime) :
    (∏ p ∈ B, p).divisors = B.powerset.image fun s => ∏ p ∈ s, p := by
  have hP0 : (∏ p ∈ B, p) ≠ 0 :=
    (Finset.prod_pos fun p hp => (hB p hp).pos).ne'
  ext d
  simp only [Nat.mem_divisors, Finset.mem_image, Finset.mem_powerset]
  constructor
  · rintro ⟨hd, -⟩
    refine ⟨d.primeFactors, ?_, ?_⟩
    · calc d.primeFactors
          ⊆ (∏ p ∈ B, p).primeFactors := Nat.primeFactors_mono hd hP0
        _ = B := Nat.primeFactors_prod hB
    · exact Nat.prod_primeFactors_of_squarefree
        (Squarefree.squarefree_of_dvd hd (squarefree_prodPrimes hB))
  · rintro ⟨s, hs, rfl⟩
    exact ⟨Finset.prod_dvd_prod_of_subset s B (fun p => p) hs, hP0⟩

theorem prodPrimes_injOn {B : Finset ℕ} (hB : ∀ p ∈ B, p.Prime) :
    Set.InjOn (fun s : Finset ℕ => ∏ p ∈ s, p) B.powerset := by
  intro s hs t ht hst
  have hs' : s ⊆ B := Finset.mem_powerset.mp (Finset.mem_coe.mp hs)
  have ht' : t ⊆ B := Finset.mem_powerset.mp (Finset.mem_coe.mp ht)
  have h1 : (∏ p ∈ s, p).primeFactors = s :=
    Nat.primeFactors_prod fun p hp => hB p (hs' hp)
  have h2 : (∏ p ∈ t, p).primeFactors = t :=
    Nat.primeFactors_prod fun p hp => hB p (ht' hp)
  have hst' : ∏ p ∈ s, p = ∏ p ∈ t, p := hst
  rw [← h1, ← h2, hst']

theorem card_divisors_prodPrimes {B : Finset ℕ} (hB : ∀ p ∈ B, p.Prime) :
    (∏ p ∈ B, p).divisors.card = 2 ^ B.card := by
  rw [divisors_prodPrimes hB, Finset.card_image_of_injOn (prodPrimes_injOn hB),
    Finset.card_powerset]

/-! ### Bounding the sum of inverses of divisors -/

/-- If `0 ≤ u` and `2Ku ≤ 1` then `(1+u)^K ≤ 1 + 2Ku`. -/
lemma one_add_pow_le_aux {u : ℝ} (hu : 0 ≤ u) :
    ∀ K : ℕ, 2 * K * u ≤ 1 → (1 + u) ^ K ≤ 1 + 2 * K * u := by
  intro K
  induction K with
  | zero => intro _; norm_num
  | succ K ih =>
    intro hK1
    push_cast at hK1 ⊢
    have h2K : 2 * (K : ℝ) * u ≤ 1 := by
      have hstep : 2 * (K : ℝ) * u ≤ 2 * ((K : ℝ) + 1) * u :=
        mul_le_mul_of_nonneg_right (by linarith) hu
      linarith
    have h1u : (0 : ℝ) ≤ 1 + u := by linarith
    have hKuu : 2 * (K : ℝ) * u * u ≤ 1 * u := mul_le_mul_of_nonneg_right h2K hu
    calc (1 + u) ^ (K + 1) = (1 + u) ^ K * (1 + u) := pow_succ _ _
      _ ≤ (1 + 2 * (K : ℝ) * u) * (1 + u) := mul_le_mul_of_nonneg_right (ih h2K) h1u
      _ = 1 + 2 * (K : ℝ) * u + u + 2 * (K : ℝ) * u * u := by ring
      _ ≤ 1 + 2 * ((K : ℝ) + 1) * u := by linarith

theorem sum_inv_divisors_le {B : Finset ℕ} {x₀ : ℕ} (hB : ∀ p ∈ B, p.Prime)
    (hlow : ∀ p ∈ B, x₀ ≤ p) (hx₀ : 2 * B.card ≤ x₀) (h0 : 0 < x₀) :
    ∑ d ∈ (∏ p ∈ B, p).divisors, ((d:ℝ))⁻¹ ≤ 1 + 2 * B.card / x₀ := by
  have hx0R : (0 : ℝ) < (x₀ : ℝ) := by exact_mod_cast h0
  have hcardle : 2 * (B.card : ℝ) * ((x₀ : ℝ))⁻¹ ≤ 1 := by
    have h1 : 2 * (B.card : ℝ) ≤ (x₀ : ℝ) := by exact_mod_cast hx₀
    have h2 : 2 * (B.card : ℝ) * ((x₀ : ℝ))⁻¹ ≤ (x₀ : ℝ) * ((x₀ : ℝ))⁻¹ :=
      mul_le_mul_of_nonneg_right h1 (by positivity)
    rwa [mul_inv_cancel₀ hx0R.ne'] at h2
  rw [divisors_prodPrimes hB, Finset.sum_image (prodPrimes_injOn hB)]
  calc ∑ s ∈ B.powerset, (((∏ p ∈ s, p : ℕ) : ℝ))⁻¹
      = ∑ s ∈ B.powerset, ∏ p ∈ s, ((p : ℝ))⁻¹ := by
        refine Finset.sum_congr rfl fun s _ => ?_
        rw [Nat.cast_prod]
        exact (Finset.prod_inv_distrib _).symm
    _ = ∏ p ∈ B, (1 + ((p : ℝ))⁻¹) := (Finset.prod_one_add B).symm
    _ ≤ (1 + ((x₀ : ℝ))⁻¹) ^ B.card := by
        rw [← Finset.prod_const]
        refine Finset.prod_le_prod (fun p _ => by positivity) fun p hp => ?_
        have hxp : (x₀ : ℝ) ≤ (p : ℝ) := by exact_mod_cast hlow p hp
        have hinv := inv_anti₀ hx0R hxp
        linarith
    _ ≤ 1 + 2 * (B.card : ℝ) * ((x₀ : ℝ))⁻¹ :=
        one_add_pow_le_aux (by positivity) B.card hcardle
    _ = 1 + 2 * (B.card : ℝ) / (x₀ : ℝ) := by rw [div_eq_mul_inv]

theorem sum_inv_divisors_erase_one_le {B : Finset ℕ} {x₀ : ℕ} (hB : ∀ p ∈ B, p.Prime)
    (hlow : ∀ p ∈ B, x₀ ≤ p) (hx₀ : 2 * B.card ≤ x₀) (h0 : 0 < x₀) :
    ∑ d ∈ (∏ p ∈ B, p).divisors.erase 1, ((d:ℝ))⁻¹ ≤ 2 * B.card / x₀ := by
  have hP0 : (∏ p ∈ B, p) ≠ 0 :=
    (Finset.prod_pos fun p hp => (hB p hp).pos).ne'
  have h1mem : 1 ∈ (∏ p ∈ B, p).divisors := Nat.one_mem_divisors.mpr hP0
  have hsplit := Finset.add_sum_erase (∏ p ∈ B, p).divisors
    (fun d => ((d : ℝ))⁻¹) h1mem
  have hsum := sum_inv_divisors_le hB hlow hx₀ h0
  rw [← hsplit] at hsum
  norm_num at hsum
  linarith

/-! ### Divisors of products of pairwise coprime numbers -/

/-- If the members of `t` are pairwise coprime under `f`, and `a ∉ t` is such that
`Finset.cons a t` is still pairwise coprime, then `f a` is coprime to `∏ i ∈ t, f i`. -/
private lemma coprime_prod_of_pairwise_cons {ι : Type*} {f : ι → ℕ} {a : ι} {t : Finset ι}
    (ha : a ∉ t) (h : (↑(Finset.cons a t ha) : Set ι).Pairwise (Nat.Coprime on f)) :
    Nat.Coprime (f a) (∏ i ∈ t, f i) := by
  refine Nat.Coprime.prod_right fun i hi => ?_
  have hne : a ≠ i := by rintro rfl; exact ha hi
  have hma : a ∈ (↑(Finset.cons a t ha) : Set ι) := by
    rw [Finset.coe_cons]; exact Set.mem_insert _ _
  have hmi : i ∈ (↑(Finset.cons a t ha) : Set ι) := by
    rw [Finset.coe_cons]; exact Set.mem_insert_of_mem _ (Finset.mem_coe.mpr hi)
  exact h hma hmi hne

private lemma gcd_prod_eq_prod_gcd {ι : Type*} (d : ℕ) {m : ι → ℕ} (t : Finset ι) :
    (↑t : Set ι).Pairwise (Nat.Coprime on m) →
      Nat.gcd d (∏ i ∈ t, m i) = ∏ i ∈ t, Nat.gcd d (m i) := by
  induction t using Finset.cons_induction with
  | empty => intro _; simp
  | cons a t ha ih =>
    intro h
    have hsub : (↑t : Set ι) ⊆ ↑(Finset.cons a t ha) := by
      rw [Finset.coe_cons]; exact Set.subset_insert _ _
    have hcop : Nat.Coprime (m a) (∏ i ∈ t, m i) := coprime_prod_of_pairwise_cons ha h
    rw [Finset.prod_cons ha, Finset.prod_cons ha, Nat.Coprime.gcd_mul d hcop,
      ih (h.mono hsub)]

private lemma card_primeFactors_prod {ι : Type*} {f : ι → ℕ} (t : Finset ι) :
    (∀ i ∈ t, f i ≠ 0) → (↑t : Set ι).Pairwise (Nat.Coprime on f) →
      (∏ i ∈ t, f i).primeFactors.card = ∑ i ∈ t, (f i).primeFactors.card := by
  induction t using Finset.cons_induction with
  | empty => intro _ _; simp
  | cons a t ha ih =>
    intro h0 h
    have hsub : (↑t : Set ι) ⊆ ↑(Finset.cons a t ha) := by
      rw [Finset.coe_cons]; exact Set.subset_insert _ _
    have ha0 : f a ≠ 0 := h0 a (Finset.mem_cons_self a t)
    have ht0 : ∀ i ∈ t, f i ≠ 0 := fun i hi => h0 i (Finset.mem_cons_of_mem hi)
    have hprod0 : (∏ i ∈ t, f i) ≠ 0 := Finset.prod_ne_zero_iff.mpr ht0
    have hcop : Nat.Coprime (f a) (∏ i ∈ t, f i) := coprime_prod_of_pairwise_cons ha h
    rw [Finset.prod_cons ha, Finset.sum_cons ha, Nat.primeFactors_mul ha0 hprod0,
      Finset.card_union_of_disjoint hcop.disjoint_primeFactors, ih ht0 (h.mono hsub)]

theorem prod_gcd_of_dvd_prod {r : ℕ} {m : Fin r → ℕ} (hm : ∀ i, m i ≠ 0)
    (hcop : Pairwise (Nat.Coprime on m)) {d : ℕ} (hd : d ∣ ∏ i, m i) :
    d = ∏ i, Nat.gcd d (m i) := by
  have hpw : (↑(Finset.univ : Finset (Fin r)) : Set (Fin r)).Pairwise (Nat.Coprime on m) :=
    fun i _ j _ hij => hcop hij
  calc d = Nat.gcd d (∏ i, m i) := (Nat.gcd_eq_left hd).symm
    _ = ∏ i, Nat.gcd d (m i) := gcd_prod_eq_prod_gcd d Finset.univ hpw

theorem card_primeFactors_eq_sum_gcd {r : ℕ} {m : Fin r → ℕ} (hm : ∀ i, m i ≠ 0)
    (hcop : Pairwise (Nat.Coprime on m)) {d : ℕ} (hd : d ∣ ∏ i, m i) (hd0 : d ≠ 0) :
    d.primeFactors.card = ∑ i, (Nat.gcd d (m i)).primeFactors.card := by
  have hg0 : ∀ i ∈ (Finset.univ : Finset (Fin r)), Nat.gcd d (m i) ≠ 0 := by
    intro i _ hzero
    exact hm i (Nat.gcd_eq_zero_iff.mp hzero).2
  have hgcop : (↑(Finset.univ : Finset (Fin r)) : Set (Fin r)).Pairwise
      (Nat.Coprime on fun i => Nat.gcd d (m i)) := by
    intro i _ j _ hij
    have h1 : (m i).Coprime (m j) := hcop hij
    exact Nat.Coprime.coprime_dvd_left (Nat.gcd_dvd_right d (m i))
      (Nat.Coprime.coprime_dvd_right (Nat.gcd_dvd_right d (m j)) h1)
  conv_lhs => rw [prod_gcd_of_dvd_prod hm hcop hd]
  exact card_primeFactors_prod Finset.univ hg0 hgcop

end Erdos884
end

/-! Flattened from Erdos884/PolyGap884.lean. -/
section

/-!
# Erdős 884 — Lemma F: polynomial gap bounds (Tao Lemma 2.2)

Real product functions `x ↦ ∏ (x - a)` over finsets, shifted elementary symmetric
sums, and the constant/non-constant difference dichotomy.
-/

namespace Erdos884

theorem F_prod_nonneg (s : Finset ℝ) (y : ℝ) (h : ∀ a ∈ s, a ≤ y) : 0 ≤ ∏ a ∈ s, (y - a) :=
  Finset.prod_nonneg fun a ha => sub_nonneg.2 (h a ha)

theorem F_prod_mono (s : Finset ℝ) {x y : ℝ} (h : ∀ a ∈ s, a ≤ y) (hxy : y ≤ x) :
    ∏ a ∈ s, (y - a) ≤ ∏ a ∈ s, (x - a) :=
  Finset.prod_le_prod (fun a ha => sub_nonneg.2 (h a ha)) (fun a ha => by
    have := h a ha; linarith)

theorem F_prod_sub_ge (s : Finset ℝ) {a₀ x y : ℝ} (ha₀ : a₀ ∈ s) (h : ∀ a ∈ s, a ≤ y)
    (hxy : y ≤ x) :
    (x - y) * ∏ a ∈ s.erase a₀, (y - a) ≤ (∏ a ∈ s, (x - a)) - ∏ a ∈ s, (y - a) := by
  have ht' : ∀ a ∈ s.erase a₀, a ≤ y := fun a ha => h a (Finset.mem_of_mem_erase ha)
  have hx : ∏ a ∈ s, (x - a) = (x - a₀) * ∏ a ∈ s.erase a₀, (x - a) := by
    rw [← Finset.prod_insert (Finset.notMem_erase a₀ s), Finset.insert_erase ha₀]
  have hy : ∏ a ∈ s, (y - a) = (y - a₀) * ∏ a ∈ s.erase a₀, (y - a) := by
    rw [← Finset.prod_insert (Finset.notMem_erase a₀ s), Finset.insert_erase ha₀]
  have h1 : ∏ a ∈ s.erase a₀, (y - a) ≤ ∏ a ∈ s.erase a₀, (x - a) := F_prod_mono _ ht' hxy
  have h2 : 0 ≤ ∏ a ∈ s.erase a₀, (y - a) := F_prod_nonneg _ y ht'
  have h3 : 0 ≤ y - a₀ := sub_nonneg.2 (h a₀ ha₀)
  have h4 : (x - y) * ∏ a ∈ s.erase a₀, (y - a) ≤ (x - y) * ∏ a ∈ s.erase a₀, (x - a) :=
    mul_le_mul_of_nonneg_left h1 (by linarith)
  have h5 : 0 ≤ (y - a₀) * (∏ a ∈ s.erase a₀, (x - a) - ∏ a ∈ s.erase a₀, (y - a)) :=
    mul_nonneg h3 (by linarith)
  rw [hx, hy]
  nlinarith [h4, h5]

theorem F_const_gap {s s' : Finset ℝ} (hne : s.Nonempty) (hne' : s'.Nonempty) {ℓ : ℝ}
    (hℓ : 0 < ℓ)
    (heq : ∀ x : ℝ, ∏ a ∈ s, (x - a) = (∏ a ∈ s', (x - a)) + ℓ) :
    s.max' hne < s'.max' hne' ∧
    (s'.max' hne' - s.max' hne) * ∏ a ∈ s.erase (s.max' hne), (s.max' hne - a) ≤ ℓ := by
  have hM : s.max' hne ∈ s := s.max'_mem hne
  have hM' : s'.max' hne' ∈ s' := s'.max'_mem hne'
  have hPs0 : ∏ a ∈ s, (s.max' hne - a) = 0 := Finset.prod_eq_zero hM (sub_self _)
  have hPs'0 : ∏ a ∈ s', (s'.max' hne' - a) = 0 := Finset.prod_eq_zero hM' (sub_self _)
  have hlt : s.max' hne < s'.max' hne' := by
    by_contra hcon
    push_neg at hcon
    have h0 := heq (s.max' hne)
    rw [hPs0] at h0
    have hge : 0 ≤ ∏ a ∈ s', (s.max' hne - a) :=
      F_prod_nonneg s' _ fun a ha => le_trans (s'.le_max' a ha) hcon
    linarith
  refine ⟨hlt, ?_⟩
  have hPsM' : ∏ a ∈ s, (s'.max' hne' - a) = ℓ := by
    rw [heq (s'.max' hne'), hPs'0, zero_add]
  have hkey := F_prod_sub_ge s hM (fun a ha => s.le_max' a ha) hlt.le
  rw [hPsM', hPs0, sub_zero] at hkey
  exact hkey

/-- Shifted elementary symmetric sum: the `j`-th elementary symmetric polynomial of the
(truncated) shifts `p - x₀`, `p ∈ s`. -/
noncomputable def esymmShift (x₀ : ℕ) (s : Finset ℕ) (j : ℕ) : ℕ :=
  ∑ u ∈ s.powerset.filter (fun u => u.card = j), ∏ p ∈ u, (p - x₀)

theorem esymmShift_zero (x₀ : ℕ) (s : Finset ℕ) : esymmShift x₀ s 0 = 1 := by
  unfold esymmShift
  have h : s.powerset.filter (fun u => u.card = 0) = {∅} := by
    ext u
    simp only [Finset.mem_filter, Finset.mem_powerset, Finset.card_eq_zero, Finset.mem_singleton]
    exact ⟨fun h => h.2, fun h => ⟨h ▸ Finset.empty_subset s, h⟩⟩
  rw [h, Finset.sum_singleton, Finset.prod_empty]

theorem F_prod_expand {x₀ : ℕ} {s : Finset ℕ} (h : ∀ p ∈ s, x₀ ≤ p) (x : ℝ) :
    ∏ p ∈ s, (x + (p:ℝ)) =
      ∑ j ∈ Finset.range (s.card + 1), (esymmShift x₀ s j : ℝ) * (x + (x₀:ℝ)) ^ (s.card - j) := by
  classical
  have hsplit : ∀ p ∈ s, x + (p:ℝ) = ((p - x₀ : ℕ) : ℝ) + (x + (x₀:ℝ)) := by
    intro p hp
    rw [Nat.cast_sub (h p hp)]
    ring
  calc ∏ p ∈ s, (x + (p:ℝ))
      = ∏ p ∈ s, (((p - x₀ : ℕ):ℝ) + (x + (x₀:ℝ))) := Finset.prod_congr rfl hsplit
    _ = ∑ u ∈ s.powerset, (∏ p ∈ u, ((p - x₀:ℕ):ℝ)) * ∏ _p ∈ s \ u, (x + (x₀:ℝ)) :=
        Finset.prod_add _ _ s
    _ = ∑ u ∈ s.powerset, (∏ p ∈ u, ((p - x₀:ℕ):ℝ)) * (x + (x₀:ℝ)) ^ (s.card - u.card) := by
        refine Finset.sum_congr rfl fun u hu => ?_
        rw [Finset.prod_const, Finset.card_sdiff,
          Finset.inter_eq_left.2 (Finset.mem_powerset.1 hu)]
    _ = ∑ j ∈ Finset.range (s.card + 1), ∑ u ∈ s.powerset.filter (fun u => u.card = j),
          (∏ p ∈ u, ((p - x₀:ℕ):ℝ)) * (x + (x₀:ℝ)) ^ (s.card - u.card) := by
        refine (Finset.sum_fiberwise_of_maps_to (fun u hu => ?_) _).symm
        rw [Finset.mem_range, Nat.lt_succ_iff]
        exact Finset.card_le_card (Finset.mem_powerset.1 hu)
    _ = ∑ j ∈ Finset.range (s.card + 1), (esymmShift x₀ s j : ℝ) * (x + (x₀:ℝ)) ^ (s.card - j) := by
        refine Finset.sum_congr rfl fun j hj => ?_
        simp only [esymmShift]
        rw [Nat.cast_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun u hu => ?_
        rw [Nat.cast_prod, (Finset.mem_filter.1 hu).2]

theorem esymmShift_le {x₀ H : ℕ} {s : Finset ℕ} (h : ∀ p ∈ s, p ≤ x₀ + H) (j : ℕ) :
    esymmShift x₀ s j ≤ 2 ^ s.card * H ^ j := by
  classical
  unfold esymmShift
  calc ∑ u ∈ s.powerset.filter (fun u => u.card = j), ∏ p ∈ u, (p - x₀)
      ≤ ∑ _u ∈ s.powerset.filter (fun u => u.card = j), H ^ j := by
        refine Finset.sum_le_sum fun u hu => ?_
        obtain ⟨hus, huj⟩ := Finset.mem_filter.1 hu
        rw [Finset.mem_powerset] at hus
        calc ∏ p ∈ u, (p - x₀) ≤ ∏ _p ∈ u, H :=
              Finset.prod_le_prod' fun p hp => by have := h p (hus hp); omega
          _ = H ^ u.card := Finset.prod_const H
          _ = H ^ j := by rw [huj]
    _ = (s.powerset.filter (fun u => u.card = j)).card * H ^ j := by
        rw [Finset.sum_const, smul_eq_mul]
    _ ≤ 2 ^ s.card * H ^ j :=
        Nat.mul_le_mul (le_trans (Finset.card_filter_le _ _)
          (le_of_eq (Finset.card_powerset s))) le_rfl

theorem F_const_of_esymm_eq {x₀ : ℕ} {s s' : Finset ℕ}
    (hs : ∀ p ∈ s, x₀ ≤ p) (hs' : ∀ p ∈ s', x₀ ≤ p) (hcard : s.card = s'.card)
    (heq : ∀ j, j < s.card → esymmShift x₀ s j = esymmShift x₀ s' j) (x : ℝ) :
    ∏ p ∈ s, (x + (p:ℝ)) = (∏ p ∈ s', (x + (p:ℝ))) + ((∏ p ∈ s, (p:ℝ)) - ∏ p ∈ s', (p:ℝ)) := by
  have key : ∀ y : ℝ, (∏ p ∈ s, (y + (p:ℝ))) - ∏ p ∈ s', (y + (p:ℝ)) =
      (esymmShift x₀ s s.card : ℝ) - (esymmShift x₀ s' s.card : ℝ) := by
    intro y
    rw [F_prod_expand hs y, F_prod_expand hs' y, ← hcard, ← Finset.sum_sub_distrib,
      Finset.sum_range_succ]
    have h0 : ∑ j ∈ Finset.range s.card,
        ((esymmShift x₀ s j : ℝ) * (y + (x₀:ℝ)) ^ (s.card - j)
          - (esymmShift x₀ s' j : ℝ) * (y + (x₀:ℝ)) ^ (s.card - j)) = 0 :=
      Finset.sum_eq_zero fun j hj => by rw [heq j (Finset.mem_range.1 hj)]; ring
    rw [h0, Nat.sub_self, pow_zero, zero_add]
    ring
  have h1 := key x
  have h2 := key 0
  simp only [zero_add] at h2
  linarith

/-- Internal helper: partial geometric-type sums with ratio ≤ 1/2 are at most twice the
leading term. -/
lemma geom_sum_aux {a b : ℝ} (ha : 0 ≤ a) (hab : 2 * a ≤ b) (m : ℕ) :
    ∑ i ∈ Finset.range (m + 1), a ^ i * b ^ (m - i) ≤ 2 * b ^ m := by
  have hb : 0 ≤ b := by linarith
  induction m with
  | zero => norm_num [Finset.sum_range_one]
  | succ n ih =>
    rw [Finset.sum_range_succ']
    have h1 : ∀ i ∈ Finset.range (n + 1),
        a ^ (i + 1) * b ^ (n + 1 - (i + 1)) = a * (a ^ i * b ^ (n - i)) := by
      intro i _
      have he : n + 1 - (i + 1) = n - i := by omega
      rw [he, pow_succ]
      ring
    rw [Finset.sum_congr rfl h1, ← Finset.mul_sum]
    have h2 : a * ∑ i ∈ Finset.range (n + 1), a ^ i * b ^ (n - i) ≤ a * (2 * b ^ n) :=
      mul_le_mul_of_nonneg_left ih ha
    have hbn : 0 ≤ b ^ n := pow_nonneg hb n
    have h3 : a * (2 * b ^ n) ≤ b * b ^ n := by nlinarith
    have h4 : b * b ^ n = b ^ (n + 1) := by rw [pow_succ]; ring
    simp only [pow_zero, one_mul, Nat.sub_zero]
    linarith

/-- Internal helper: distinct naturals differ by at least 1 as reals. -/
lemma one_le_abs_natCast_sub {a b : ℕ} (h : a ≠ b) : (1:ℝ) ≤ |(a:ℝ) - (b:ℝ)| := by
  rcases lt_or_gt_of_ne h with hlt | hlt
  · have h1 : a + 1 ≤ b := hlt
    have h2 : (a:ℝ) + 1 ≤ (b:ℝ) := by exact_mod_cast h1
    rw [abs_sub_comm, abs_of_nonneg (by linarith)]
    linarith
  · have h1 : b + 1 ≤ a := hlt
    have h2 : (b:ℝ) + 1 ≤ (a:ℝ) := by exact_mod_cast h1
    rw [abs_of_nonneg (by linarith)]
    linarith

/-- Internal helper: if the coefficients of `∑ f j · x^(k-j)` vanish below `j₀`, the `j₀`-th has
absolute value ≥ 1, and the later ones are geometrically small compared to `x`, then the whole
sum has absolute value at least `x/2`. -/
lemma abs_expansion_ge {x C Hb : ℝ} {k j₀ : ℕ} (f : ℕ → ℝ)
    (hx1 : 1 ≤ x) (hHb : 0 ≤ Hb) (h2H : 2 * Hb ≤ x) (hC : 0 ≤ C)
    (hj₀k : j₀ < k)
    (hzero : ∀ i, i < j₀ → f i = 0)
    (hhead : 1 ≤ |f j₀|)
    (htail : ∀ j, j₀ < j → |f j| ≤ C * Hb ^ j)
    (hfinal : 4 * (C * Hb ^ (j₀ + 1)) ≤ x) :
    x / 2 ≤ |∑ j ∈ Finset.range (k + 1), f j * x ^ (k - j)| := by
  have hx0 : 0 ≤ x := by linarith
  obtain ⟨m, rfl⟩ : ∃ m, k = j₀ + 1 + m := ⟨k - j₀ - 1, by omega⟩
  have he1 : j₀ + 1 + m - j₀ = m + 1 := by omega
  -- split off the head term; earlier terms vanish
  have hsplit : ∑ j ∈ Finset.range (j₀ + 1 + m + 1), f j * x ^ (j₀ + 1 + m - j)
      = f j₀ * x ^ (m + 1)
        + ∑ j ∈ Finset.Ico (j₀ + 1) (j₀ + 1 + m + 1), f j * x ^ (j₀ + 1 + m - j) := by
    rw [Finset.range_eq_Ico,
      ← Finset.sum_Ico_consecutive (fun j => f j * x ^ (j₀ + 1 + m - j)) (Nat.zero_le j₀)
        (by omega : j₀ ≤ j₀ + 1 + m + 1)]
    have hzs : ∑ j ∈ Finset.Ico 0 j₀, f j * x ^ (j₀ + 1 + m - j) = 0 :=
      Finset.sum_eq_zero fun j hj => by rw [hzero j (Finset.mem_Ico.1 hj).2]; ring
    rw [hzs, zero_add,
      Finset.sum_eq_sum_Ico_succ_bot (by omega : j₀ < j₀ + 1 + m + 1)
        (fun j => f j * x ^ (j₀ + 1 + m - j)), he1]
  -- the tail is small
  have htail_bound : |∑ j ∈ Finset.Ico (j₀ + 1) (j₀ + 1 + m + 1), f j * x ^ (j₀ + 1 + m - j)|
      ≤ 2 * (C * Hb ^ (j₀ + 1)) * x ^ m := by
    have hstep1 : |∑ j ∈ Finset.Ico (j₀ + 1) (j₀ + 1 + m + 1), f j * x ^ (j₀ + 1 + m - j)|
        ≤ ∑ j ∈ Finset.Ico (j₀ + 1) (j₀ + 1 + m + 1), C * Hb ^ j * x ^ (j₀ + 1 + m - j) := by
      refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum fun j hj => ?_)
      obtain ⟨hj1, _hj2⟩ := Finset.mem_Ico.1 hj
      rw [abs_mul, abs_pow, abs_of_nonneg hx0]
      exact mul_le_mul_of_nonneg_right (htail j hj1) (pow_nonneg hx0 _)
    have hstep2 : ∑ j ∈ Finset.Ico (j₀ + 1) (j₀ + 1 + m + 1), C * Hb ^ j * x ^ (j₀ + 1 + m - j)
        = (C * Hb ^ (j₀ + 1)) * ∑ i ∈ Finset.range (m + 1), Hb ^ i * x ^ (m - i) := by
      rw [Finset.sum_Ico_eq_sum_range]
      have he2 : j₀ + 1 + m + 1 - (j₀ + 1) = m + 1 := by omega
      rw [he2, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i hi => ?_
      have he3 : j₀ + 1 + m - (j₀ + 1 + i) = m - i := by omega
      rw [he3, pow_add]
      ring
    have hstep3 : (C * Hb ^ (j₀ + 1)) * ∑ i ∈ Finset.range (m + 1), Hb ^ i * x ^ (m - i)
        ≤ (C * Hb ^ (j₀ + 1)) * (2 * x ^ m) :=
      mul_le_mul_of_nonneg_left (geom_sum_aux hHb h2H m) (mul_nonneg hC (pow_nonneg hHb _))
    calc |∑ j ∈ Finset.Ico (j₀ + 1) (j₀ + 1 + m + 1), f j * x ^ (j₀ + 1 + m - j)|
        ≤ ∑ j ∈ Finset.Ico (j₀ + 1) (j₀ + 1 + m + 1), C * Hb ^ j * x ^ (j₀ + 1 + m - j) := hstep1
      _ = (C * Hb ^ (j₀ + 1)) * ∑ i ∈ Finset.range (m + 1), Hb ^ i * x ^ (m - i) := hstep2
      _ ≤ (C * Hb ^ (j₀ + 1)) * (2 * x ^ m) := hstep3
      _ = 2 * (C * Hb ^ (j₀ + 1)) * x ^ m := by ring
  -- the head is big
  have hhead_bound : x ^ (m + 1) ≤ |f j₀ * x ^ (m + 1)| := by
    rw [abs_mul, abs_pow, abs_of_nonneg hx0]
    exact le_mul_of_one_le_left (pow_nonneg hx0 _) hhead
  -- triangle inequality: |head + tail| ≥ |head| - |tail|
  have htri : |f j₀ * x ^ (m + 1)|
      - |∑ j ∈ Finset.Ico (j₀ + 1) (j₀ + 1 + m + 1), f j * x ^ (j₀ + 1 + m - j)|
      ≤ |f j₀ * x ^ (m + 1)
          + ∑ j ∈ Finset.Ico (j₀ + 1) (j₀ + 1 + m + 1), f j * x ^ (j₀ + 1 + m - j)| := by
    have h := abs_sub_abs_le_abs_sub (f j₀ * x ^ (m + 1))
      (-(∑ j ∈ Finset.Ico (j₀ + 1) (j₀ + 1 + m + 1), f j * x ^ (j₀ + 1 + m - j)))
    rw [abs_neg, sub_neg_eq_add] at h
    linarith
  -- assemble
  have hxm : 1 ≤ x ^ m := one_le_pow₀ hx1
  have hfin1 : 4 * (C * Hb ^ (j₀ + 1)) * x ^ m ≤ x * x ^ m :=
    mul_le_mul_of_nonneg_right hfinal (pow_nonneg hx0 m)
  have hpow : x ^ (m + 1) = x * x ^ m := by rw [pow_succ]; ring
  rw [hsplit]
  calc x / 2 ≤ x / 2 * x ^ m := le_mul_of_one_le_right (by linarith) hxm
    _ ≤ x ^ (m + 1) - 2 * (C * Hb ^ (j₀ + 1)) * x ^ m := by rw [hpow]; linarith
    _ ≤ |f j₀ * x ^ (m + 1)|
        - |∑ j ∈ Finset.Ico (j₀ + 1) (j₀ + 1 + m + 1), f j * x ^ (j₀ + 1 + m - j)| := by
          linarith [hhead_bound, htail_bound]
    _ ≤ |f j₀ * x ^ (m + 1)
        + ∑ j ∈ Finset.Ico (j₀ + 1) (j₀ + 1 + m + 1), f j * x ^ (j₀ + 1 + m - j)| := htri

theorem F_nonconst_gap {x₀ H K : ℕ} {s s' : Finset ℕ}
    (hs : ∀ p ∈ s, x₀ < p ∧ p ≤ x₀ + H) (hs' : ∀ p ∈ s', x₀ < p ∧ p ≤ x₀ + H)
    (hcard : s.card = s'.card) (hK : s.card ≤ K) (hH : 1 ≤ H)
    (hbig : 8 * (2*H)^(K+1) ≤ x₀)
    (hne : ∃ j, j < s.card ∧ esymmShift x₀ s j ≠ esymmShift x₀ s' j) :
    (x₀ : ℝ) / 2 ≤ |(∏ p ∈ s, (p:ℝ)) - ∏ p ∈ s', (p:ℝ)| := by
  classical
  -- basic numeric facts
  have h2Hx : 2 * H ≤ x₀ := by
    have h1 : 2 * H ≤ (2 * H) ^ (K + 1) := Nat.le_self_pow (by omega) _
    have h2 : (2 * H) ^ (K + 1) ≤ 8 * (2 * H) ^ (K + 1) :=
      le_mul_of_one_le_left (Nat.zero_le _) (by norm_num)
    exact le_trans h1 (le_trans h2 hbig)
  have hx1 : 1 ≤ x₀ := by omega
  -- expansions at x = 0 give the difference of products as a sum
  have hs1 : ∀ p ∈ s, x₀ ≤ p := fun p hp => (hs p hp).1.le
  have hs1' : ∀ p ∈ s', x₀ ≤ p := fun p hp => (hs' p hp).1.le
  have hexp := F_prod_expand hs1 0
  have hexp' := F_prod_expand hs1' 0
  simp only [zero_add] at hexp hexp'
  have hD : (∏ p ∈ s, (p:ℝ)) - ∏ p ∈ s', (p:ℝ)
      = ∑ j ∈ Finset.range (s.card + 1),
          ((esymmShift x₀ s j : ℝ) - (esymmShift x₀ s' j : ℝ)) * (x₀:ℝ) ^ (s.card - j) := by
    rw [hexp, hexp', ← hcard, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  -- least index at which the shifted symmetric sums differ
  have hne2 : ∃ j, esymmShift x₀ s j ≠ esymmShift x₀ s' j := hne.imp fun j h => h.2
  have hj₀lt : Nat.find hne2 < s.card := by
    obtain ⟨j, hjlt, hj⟩ := hne
    exact lt_of_le_of_lt (Nat.find_le hj) hjlt
  -- coefficient bounds
  have habs : ∀ j, |(esymmShift x₀ s j : ℝ) - (esymmShift x₀ s' j : ℝ)|
      ≤ (2:ℝ) ^ (K + 1) * (H:ℝ) ^ j := by
    intro j
    have h1 : esymmShift x₀ s j ≤ 2 ^ K * H ^ j :=
      le_trans (esymmShift_le (fun p hp => (hs p hp).2) j)
        (Nat.mul_le_mul (Nat.pow_le_pow_right (by norm_num) hK) le_rfl)
    have h2 : esymmShift x₀ s' j ≤ 2 ^ K * H ^ j := by
      have h3 := esymmShift_le (fun p hp => (hs' p hp).2) j
      rw [← hcard] at h3
      exact le_trans h3 (Nat.mul_le_mul (Nat.pow_le_pow_right (by norm_num) hK) le_rfl)
    have h1' : (esymmShift x₀ s j : ℝ) ≤ (2:ℝ) ^ K * (H:ℝ) ^ j := by exact_mod_cast h1
    have h2' : (esymmShift x₀ s' j : ℝ) ≤ (2:ℝ) ^ K * (H:ℝ) ^ j := by exact_mod_cast h2
    have hn1 : (0:ℝ) ≤ (esymmShift x₀ s j : ℝ) := Nat.cast_nonneg _
    have hn2 : (0:ℝ) ≤ (esymmShift x₀ s' j : ℝ) := Nat.cast_nonneg _
    have hpow2 : (2:ℝ) ^ (K + 1) * (H:ℝ) ^ j = 2 * ((2:ℝ) ^ K * (H:ℝ) ^ j) := by ring
    rw [hpow2, abs_le]
    constructor <;> linarith
  -- the size hypothesis, in the form the helper needs
  have hnat : 2 ^ (K + 3) * H ^ (Nat.find hne2 + 1) ≤ x₀ := by
    have h1 : H ^ (Nat.find hne2 + 1) ≤ H ^ (K + 1) :=
      Nat.pow_le_pow_right hH (by omega)
    have h2 : (2:ℕ) ^ (K + 3) ≤ 2 ^ (K + 4) := Nat.pow_le_pow_right (by norm_num) (by omega)
    calc 2 ^ (K + 3) * H ^ (Nat.find hne2 + 1) ≤ 2 ^ (K + 4) * H ^ (K + 1) :=
          Nat.mul_le_mul h2 h1
      _ = 8 * (2 * H) ^ (K + 1) := by rw [Nat.mul_pow]; ring
      _ ≤ x₀ := hbig
  rw [hD]
  refine abs_expansion_ge (x := (x₀:ℝ)) (C := (2:ℝ)^(K+1)) (Hb := (H:ℝ)) (k := s.card)
      (j₀ := Nat.find hne2)
      (fun j => (esymmShift x₀ s j : ℝ) - (esymmShift x₀ s' j : ℝ))
      ?_ (Nat.cast_nonneg H) ?_ (by positivity) hj₀lt ?_ ?_ ?_ ?_
  · exact_mod_cast hx1
  · exact_mod_cast h2Hx
  · intro i hi
    have heqi : esymmShift x₀ s i = esymmShift x₀ s' i := not_ne_iff.1 (Nat.find_min hne2 hi)
    simp [heqi]
  · exact one_le_abs_natCast_sub (Nat.find_spec hne2)
  · intro j _
    exact habs j
  · have hcast : ((2:ℝ) ^ (K + 3) * (H:ℝ) ^ (Nat.find hne2 + 1)) ≤ (x₀:ℝ) := by
      exact_mod_cast hnat
    calc 4 * ((2:ℝ) ^ (K + 1) * (H:ℝ) ^ (Nat.find hne2 + 1))
        = (2:ℝ) ^ (K + 3) * (H:ℝ) ^ (Nat.find hne2 + 1) := by ring
      _ ≤ (x₀:ℝ) := hcast

end Erdos884
end

/-! Flattened from Erdos884/TauSingular884.lean. -/
section

/-!
# Erdős 884 — Lemma B auxiliary sums (TauBound and B.4)

Exports:
* `sum_inv_le_one_add_log` : `∑_{1 ≤ e ≤ y} 1/e ≤ 1 + log y`
* `sum_pow_primeFactors_le` : `∑_{1 ≤ d ≤ y} c^{ω(d)} ≤ y (1 + log y)^{c-1}` for `c ≥ 1`
* `sum_totient_ratio_sq_le` : `∑_{1 ≤ h ≤ N} (h/φ(h))² ≤ 200 N`
-/

namespace Erdos884

/-! ### Harmonic sum: `∑_{e ≤ y} 1/e ≤ 1 + log y` -/

lemma one_add_log_natCast_nonneg (y : ℕ) : (0:ℝ) ≤ 1 + Real.log y := by
  have := Real.log_natCast_nonneg y
  linarith

theorem sum_inv_le_one_add_log (y : ℕ) :
    ∑ e ∈ Finset.Icc 1 y, ((e:ℝ))⁻¹ ≤ 1 + Real.log y := by
  have h1 : ((harmonic y : ℚ) : ℝ) = ∑ e ∈ Finset.Icc 1 y, ((e:ℝ))⁻¹ := by
    rw [harmonic_eq_sum_Icc]
    push_cast
    rfl
  rw [← h1]
  exact_mod_cast harmonic_le_one_add_log y

/-! ### Telescoping: `∑_{2 ≤ n ≤ M} 2/(n-1)² ≤ 4 - 4/M` -/

lemma sum_two_div_sq_le (M : ℕ) (hM : 1 ≤ M) :
    ∑ n ∈ Finset.Icc 2 M, 2 / (((n:ℝ) - 1) ^ 2) ≤ 4 - 4 / (M:ℝ) := by
  induction M, hM using Nat.le_induction with
  | base =>
    rw [Finset.Icc_eq_empty (by omega)]
    norm_num
  | succ M hM ih =>
    rw [Finset.sum_Icc_succ_top (by omega : 2 ≤ M + 1)]
    have hM' : (1:ℝ) ≤ (M:ℝ) := by exact_mod_cast hM
    have hM0 : (0:ℝ) < (M:ℝ) := by linarith
    have hM1 : (0:ℝ) < (M:ℝ) + 1 := by linarith
    have key : 2 / ((M:ℝ)) ^ 2 ≤ 4 / (M:ℝ) - 4 / ((M:ℝ) + 1) := by
      rw [div_sub_div _ _ hM0.ne' hM1.ne']
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [sq_nonneg ((M:ℝ) - 1)]
    push_cast
    have e1 : (M:ℝ) + 1 - 1 = (M:ℝ) := by ring
    rw [e1]
    linarith [ih]

/-! ### Pointwise bound `(c+1)^{ω d} ≤ ∑_{e ∣ d} c^{ω e}` -/

lemma pow_card_powerset_expand (c : ℕ) (P : Finset ℕ) :
    ((c:ℝ) + 1) ^ P.card = ∑ S ∈ P.powerset, (c:ℝ) ^ S.card := by
  classical
  calc ((c:ℝ) + 1) ^ P.card
      = ∏ _p ∈ P, ((c:ℝ) + 1) := by rw [Finset.prod_const]
    _ = ∑ S ∈ P.powerset, (∏ _p ∈ S, (c:ℝ)) * ∏ _p ∈ P \ S, 1 := Finset.prod_add _ _ _
    _ = ∑ S ∈ P.powerset, (c:ℝ) ^ S.card := by simp [Finset.prod_const]

lemma pow_omega_le_sum_divisors (c : ℕ) {d : ℕ} (hd : d ≠ 0) :
    ((c:ℝ) + 1) ^ d.primeFactors.card
      ≤ ∑ e ∈ d.divisors, (c:ℝ) ^ e.primeFactors.card := by
  classical
  have hprime : ∀ S ∈ d.primeFactors.powerset, ∀ p ∈ S, Nat.Prime p := fun S hS p hp =>
    Nat.prime_of_mem_primeFactors (Finset.mem_powerset.mp hS hp)
  have hinj : Set.InjOn (fun S : Finset ℕ => ∏ p ∈ S, p) ↑d.primeFactors.powerset := by
    intro S hS T hT hST
    rw [Finset.mem_coe] at hS hT
    have h1 := Nat.primeFactors_prod (hprime S hS)
    have h2 := Nat.primeFactors_prod (hprime T hT)
    dsimp only at hST
    rw [← h1, ← h2, hST]
  calc ((c:ℝ) + 1) ^ d.primeFactors.card
      = ∑ S ∈ d.primeFactors.powerset, (c:ℝ) ^ S.card := pow_card_powerset_expand c _
    _ = ∑ S ∈ d.primeFactors.powerset, (c:ℝ) ^ (∏ p ∈ S, p).primeFactors.card :=
        Finset.sum_congr rfl fun S hS => by rw [Nat.primeFactors_prod (hprime S hS)]
    _ = ∑ e ∈ d.primeFactors.powerset.image (fun S => ∏ p ∈ S, p),
          (c:ℝ) ^ e.primeFactors.card :=
        (Finset.sum_image (f := fun e => (c:ℝ) ^ e.primeFactors.card) hinj).symm
    _ ≤ ∑ e ∈ d.divisors, (c:ℝ) ^ e.primeFactors.card := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro e he
          rw [Finset.mem_image] at he
          obtain ⟨S, hS, rfl⟩ := he
          rw [Nat.mem_divisors]
          exact ⟨(Finset.prod_dvd_prod_of_subset S d.primeFactors (fun p => p)
            (Finset.mem_powerset.mp hS)).trans (Nat.prod_primeFactors_dvd d), hd⟩
        · intro e _ _
          positivity

/-! ### Hyperbola-style swap for `∑_{d ≤ y} ∑_{ef = d}` -/

lemma sum_sum_divisorsAntidiagonal_le (F : ℕ → ℝ) (hF : ∀ n, 0 ≤ F n) (y : ℕ) :
    ∑ d ∈ Finset.Icc 1 y, ∑ p ∈ d.divisorsAntidiagonal, F p.2
      ≤ ∑ e ∈ Finset.Icc 1 y, ∑ f ∈ Finset.Icc 1 (y / e), F f := by
  classical
  have swap : ∑ d ∈ Finset.Icc 1 y, ∑ p ∈ d.divisorsAntidiagonal, F p.2
      = ∑ p ∈ (Finset.Icc 1 y ×ˢ Finset.Icc 1 y).filter (fun p : ℕ × ℕ => p.1 * p.2 ≤ y),
          ∑ _d ∈ ({p.1 * p.2} : Finset ℕ), F p.2 := by
    apply Finset.sum_comm'
    intro d p
    simp only [Nat.mem_divisorsAntidiagonal, Finset.mem_Icc, Finset.mem_filter,
      Finset.mem_product, Finset.mem_singleton]
    constructor
    · rintro ⟨⟨hd1, hd2⟩, heq, hne⟩
      have hp1 : 1 ≤ p.1 := Nat.one_le_iff_ne_zero.mpr fun h => hne (by rw [← heq, h, zero_mul])
      have hp2 : 1 ≤ p.2 := Nat.one_le_iff_ne_zero.mpr fun h => hne (by rw [← heq, h, mul_zero])
      have hle1 : p.1 ≤ y :=
        le_trans (le_trans (le_mul_of_one_le_right (Nat.zero_le _) hp2) heq.le) hd2
      have hle2 : p.2 ≤ y :=
        le_trans (le_trans (le_mul_of_one_le_left (Nat.zero_le _) hp1) heq.le) hd2
      exact ⟨heq.symm, ⟨⟨hp1, hle1⟩, hp2, hle2⟩, le_of_eq_of_le heq hd2⟩
    · rintro ⟨hdeq, ⟨⟨hp11, hp12⟩, hp21, hp22⟩, hmul⟩
      subst hdeq
      refine ⟨⟨?_, hmul⟩, rfl, ?_⟩
      · exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
      · exact Nat.mul_ne_zero (by omega) (by omega)
  have hdisj : (↑(Finset.Icc 1 y) : Set ℕ).PairwiseDisjoint
      (fun e => ({e} : Finset ℕ) ×ˢ Finset.Icc 1 (y / e)) := by
    intro e1 _ e2 _ hne
    simp only [Function.onFun]
    rw [Finset.disjoint_left]
    rintro ⟨a, b⟩ h1 h2
    simp only [Finset.mem_product, Finset.mem_singleton] at h1 h2
    exact hne (h1.1.symm.trans h2.1)
  have hTU : (Finset.Icc 1 y ×ˢ Finset.Icc 1 y).filter (fun p : ℕ × ℕ => p.1 * p.2 ≤ y)
      = (Finset.Icc 1 y).biUnion (fun e => ({e} : Finset ℕ) ×ˢ Finset.Icc 1 (y / e)) := by
    ext ⟨a, b⟩
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, Finset.mem_biUnion,
      Finset.mem_singleton]
    constructor
    · rintro ⟨⟨⟨ha1, ha2⟩, hb1, hb2⟩, hab⟩
      exact ⟨a, ⟨ha1, ha2⟩, rfl,
        hb1, (Nat.le_div_iff_mul_le (by omega : 0 < a)).mpr (by rw [mul_comm]; exact hab)⟩
    · rintro ⟨e, ⟨he1, he2⟩, rfl, hb1, hb2⟩
      have hba : b * a ≤ y := (Nat.le_div_iff_mul_le (by omega : 0 < a)).mp hb2
      exact ⟨⟨⟨he1, he2⟩, hb1, le_trans hb2 (Nat.div_le_self y a)⟩,
        by rw [mul_comm]; exact hba⟩
  rw [swap]
  simp only [Finset.sum_singleton]
  rw [hTU, Finset.sum_biUnion hdisj]
  apply le_of_eq
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [Finset.sum_product]
  simp

/-! ### TauBound: `∑_{d ≤ y} c^{ω(d)} ≤ y (1 + log y)^{c-1}` -/

theorem sum_pow_primeFactors_le (c y : ℕ) (hc : 1 ≤ c) :
    ∑ d ∈ Finset.Icc 1 y, (c:ℝ) ^ (d.primeFactors.card) ≤ (y:ℝ) * (1 + Real.log y)^(c-1) := by
  induction c, hc using Nat.le_induction generalizing y with
  | base => simp [Nat.card_Icc]
  | succ c hc ih =>
    have step1 : ∑ d ∈ Finset.Icc 1 y, ((c:ℝ) + 1) ^ d.primeFactors.card
        ≤ ∑ d ∈ Finset.Icc 1 y, ∑ p ∈ d.divisorsAntidiagonal, (c:ℝ) ^ p.2.primeFactors.card := by
      apply Finset.sum_le_sum
      intro d hd
      rw [Finset.mem_Icc] at hd
      have hconv : ∑ p ∈ d.divisorsAntidiagonal, (c:ℝ) ^ p.2.primeFactors.card
          = ∑ e ∈ d.divisors, (c:ℝ) ^ e.primeFactors.card := by
        rw [Nat.sum_divisorsAntidiagonal (M := ℝ)
          (fun _ j => (c:ℝ) ^ j.primeFactors.card) (n := d)]
        exact Nat.sum_div_divisors (α := ℝ) d (fun e => (c:ℝ) ^ e.primeFactors.card)
      rw [hconv]
      exact pow_omega_le_sum_divisors c (by omega)
    have step2 := sum_sum_divisorsAntidiagonal_le (fun n => (c:ℝ) ^ n.primeFactors.card)
      (fun n => by positivity) y
    have step3 : ∑ e ∈ Finset.Icc 1 y, ∑ f ∈ Finset.Icc 1 (y / e), (c:ℝ) ^ f.primeFactors.card
        ≤ ∑ e ∈ Finset.Icc 1 y, (y:ℝ) / e * (1 + Real.log y) ^ (c - 1) := by
      apply Finset.sum_le_sum
      intro e he
      rw [Finset.mem_Icc] at he
      have h1 : (((y / e : ℕ)):ℝ) ≤ (y:ℝ) / e := Nat.cast_div_le
      have hde : 1 ≤ y / e := (Nat.one_le_div_iff (by omega)).mpr he.2
      have h2 : Real.log ((y / e : ℕ):ℝ) ≤ Real.log (y:ℝ) := by
        apply Real.log_le_log
        · exact_mod_cast hde
        · exact_mod_cast Nat.div_le_self y e
      have h3 : (0:ℝ) ≤ 1 + Real.log ((y / e : ℕ):ℝ) := one_add_log_natCast_nonneg _
      calc ∑ f ∈ Finset.Icc 1 (y / e), (c:ℝ) ^ f.primeFactors.card
          ≤ ((y / e : ℕ):ℝ) * (1 + Real.log ((y / e : ℕ):ℝ)) ^ (c - 1) := ih (y / e)
        _ ≤ (y:ℝ) / e * (1 + Real.log (y:ℝ)) ^ (c - 1) := by
            apply mul_le_mul h1 _ (pow_nonneg h3 _) (by positivity)
            exact pow_le_pow_left₀ h3 (by linarith) _
    have step5 : ∑ e ∈ Finset.Icc 1 y, (y:ℝ) / e * (1 + Real.log y) ^ (c - 1)
        ≤ (y:ℝ) * (1 + Real.log y) ^ c := by
      have h0 : (0:ℝ) ≤ 1 + Real.log y := one_add_log_natCast_nonneg y
      have hb : (0:ℝ) ≤ (y:ℝ) * (1 + Real.log y) ^ (c - 1) :=
        mul_nonneg (Nat.cast_nonneg y) (pow_nonneg h0 _)
      have hrw : ∑ e ∈ Finset.Icc 1 y, (y:ℝ) / e * (1 + Real.log y) ^ (c - 1)
          = (y:ℝ) * (1 + Real.log y) ^ (c - 1) * ∑ e ∈ Finset.Icc 1 y, ((e:ℝ))⁻¹ := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun e _ => ?_
        rw [div_eq_mul_inv]
        ring
      rw [hrw]
      calc (y:ℝ) * (1 + Real.log y) ^ (c - 1) * ∑ e ∈ Finset.Icc 1 y, ((e:ℝ))⁻¹
          ≤ (y:ℝ) * (1 + Real.log y) ^ (c - 1) * (1 + Real.log y) :=
            mul_le_mul_of_nonneg_left (sum_inv_le_one_add_log y) hb
        _ = (y:ℝ) * (1 + Real.log y) ^ (c - 1 + 1) := by rw [pow_succ]; ring
        _ = (y:ℝ) * (1 + Real.log y) ^ c := by rw [Nat.sub_add_cancel hc]
    rw [Nat.add_sub_cancel]
    push_cast
    exact le_trans step1 (le_trans step2 (le_trans step3 step5))

/-! ### B.4: `∑_{h ≤ N} (h/φ(h))² ≤ 200 N` -/

/-- The weight `(2p-1)/(p-1)²`, so that `(p/(p-1))² = 1 + totientWeight p`. -/
noncomputable def totientWeight (p : ℕ) : ℝ := (2 * (p:ℝ) - 1) / ((p:ℝ) - 1) ^ 2

lemma totientWeight_nonneg {p : ℕ} (hp : 2 ≤ p) : 0 ≤ totientWeight p := by
  have h2 : (2:ℝ) ≤ (p:ℝ) := by exact_mod_cast hp
  unfold totientWeight
  apply div_nonneg
  · linarith
  · positivity

/-- Expansion of a product of `1 + g p` as a sum over subsets. -/
lemma prod_one_add_expand (P : Finset ℕ) (g : ℕ → ℝ) :
    ∏ p ∈ P, (1 + g p) = ∑ S ∈ P.powerset, ∏ p ∈ S, g p := by
  classical
  calc ∏ p ∈ P, (1 + g p)
      = ∏ p ∈ P, (g p + 1) := Finset.prod_congr rfl fun p _ => add_comm 1 (g p)
    _ = ∑ S ∈ P.powerset, (∏ p ∈ S, g p) * ∏ p ∈ P \ S, 1 := Finset.prod_add _ _ _
    _ = ∑ S ∈ P.powerset, ∏ p ∈ S, g p := by simp

/-- `(h/φ(h))² = ∏_{p ∣ h} (1 + (2p-1)/(p-1)²)`. -/
lemma totient_ratio_sq_eq_prod {h : ℕ} (hh : 1 ≤ h) :
    ((h:ℝ) / (Nat.totient h)) ^ 2 = ∏ p ∈ h.primeFactors, (1 + totientWeight p) := by
  have hφpos : 0 < Nat.totient h := Nat.totient_pos.mpr (by omega)
  have hφ : (0:ℝ) < (Nat.totient h : ℝ) := by exact_mod_cast hφpos
  have hfac : ∀ p ∈ h.primeFactors, (2:ℝ) ≤ (p:ℝ) := fun p hp => by
    exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
  have hprodpos : (0:ℝ) < ∏ p ∈ h.primeFactors, ((p:ℝ) - 1) := by
    apply Finset.prod_pos
    intro p hp
    have := hfac p hp
    linarith
  have hkeyR : (Nat.totient h : ℝ) * ∏ p ∈ h.primeFactors, (p:ℝ)
      = (h:ℝ) * ∏ p ∈ h.primeFactors, ((p:ℝ) - 1) := by
    have hcast : ∏ p ∈ h.primeFactors, ((p:ℝ) - 1)
        = ((∏ p ∈ h.primeFactors, (p - 1) : ℕ) : ℝ) := by
      push_cast
      refine Finset.prod_congr rfl fun p hp => ?_
      rw [Nat.cast_pred (Nat.prime_of_mem_primeFactors hp).pos]
    have hcast2 : ∏ p ∈ h.primeFactors, (p:ℝ) = ((∏ p ∈ h.primeFactors, p : ℕ) : ℝ) := by
      push_cast
      rfl
    rw [hcast, hcast2]
    exact_mod_cast congrArg (Nat.cast (R := ℝ)) (Nat.totient_mul_prod_primeFactors h)
  have hratio : (h:ℝ) / (Nat.totient h : ℝ)
      = ∏ p ∈ h.primeFactors, ((p:ℝ) / ((p:ℝ) - 1)) := by
    rw [Finset.prod_div_distrib]
    rw [div_eq_div_iff hφ.ne' hprodpos.ne']
    linear_combination -hkeyR
  rw [hratio, ← Finset.prod_pow]
  refine Finset.prod_congr rfl fun p hp => ?_
  have h2 := hfac p hp
  have hne : (p:ℝ) - 1 ≠ 0 := by linarith
  unfold totientWeight
  field_simp
  ring

/-- Swap the sum over `h` and over subsets of prime factors of `h`. -/
lemma totient_powerset_swap (N : ℕ) (g : Finset ℕ → ℝ) :
    ∑ h ∈ Finset.Icc 1 N, ∑ S ∈ h.primeFactors.powerset, g S
      = ∑ S ∈ ((Finset.Icc 1 N).filter Nat.Prime).powerset,
          ∑ h ∈ (Finset.Icc 1 N).filter (fun h => (∏ p ∈ S, p) ∣ h), g S := by
  classical
  apply Finset.sum_comm'
  intro h S
  simp only [Finset.mem_Icc, Finset.mem_powerset, Finset.mem_filter]
  constructor
  · rintro ⟨⟨h1, h2⟩, hS⟩
    refine ⟨⟨⟨h1, h2⟩, ?_⟩, ?_⟩
    · exact (Finset.prod_dvd_prod_of_subset S h.primeFactors (fun p => p) hS).trans
        (Nat.prod_primeFactors_dvd h)
    · intro p hp
      have hp' := hS hp
      rw [Nat.mem_primeFactors] at hp'
      obtain ⟨hpp, hpd, -⟩ := hp'
      rw [Finset.mem_filter, Finset.mem_Icc]
      exact ⟨⟨hpp.one_lt.le, (Nat.le_of_dvd (by omega) hpd).trans h2⟩, hpp⟩
  · rintro ⟨⟨⟨h1, h2⟩, hdvd⟩, hS⟩
    refine ⟨⟨h1, h2⟩, ?_⟩
    intro p hp
    have hpP := hS hp
    rw [Finset.mem_filter] at hpP
    rw [Nat.mem_primeFactors]
    exact ⟨hpP.2, dvd_trans (Finset.dvd_prod_of_mem (fun p => p) hp) hdvd, by omega⟩

lemma exp_four_le_55 : Real.exp 4 ≤ 55 := by
  have h1 : Real.exp 1 ≤ 2.7182818286 := Real.exp_one_lt_d9.le
  have h4 : Real.exp 4 = Real.exp 1 ^ 4 := by
    rw [Real.exp_one_pow]
    norm_num
  rw [h4]
  calc Real.exp 1 ^ 4 ≤ (2.7182818286:ℝ) ^ 4 :=
        pow_le_pow_left₀ (Real.exp_pos 1).le h1 4
    _ ≤ 55 := by norm_num

theorem sum_totient_ratio_sq_le (N : ℕ) :
    ∑ h ∈ Finset.Icc 1 N, ((h:ℝ) / (Nat.totient h))^2 ≤ 200 * N := by
  classical
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp
  have hN0 : (0:ℝ) ≤ (N:ℝ) := Nat.cast_nonneg N
  set P := (Finset.Icc 1 N).filter Nat.Prime with hPdef
  have hPprime : ∀ p ∈ P, Nat.Prime p := fun p hp => (Finset.mem_filter.mp hp).2
  have hSprime : ∀ S ∈ P.powerset, ∀ p ∈ S, Nat.Prime p := fun S hS p hp =>
    hPprime p (Finset.mem_powerset.mp hS hp)
  have hwtS : ∀ S ∈ P.powerset, 0 ≤ ∏ p ∈ S, totientWeight p := fun S hS =>
    Finset.prod_nonneg fun p hp => totientWeight_nonneg (hSprime S hS p hp).two_le
  -- the exponent bound
  have hexp4 : ∑ p ∈ P, totientWeight p / (p:ℝ) ≤ 4 := by
    have hstep : ∀ p ∈ P, totientWeight p / (p:ℝ) ≤ 2 / (((p:ℝ) - 1) ^ 2) := by
      intro p hp
      have h2 : (2:ℝ) ≤ (p:ℝ) := by exact_mod_cast (hPprime p hp).two_le
      have hp1 : (0:ℝ) < (p:ℝ) - 1 := by linarith
      have hp0 : (0:ℝ) < (p:ℝ) := by linarith
      unfold totientWeight
      rw [div_div, div_le_div_iff₀ (mul_pos (pow_pos hp1 2) hp0) (pow_pos hp1 2)]
      nlinarith [sq_nonneg ((p:ℝ) - 1)]
    calc ∑ p ∈ P, totientWeight p / (p:ℝ)
        ≤ ∑ p ∈ P, 2 / (((p:ℝ) - 1) ^ 2) := Finset.sum_le_sum hstep
      _ ≤ ∑ n ∈ Finset.Icc 2 N, 2 / (((n:ℝ) - 1) ^ 2) := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro p hp
            rw [Finset.mem_Icc]
            exact ⟨(hPprime p hp).two_le, (Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).2⟩
          · intro n _ _
            positivity
      _ ≤ 4 - 4 / (N:ℝ) := sum_two_div_sq_le N hN
      _ ≤ 4 := by
          have : (0:ℝ) ≤ 4 / (N:ℝ) := by positivity
          linarith
  -- rewrite the summand and swap
  have hstep1 : ∑ h ∈ Finset.Icc 1 N, ((h:ℝ) / (Nat.totient h)) ^ 2
      = ∑ S ∈ P.powerset, ∑ h ∈ (Finset.Icc 1 N).filter (fun h => (∏ p ∈ S, p) ∣ h),
          ∏ p ∈ S, totientWeight p := by
    rw [← totient_powerset_swap N (fun S => ∏ p ∈ S, totientWeight p)]
    refine Finset.sum_congr rfl fun h hh => ?_
    rw [totient_ratio_sq_eq_prod (Finset.mem_Icc.mp hh).1, prod_one_add_expand]
  -- count multiples of ∏ S
  have hcount : ∀ S ∈ P.powerset,
      ∑ h ∈ (Finset.Icc 1 N).filter (fun h => (∏ p ∈ S, p) ∣ h), ∏ p ∈ S, totientWeight p
        = ((N / ∏ p ∈ S, p : ℕ) : ℝ) * ∏ p ∈ S, totientWeight p := by
    intro S _
    rw [Finset.sum_const]
    rw [show Finset.Icc 1 N = Finset.Ioc 0 N from rfl, Nat.Ioc_filter_dvd_card_eq_div]
    rw [nsmul_eq_mul]
  rw [hstep1, Finset.sum_congr rfl hcount]
  calc ∑ S ∈ P.powerset, ((N / ∏ p ∈ S, p : ℕ) : ℝ) * ∏ p ∈ S, totientWeight p
      ≤ ∑ S ∈ P.powerset, (N:ℝ) * ∏ p ∈ S, (totientWeight p / (p:ℝ)) := by
        apply Finset.sum_le_sum
        intro S hS
        have h1 : ((N / ∏ p ∈ S, p : ℕ) : ℝ) ≤ (N:ℝ) / ((∏ p ∈ S, p : ℕ) : ℝ) :=
          Nat.cast_div_le
        calc ((N / ∏ p ∈ S, p : ℕ) : ℝ) * ∏ p ∈ S, totientWeight p
            ≤ (N:ℝ) / ((∏ p ∈ S, p : ℕ) : ℝ) * ∏ p ∈ S, totientWeight p :=
              mul_le_mul_of_nonneg_right h1 (hwtS S hS)
          _ = (N:ℝ) * ∏ p ∈ S, (totientWeight p / (p:ℝ)) := by
              rw [Nat.cast_prod, Finset.prod_div_distrib]
              ring
    _ = (N:ℝ) * ∑ S ∈ P.powerset, ∏ p ∈ S, (totientWeight p / (p:ℝ)) := by
        rw [Finset.mul_sum]
    _ = (N:ℝ) * ∏ p ∈ P, (1 + totientWeight p / (p:ℝ)) := by
        rw [prod_one_add_expand]
    _ ≤ (N:ℝ) * ∏ p ∈ P, Real.exp (totientWeight p / (p:ℝ)) := by
        apply mul_le_mul_of_nonneg_left _ hN0
        apply Finset.prod_le_prod
        · intro p hp
          have hw := totientWeight_nonneg (hPprime p hp).two_le
          have hp0 : (0:ℝ) < (p:ℝ) := by exact_mod_cast (hPprime p hp).pos
          positivity
        · intro p hp
          have := Real.add_one_le_exp (totientWeight p / (p:ℝ))
          linarith
    _ = (N:ℝ) * Real.exp (∑ p ∈ P, totientWeight p / (p:ℝ)) := by
        rw [Real.exp_sum]
    _ ≤ (N:ℝ) * Real.exp 4 :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp4) hN0
    _ ≤ 200 * (N:ℝ) := by
        nlinarith [exp_four_le_55, hN0, Real.exp_pos (4:ℝ)]

end Erdos884
end

/-! Flattened from Erdos884/Chebyshev884.lean. -/
section

/-!
# Erdős 884 — Lemma A: Chebyshev-type lower bound for primes in `(t, 8t]`

We prove `primesBetween_lower`: there is a threshold `T ≥ 3` such that for all `t ≥ T`
the interval `(⌊t⌋₊, ⌊8t⌋₊]` contains at least `2t / log t` primes.

Route: `Chebyshev.pi_ge'` at `8t` gives a lower bound for `π(⌊8t⌋₊)`, and
`Chebyshev.eventually_primeCounting_le` (with `ε = 1/10`) an upper bound for `π(⌊t⌋₊)`;
the count of primes in the interval is exactly `π(⌊8t⌋₊) - π(⌊t⌋₊)`.
-/

namespace Erdos884

/-- Counting primes in `(a, b]`: `π a + #{primes in (a,b]} = π b`. -/
lemma primeCounting_add_card_Ioc {a b : ℕ} (h : a ≤ b) :
    a.primeCounting + ((Finset.Ioc a b).filter Nat.Prime).card = b.primeCounting := by
  have key : ∀ n : ℕ, n.primeCounting = ((Finset.Iic n).filter Nat.Prime).card := by
    intro n
    rw [Nat.primeCounting, Nat.primeCounting', Nat.count_eq_card_filter_range,
      Nat.range_succ_eq_Iic]
  have hdisj : Disjoint ((Finset.Iic a).filter Nat.Prime)
      ((Finset.Ioc a b).filter Nat.Prime) := by
    rw [Finset.disjoint_left]
    intro x hx hx'
    simp only [Finset.mem_filter, Finset.mem_Iic] at hx
    simp only [Finset.mem_filter, Finset.mem_Ioc] at hx'
    omega
  rw [key a, key b, ← Finset.card_union_of_disjoint hdisj, ← Finset.filter_union,
    Finset.Iic_union_Ioc_eq_Iic h]

/-- The core algebraic inequality behind Lemma A, with `c = log 2`, `L = log t`,
`M = log (8t)`, `E = log (8t+2)` abstracted into real variables. -/
lemma core_ineq {t c L M E : ℝ} (ht : 36 ≤ t) (hc1 : (0.69 : ℝ) ≤ c) (hc2 : c ≤ 0.7)
    (hL0 : 0 < L) (hML : 20 * M ≤ 21 * L) (hE : E ≤ 2 * L) (hLt : 3 * L ≤ t) :
    (2 + (2 * c + 1/10)) * t * M ≤ ((8 * t - 1) * c - E) * L := by
  have ht0 : (0 : ℝ) ≤ t := by linarith
  have step1 : (2 + (2 * c + 1/10)) * t * M
      ≤ (2 + (2 * c + 1/10)) * t * ((21/20) * L) := by
    have h1 : (0 : ℝ) ≤ (2 + (2 * c + 1/10)) * t := by nlinarith
    have h2 : M ≤ (21/20) * L := by linarith
    exact mul_le_mul_of_nonneg_left h2 h1
  have step2 : ((8 * t - 1) * c - 2 * L) * L ≤ ((8 * t - 1) * c - E) * L := by
    apply mul_le_mul_of_nonneg_right _ hL0.le
    linarith
  refine step1.trans (le_trans ?_ step2)
  have hct : 0.69 * t ≤ c * t := mul_le_mul_of_nonneg_right hc1 ht0
  have key : (2 + (2 * c + 1/10)) * t * (21/20) ≤ (8 * t - 1) * c - 2 * L := by
    nlinarith
  calc (2 + (2 * c + 1/10)) * t * ((21/20) * L)
      = ((2 + (2 * c + 1/10)) * t * (21/20)) * L := by ring
    _ ≤ ((8 * t - 1) * c - 2 * L) * L := mul_le_mul_of_nonneg_right key hL0.le

/-- **Lemma A.** For all sufficiently large `t`, the interval `(⌊t⌋₊, ⌊8t⌋₊]` contains
at least `2t / log t` primes. -/
theorem primesBetween_lower :
    ∃ T : ℝ, 3 ≤ T ∧ ∀ t : ℝ, T ≤ t →
      2 * t / Real.log t ≤ (((Finset.Ioc ⌊t⌋₊ ⌊8*t⌋₊)).filter Nat.Prime).card := by
  obtain ⟨T₄, hT₄⟩ := Filter.eventually_atTop.mp
    (Chebyshev.eventually_primeCounting_le (show (0:ℝ) < 1/10 by norm_num))
  refine ⟨max (max T₄ ((2:ℝ)^60)) 36, le_trans (by norm_num) (le_max_right _ _), ?_⟩
  intro t hTt
  have ht36 : (36 : ℝ) ≤ t := le_trans (le_max_right _ _) hTt
  have ht4 : T₄ ≤ t := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hTt
  have ht60 : (2:ℝ)^60 ≤ t := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hTt
  have ht0 : (0 : ℝ) < t := by linarith
  have hL0 : 0 < Real.log t := Real.log_pos (by linarith)
  have hc1 : (0.69 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hc2 : Real.log 2 ≤ 0.7 := by linarith [Real.log_two_lt_d9]
  -- log t ≥ 60 log 2
  have hL60 : 60 * Real.log 2 ≤ Real.log t := by
    have h1 : Real.log ((2:ℝ)^60) ≤ Real.log t := Real.log_le_log (by positivity) ht60
    rwa [Real.log_pow, Nat.cast_ofNat] at h1
  -- 3 log t ≤ t
  have hLt : 3 * Real.log t ≤ t := by
    have hsqrt6 : (6 : ℝ) ≤ Real.sqrt t := by
      rw [show (6:ℝ) = Real.sqrt (6^2) from (Real.sqrt_sq (by norm_num)).symm]
      exact Real.sqrt_le_sqrt (by nlinarith : (6:ℝ)^2 ≤ t)
    have h1 : Real.log (Real.sqrt t) ≤ Real.sqrt t - 1 :=
      Real.log_le_sub_one_of_pos (by positivity)
    have h2 : Real.log (Real.sqrt t) = Real.log t / 2 := Real.log_sqrt ht0.le
    have h3 : Real.sqrt t * Real.sqrt t = t := Real.mul_self_sqrt ht0.le
    have h4 : 6 * Real.sqrt t ≤ Real.sqrt t * Real.sqrt t :=
      mul_le_mul_of_nonneg_right hsqrt6 (Real.sqrt_nonneg t)
    linarith
  -- log (8t) = 3 log 2 + log t
  have hM_eq : Real.log (8*t) = 3 * Real.log 2 + Real.log t := by
    rw [Real.log_mul (by norm_num) (ne_of_gt ht0), show (8:ℝ) = 2^3 by norm_num,
      Real.log_pow]
    norm_num
  have hM0 : 0 < Real.log (8*t) := by rw [hM_eq]; linarith
  have hML : 20 * Real.log (8*t) ≤ 21 * Real.log t := by rw [hM_eq]; linarith
  -- log (8t+2) ≤ 2 log t
  have hE : Real.log (8*t+2) ≤ 2 * Real.log t := by
    have h1 : Real.log (8*t+2) ≤ Real.log (16*t) :=
      Real.log_le_log (by linarith) (by linarith)
    have h2 : Real.log (16*t) = 4 * Real.log 2 + Real.log t := by
      rw [Real.log_mul (by norm_num) (ne_of_gt ht0), show (16:ℝ) = 2^4 by norm_num,
        Real.log_pow]
      norm_num
    linarith
  -- the two prime-counting estimates
  have hpi8 : ((8*t - 1) * Real.log 2 - Real.log (8*t + 2)) / Real.log (8*t)
      ≤ (Nat.primeCounting ⌊8*t⌋₊ : ℝ) := Chebyshev.pi_ge' (by linarith)
  have hpit : (Nat.primeCounting ⌊t⌋₊ : ℝ) ≤ (Real.log 4 + 1/10) * t / Real.log t := hT₄ t ht4
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4:ℝ) = 2^2 by norm_num, Real.log_pow]
    norm_num
  rw [hlog4] at hpit
  -- the counting bridge
  have hbridge : (Nat.primeCounting ⌊t⌋₊ : ℝ)
      + ((((Finset.Ioc ⌊t⌋₊ ⌊8*t⌋₊)).filter Nat.Prime).card : ℝ)
      = (Nat.primeCounting ⌊8*t⌋₊ : ℝ) := by
    exact_mod_cast primeCounting_add_card_Ioc (Nat.floor_le_floor (by linarith : t ≤ 8*t))
  -- the core estimate, in division form
  have hdiv : (2 + (2 * Real.log 2 + 1/10)) * t / Real.log t
      ≤ ((8*t - 1) * Real.log 2 - Real.log (8*t+2)) / Real.log (8*t) := by
    rw [div_le_div_iff₀ hL0 hM0]
    exact core_ineq ht36 hc1 hc2 hL0 hML hE hLt
  have hexpand : (2 + (2 * Real.log 2 + 1/10)) * t / Real.log t
      = 2 * t / Real.log t + (2 * Real.log 2 + 1/10) * t / Real.log t := by ring
  linarith [hdiv, hpi8, hpit, hbridge, hexpand]

end Erdos884
end

/-! Flattened from Erdos884/Energy884.lean. -/
section

/-!
# Erdős Problem 884 — Lemma D: energy lower bound (Tao eq. (1.2))

For a finite set `A ⊆ ℕ` with `k := |A| ≥ 4` contained in an interval of length `H ≥ 1`,

`pairSum A ≥ k² · log(k/2) / (4H)`.

Proof by chain decomposition: for each index-distance `m ≤ k/2`, split the indices into `m`
arithmetic chains; per chain the consecutive gaps telescope to `≤ H` and Cauchy–Schwarz gives
`Σ 1/gap ≥ L²/H`; Cauchy–Schwarz again over the chains gives `≥ (k−m)²/(mH)`; summing over `m`
and using the harmonic sum lower bound `Σ_{m≤M} 1/m ≥ log(M+1)` finishes.
-/

namespace Erdos884

/-! ### The increasing enumeration of a finset of naturals -/

/-- The `i`-th element (0-based) of `A` in increasing order (junk value for `i ≥ A.card`). -/
def nth (A : Finset ℕ) (i : ℕ) : ℕ := (A.sort (· ≤ ·)).getD i 0

lemma nth_mem (A : Finset ℕ) {i : ℕ} (h : i < A.card) : nth A i ∈ A := by
  have hl : i < (A.sort (· ≤ ·)).length := by
    rw [Finset.length_sort]; exact h
  rw [nth, List.getD_eq_getElem _ _ hl]
  exact (Finset.mem_sort _).1 (List.getElem_mem hl)

lemma nth_lt_nth (A : Finset ℕ) {i j : ℕ} (hij : i < j) (hj : j < A.card) :
    nth A i < nth A j := by
  have hjl : j < (A.sort (· ≤ ·)).length := by
    rw [Finset.length_sort]; exact hj
  have hil : i < (A.sort (· ≤ ·)).length := lt_trans hij hjl
  rw [nth, nth, List.getD_eq_getElem _ _ hil, List.getD_eq_getElem _ _ hjl]
  exact (Finset.sortedLT_sort A).getElem_lt_getElem_of_lt hij

lemma nth_le_nth (A : Finset ℕ) {i j : ℕ} (hij : i ≤ j) (hj : j < A.card) :
    nth A i ≤ nth A j := by
  rcases eq_or_lt_of_le hij with rfl | h
  · exact le_rfl
  · exact (nth_lt_nth A h hj).le

lemma nth_inj (A : Finset ℕ) {i j : ℕ} (hi : i < A.card) (hj : j < A.card)
    (h : nth A i = nth A j) : i = j := by
  rcases lt_trichotomy i j with hlt | heq | hgt
  · exact absurd h (nth_lt_nth A hlt hj).ne
  · exact heq
  · exact absurd h.symm (nth_lt_nth A hgt hi).ne

/- `nth` is only accessed through the API above; make it irreducible so that unification
never tries to evaluate the underlying sorted list. -/
attribute [irreducible] nth

/-! ### Reindexing bound: `pairSum` dominates any injectively indexed family of gaps -/

lemma pairSum_eq_sum_filter (A : Finset ℕ) :
    pairSum A = ∑ p ∈ (A ×ˢ A).filter (fun p => p.1 < p.2), invGap p.1 p.2 := by
  rw [pairSum, pairSumOn]
  congr 1
  ext p
  simp

lemma sum_le_pairSum {ι : Type*} (A : Finset ℕ) (s : Finset ι) (a b : ι → ℕ)
    (hab : ∀ x ∈ s, a x < b x ∧ b x < A.card)
    (hinj : ∀ x ∈ s, ∀ y ∈ s, a x = a y → b x = b y → x = y) :
    ∑ x ∈ s, invGap (nth A (a x)) (nth A (b x)) ≤ pairSum A := by
  classical
  have hinj' : Set.InjOn (fun x => (nth A (a x), nth A (b x))) ↑s := by
    intro x hx y hy hxy
    simp only [Prod.mk.injEq] at hxy
    have hax := hab x (Finset.mem_coe.1 hx)
    have hay := hab y (Finset.mem_coe.1 hy)
    exact hinj x (Finset.mem_coe.1 hx) y (Finset.mem_coe.1 hy)
      (nth_inj A (hax.1.trans hax.2) (hay.1.trans hay.2) hxy.1)
      (nth_inj A hax.2 hay.2 hxy.2)
  calc ∑ x ∈ s, invGap (nth A (a x)) (nth A (b x))
      = ∑ q ∈ s.image (fun x => (nth A (a x), nth A (b x))), invGap q.1 q.2 := by
        rw [Finset.sum_image hinj']
    _ ≤ ∑ p ∈ (A ×ˢ A).filter (fun p => p.1 < p.2), invGap p.1 p.2 := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro q hq
          simp only [Finset.mem_image] at hq
          obtain ⟨x, hx, rfl⟩ := hq
          obtain ⟨h1, h2⟩ := hab x hx
          simp only [Finset.mem_filter, Finset.mem_product]
          exact ⟨⟨nth_mem A (h1.trans h2), nth_mem A h2⟩, nth_lt_nth A h1 h2⟩
        · intro p hp _
          simp only [Finset.mem_filter] at hp
          exact (invGap_pos hp.2).le
    _ = pairSum A := (pairSum_eq_sum_filter A).symm

/-- Specialization of `sum_le_pairSum` to families of index pairs `(m, i) ↦ (i, i + m)`. -/
lemma sum_pairs_le_pairSum (A : Finset ℕ) (P : Finset (ℕ × ℕ))
    (hab : ∀ p ∈ P, p.2 < p.2 + p.1 ∧ p.2 + p.1 < A.card)
    (hinj : ∀ x ∈ P, ∀ y ∈ P, x.2 = y.2 → x.2 + x.1 = y.2 + y.1 → x = y) :
    ∑ p ∈ P, invGap (nth A p.2) (nth A (p.2 + p.1)) ≤ pairSum A :=
  sum_le_pairSum A P (fun p => p.2) (fun p => p.2 + p.1) hab hinj

/-! ### Telescoping bound for ordered disjoint intervals -/

/-- If the intervals `[u i, v i]`, `i ∈ C`, are "ordered disjoint" (`v i ≤ u j` for `i < j`
in `C`) and all contained in `[lo, hi]`, then the total length is at most `hi - lo`. -/
lemma interval_telescope (u v : ℕ → ℝ) (C : Finset ℕ) :
    ∀ lo hi : ℝ, lo ≤ hi →
      (∀ i ∈ C, lo ≤ u i) → (∀ i ∈ C, v i ≤ hi) →
      (∀ i ∈ C, ∀ j ∈ C, i < j → v i ≤ u j) →
      ∑ i ∈ C, (v i - u i) ≤ hi - lo := by
  induction C using Finset.strongInduction with
  | _ C ih =>
    intro lo hi hlohi h1 h2 h3
    rcases C.eq_empty_or_nonempty with rfl | hne
    · simpa using hlohi
    have hMC : C.max' hne ∈ C := C.max'_mem hne
    have hE := ih (C.erase (C.max' hne)) (Finset.erase_ssubset hMC) lo (u (C.max' hne))
      (h1 _ hMC)
      (fun i hi => h1 i (Finset.mem_of_mem_erase hi))
      (fun i hi => h3 i (Finset.mem_of_mem_erase hi) _ hMC
        (lt_of_le_of_ne (Finset.le_max' C i (Finset.mem_of_mem_erase hi))
          (Finset.ne_of_mem_erase hi)))
      (fun i hi j hj hij =>
        h3 i (Finset.mem_of_mem_erase hi) j (Finset.mem_of_mem_erase hj) hij)
    have hsplit : ∑ i ∈ C, (v i - u i)
        = (v (C.max' hne) - u (C.max' hne)) + ∑ i ∈ C.erase (C.max' hne), (v i - u i) :=
      (Finset.add_sum_erase C _ hMC).symm
    have hvM : v (C.max' hne) ≤ hi := h2 _ hMC
    linarith

/-! ### Cauchy–Schwarz helpers -/

/-- Cauchy–Schwarz in the AM–HM form: `card² ≤ (Σ g)·(Σ g⁻¹)` for positive `g`. -/
lemma sq_card_le_sum_mul_sum_inv {ι : Type*} (s : Finset ι) (g : ι → ℝ)
    (hg : ∀ i ∈ s, 0 < g i) :
    (s.card : ℝ) ^ 2 ≤ (∑ i ∈ s, g i) * ∑ i ∈ s, (g i)⁻¹ := by
  have h1 : ∑ i ∈ s, Real.sqrt (g i) * (Real.sqrt (g i))⁻¹ = (s.card : ℝ) := by
    have hone : ∀ i ∈ s, Real.sqrt (g i) * (Real.sqrt (g i))⁻¹ = 1 := fun i hi =>
      mul_inv_cancel₀ (Real.sqrt_pos.2 (hg i hi)).ne'
    rw [Finset.sum_congr rfl hone, Finset.sum_const, nsmul_eq_mul, mul_one]
  have h2 : ∑ i ∈ s, (Real.sqrt (g i)) ^ 2 = ∑ i ∈ s, g i :=
    Finset.sum_congr rfl fun i hi => Real.sq_sqrt (hg i hi).le
  have h3 : ∑ i ∈ s, ((Real.sqrt (g i))⁻¹) ^ 2 = ∑ i ∈ s, (g i)⁻¹ :=
    Finset.sum_congr rfl fun i hi => by
      rw [inv_pow, Real.sq_sqrt (hg i hi).le]
  calc (s.card : ℝ) ^ 2
      = (∑ i ∈ s, Real.sqrt (g i) * (Real.sqrt (g i))⁻¹) ^ 2 := by rw [h1]
    _ ≤ (∑ i ∈ s, (Real.sqrt (g i)) ^ 2) * ∑ i ∈ s, ((Real.sqrt (g i))⁻¹) ^ 2 :=
        Finset.sum_mul_sq_le_sq_mul_sq s _ _
    _ = (∑ i ∈ s, g i) * ∑ i ∈ s, (g i)⁻¹ := by rw [h2, h3]

/-- Cauchy–Schwarz: `(Σ f)² ≤ card · Σ f²`. -/
lemma sq_sum_le_card_mul_sum_sq' {ι : Type*} (s : Finset ι) (f : ι → ℝ) :
    (∑ i ∈ s, f i) ^ 2 ≤ (s.card : ℝ) * ∑ i ∈ s, f i ^ 2 := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq s (fun _ => (1 : ℝ)) f
  simpa using h

/-! ### The chain bound for a fixed index-distance `m` -/

/-- For a fixed index-distance `m ≥ 1`, splitting the indices into `m` arithmetic chains,
telescoping each chain and applying Cauchy–Schwarz twice gives
`Σ_{i+m<k} 1/(nth(i+m) − nth i) ≥ (k−m)²/(mH)`. -/
lemma chain_sum_ge (A : Finset ℕ) {H : ℝ} {m : ℕ} (hm : 1 ≤ m) (hH : 0 < H)
    (hdiam : ∀ a ∈ A, ∀ b ∈ A, (b : ℝ) - (a : ℝ) ≤ H) (hne : A.Nonempty) :
    ((A.card - m : ℕ) : ℝ) ^ 2 / ((m : ℝ) * H) ≤
      ∑ i ∈ Finset.range (A.card - m), invGap (nth A i) (nth A (i + m)) := by
  classical
  set k := A.card with hk
  have hm0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hHne : H ≠ 0 := ne_of_gt hH
  have hmaps : ∀ i ∈ Finset.range (k - m), i % m ∈ Finset.range m :=
    fun i _ => Finset.mem_range.2 (Nat.mod_lt i hm)
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  -- per-chain bound: telescoping + Cauchy–Schwarz
  have hfiber : ∀ r ∈ Finset.range m,
      ((((Finset.range (k - m)).filter (fun i => i % m = r)).card : ℝ)) ^ 2 / H ≤
        ∑ i ∈ (Finset.range (k - m)).filter (fun i => i % m = r),
          invGap (nth A i) (nth A (i + m)) := by
    intro r _
    set C := (Finset.range (k - m)).filter (fun i => i % m = r) with hC
    have hCsub : ∀ i ∈ C, i < k - m := fun i hi =>
      Finset.mem_range.1 (Finset.mem_filter.1 hi).1
    have hgap_pos : ∀ i ∈ C, (0 : ℝ) < (nth A (i + m) : ℝ) - (nth A i : ℝ) := by
      intro i hi
      have h2 : i + m < k := by have := hCsub i hi; omega
      have h3 : nth A i < nth A (i + m) := nth_lt_nth A (by omega) h2
      have h4 : (nth A i : ℝ) < (nth A (i + m) : ℝ) := by exact_mod_cast h3
      linarith
    have hlb : ∀ i ∈ C, ((A.min' hne : ℕ) : ℝ) ≤ (nth A i : ℝ) := by
      intro i hi
      have hik : i < k := by have := hCsub i hi; omega
      exact_mod_cast A.min'_le _ (nth_mem A hik)
    have hub : ∀ i ∈ C, (nth A (i + m) : ℝ) ≤ ((A.min' hne : ℕ) : ℝ) + H := by
      intro i hi
      have hik : i + m < k := by have := hCsub i hi; omega
      have := hdiam (A.min' hne) (A.min'_mem hne) (nth A (i + m)) (nth_mem A hik)
      linarith
    have horder : ∀ i ∈ C, ∀ j ∈ C, i < j → (nth A (i + m) : ℝ) ≤ (nth A j : ℝ) := by
      intro i hi j hj hij
      have hri : i % m = r := (Finset.mem_filter.1 hi).2
      have hrj : j % m = r := (Finset.mem_filter.1 hj).2
      have hmod : i ≡ j [MOD m] := by
        unfold Nat.ModEq
        rw [hri, hrj]
      have hdvd : m ∣ j - i := (Nat.modEq_iff_dvd' hij.le).1 hmod
      have hji : m ≤ j - i := Nat.le_of_dvd (by omega) hdvd
      have hjk : j < k := by have := hCsub j hj; omega
      exact_mod_cast nth_le_nth A (by omega) hjk
    have htel : ∑ i ∈ C, ((nth A (i + m) : ℝ) - (nth A i : ℝ))
        ≤ (((A.min' hne : ℕ) : ℝ) + H) - ((A.min' hne : ℕ) : ℝ) :=
      interval_telescope (fun i => (nth A i : ℝ)) (fun i => (nth A (i + m) : ℝ)) C
        ((A.min' hne : ℕ) : ℝ) (((A.min' hne : ℕ) : ℝ) + H) (by linarith) hlb hub horder
    have htel' : ∑ i ∈ C, ((nth A (i + m) : ℝ) - (nth A i : ℝ)) ≤ H := by linarith
    have hinv_nonneg : 0 ≤ ∑ i ∈ C, ((nth A (i + m) : ℝ) - (nth A i : ℝ))⁻¹ :=
      Finset.sum_nonneg fun i hi => (inv_pos.2 (hgap_pos i hi)).le
    have hcs : (C.card : ℝ) ^ 2 ≤
        (∑ i ∈ C, ((nth A (i + m) : ℝ) - (nth A i : ℝ))) *
          ∑ i ∈ C, ((nth A (i + m) : ℝ) - (nth A i : ℝ))⁻¹ :=
      sq_card_le_sum_mul_sum_inv C _ hgap_pos
    rw [div_le_iff₀ hH]
    calc (C.card : ℝ) ^ 2
        ≤ (∑ i ∈ C, ((nth A (i + m) : ℝ) - (nth A i : ℝ))) *
            ∑ i ∈ C, ((nth A (i + m) : ℝ) - (nth A i : ℝ))⁻¹ := hcs
      _ ≤ H * ∑ i ∈ C, ((nth A (i + m) : ℝ) - (nth A i : ℝ))⁻¹ :=
          mul_le_mul_of_nonneg_right htel' hinv_nonneg
      _ = (∑ i ∈ C, invGap (nth A i) (nth A (i + m))) * H := by
          rw [mul_comm]
  -- counting: the chains partition the index range
  have hcardsum : (k - m) = ∑ r ∈ Finset.range m,
      ((Finset.range (k - m)).filter (fun i => i % m = r)).card := by
    have h := Finset.card_eq_sum_card_fiberwise hmaps
    rwa [Finset.card_range] at h
  have hsum : ((k - m : ℕ) : ℝ) = ∑ r ∈ Finset.range m,
      (((Finset.range (k - m)).filter (fun i => i % m = r)).card : ℝ) := by
    exact_mod_cast hcardsum
  -- Cauchy–Schwarz over the chains
  have hCS : ((k - m : ℕ) : ℝ) ^ 2 ≤
      (m : ℝ) * ∑ r ∈ Finset.range m,
        (((Finset.range (k - m)).filter (fun i => i % m = r)).card : ℝ) ^ 2 := by
    have h := sq_sum_le_card_mul_sum_sq' (Finset.range m)
      (fun r => (((Finset.range (k - m)).filter (fun i => i % m = r)).card : ℝ))
    rw [Finset.card_range] at h
    rw [hsum]
    exact h
  calc ((k - m : ℕ) : ℝ) ^ 2 / ((m : ℝ) * H)
      ≤ ∑ r ∈ Finset.range m,
          (((Finset.range (k - m)).filter (fun i => i % m = r)).card : ℝ) ^ 2 / H := by
        rw [div_le_iff₀ (mul_pos hm0 hH)]
        calc ((k - m : ℕ) : ℝ) ^ 2
            ≤ (m : ℝ) * ∑ r ∈ Finset.range m,
                (((Finset.range (k - m)).filter (fun i => i % m = r)).card : ℝ) ^ 2 := hCS
          _ = (∑ r ∈ Finset.range m,
                (((Finset.range (k - m)).filter (fun i => i % m = r)).card : ℝ) ^ 2 / H) *
                ((m : ℝ) * H) := by
              rw [← Finset.sum_div, div_mul_eq_mul_div, mul_div_assoc,
                mul_div_cancel_right₀ _ hHne, mul_comm]
    _ ≤ ∑ r ∈ Finset.range m, ∑ i ∈ (Finset.range (k - m)).filter (fun i => i % m = r),
          invGap (nth A i) (nth A (i + m)) := Finset.sum_le_sum hfiber

/-! ### Harmonic sum lower bound -/

lemma log_le_sum_inv (M : ℕ) :
    Real.log ((M : ℝ) + 1) ≤ ∑ m ∈ Finset.Icc 1 M, ((m : ℝ))⁻¹ := by
  have h := log_add_one_le_harmonic M
  rw [harmonic_eq_sum_Icc] at h
  push_cast at h
  exact h

/-! ### Lemma D: the energy lower bound (Tao eq. (1.2)) -/

theorem pairSum_ge_energy {A : Finset ℕ} {H : ℝ} (hcard : 4 ≤ A.card) (hH : 1 ≤ H)
    (hdiam : ∀ a ∈ A, ∀ b ∈ A, (b : ℝ) - (a : ℝ) ≤ H) :
    (A.card : ℝ)^2 * Real.log ((A.card : ℝ) / 2) / (4 * H) ≤ pairSum A := by
  classical
  have hne : A.Nonempty := Finset.card_pos.1 (by omega)
  have hH0 : (0 : ℝ) < H := by linarith
  have hHne : H ≠ 0 := ne_of_gt hH0
  set k := A.card with hk
  set M := k / 2 with hM
  have hk0 : (0 : ℝ) < (k : ℝ) := by
    have : 0 < k := by omega
    exact_mod_cast this
  have hk2 : (0 : ℝ) < (k : ℝ) / 2 := by linarith
  -- Step 1: the double sum over index-distances m and start indices i is ≤ pairSum A
  have hdouble : ∑ m ∈ Finset.Icc 1 M, ∑ i ∈ Finset.range (k - m),
      invGap (nth A i) (nth A (i + m)) ≤ pairSum A := by
    have hchar : ∀ p : ℕ × ℕ,
        p ∈ (Finset.Icc 1 M ×ˢ Finset.range k).filter (fun p => p.2 + p.1 < k) ↔
          p.1 ∈ Finset.Icc 1 M ∧ p.2 ∈ Finset.range (k - p.1) := by
      intro p
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, Finset.mem_range]
      omega
    have heq : ∑ m ∈ Finset.Icc 1 M, ∑ i ∈ Finset.range (k - m),
        invGap (nth A i) (nth A (i + m))
        = ∑ p ∈ (Finset.Icc 1 M ×ˢ Finset.range k).filter (fun p => p.2 + p.1 < k),
            invGap (nth A p.2) (nth A (p.2 + p.1)) :=
      (Finset.sum_finset_product' _ (Finset.Icc 1 M) (fun m => Finset.range (k - m)) hchar
        (f := fun c a => invGap (nth A a) (nth A (a + c)))).symm
    have hab : ∀ p ∈ (Finset.Icc 1 M ×ˢ Finset.range k).filter
        (fun p : ℕ × ℕ => p.2 + p.1 < k), p.2 < p.2 + p.1 ∧ p.2 + p.1 < A.card := by
      intro p hp
      rw [hchar p] at hp
      simp only [Finset.mem_Icc, Finset.mem_range] at hp
      omega
    have hinj : ∀ x ∈ (Finset.Icc 1 M ×ˢ Finset.range k).filter
        (fun p : ℕ × ℕ => p.2 + p.1 < k),
        ∀ y ∈ (Finset.Icc 1 M ×ˢ Finset.range k).filter
        (fun p : ℕ × ℕ => p.2 + p.1 < k),
        x.2 = y.2 → x.2 + x.1 = y.2 + y.1 → x = y := by
      intro x _ y _ h1 h2
      obtain ⟨x1, x2⟩ := x
      obtain ⟨y1, y2⟩ := y
      simp only [Prod.mk.injEq]
      simp only at h1 h2
      omega
    rw [heq]
    exact sum_pairs_le_pairSum A ((Finset.Icc 1 M ×ˢ Finset.range k).filter
      (fun p : ℕ × ℕ => p.2 + p.1 < k)) hab hinj
  -- Step 2: per-m chain bound
  have hper : ∀ m ∈ Finset.Icc 1 M, ((k - m : ℕ) : ℝ) ^ 2 / ((m : ℝ) * H) ≤
      ∑ i ∈ Finset.range (k - m), invGap (nth A i) (nth A (i + m)) := by
    intro m hm
    exact chain_sum_ge A (Finset.mem_Icc.1 hm).1 hH0 hdiam hne
  -- Step 3: (k−m)² ≥ (k/2)² for m ≤ M
  have hquarter : ∀ m ∈ Finset.Icc 1 M,
      ((k : ℝ) / 2) ^ 2 / ((m : ℝ) * H) ≤ ((k - m : ℕ) : ℝ) ^ 2 / ((m : ℝ) * H) := by
    intro m hm
    rw [Finset.mem_Icc] at hm
    have hm0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm.1
    have hmH : (0 : ℝ) < (m : ℝ) * H := mul_pos hm0 hH0
    have hmk : m ≤ k := by omega
    have h2m : 2 * m ≤ k := by omega
    have h2m' : 2 * (m : ℝ) ≤ (k : ℝ) := by exact_mod_cast h2m
    have hge : (k : ℝ) / 2 ≤ ((k - m : ℕ) : ℝ) := by
      rw [Nat.cast_sub hmk]
      linarith
    have hsq : ((k : ℝ) / 2) ^ 2 ≤ ((k - m : ℕ) : ℝ) ^ 2 := by
      rw [pow_two, pow_two]
      exact mul_self_le_mul_self hk2.le hge
    rw [div_le_iff₀ hmH]
    calc ((k : ℝ) / 2) ^ 2 ≤ ((k - m : ℕ) : ℝ) ^ 2 := hsq
      _ = ((k - m : ℕ) : ℝ) ^ 2 / ((m : ℝ) * H) * ((m : ℝ) * H) := by
          rw [div_mul_cancel₀ _ (ne_of_gt hmH)]
  -- Step 4: harmonic sum lower bound
  have hlog : Real.log ((k : ℝ) / 2) ≤ Real.log ((M : ℝ) + 1) := by
    apply Real.log_le_log hk2
    have h1 : k ≤ 2 * M + 1 := by omega
    have h2 : (k : ℝ) ≤ 2 * (M : ℝ) + 1 := by exact_mod_cast h1
    linarith
  have hlogsum : Real.log ((k : ℝ) / 2) ≤ ∑ m ∈ Finset.Icc 1 M, ((m : ℝ))⁻¹ :=
    hlog.trans (log_le_sum_inv M)
  -- Assemble
  calc (k : ℝ) ^ 2 * Real.log ((k : ℝ) / 2) / (4 * H)
      = ((k : ℝ) / 2) ^ 2 / H * Real.log ((k : ℝ) / 2) := by
        field_simp
        ring
    _ ≤ ((k : ℝ) / 2) ^ 2 / H * ∑ m ∈ Finset.Icc 1 M, ((m : ℝ))⁻¹ :=
        mul_le_mul_of_nonneg_left hlogsum (div_nonneg (by positivity) hH0.le)
    _ = ∑ m ∈ Finset.Icc 1 M, ((k : ℝ) / 2) ^ 2 / ((m : ℝ) * H) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun m hm => ?_
        have hm0 : ((m : ℝ)) ≠ 0 := by
          have h1 : 1 ≤ m := (Finset.mem_Icc.1 hm).1
          have : (0 : ℝ) < (m : ℝ) := by exact_mod_cast h1
          exact ne_of_gt this
        field_simp
    _ ≤ ∑ m ∈ Finset.Icc 1 M, ((k - m : ℕ) : ℝ) ^ 2 / ((m : ℝ) * H) :=
        Finset.sum_le_sum hquarter
    _ ≤ ∑ m ∈ Finset.Icc 1 M, ∑ i ∈ Finset.range (k - m),
          invGap (nth A i) (nth A (i + m)) := Finset.sum_le_sum hper
    _ ≤ pairSum A := hdouble


end Erdos884
end

/-! Flattened from Erdos884/CoprimeSum884.lean. -/
section

/-!
# Erdős 884 — Lemma B.3: lower bound for the weighted sum over squarefree numbers
coprime to `m`.

Exports `Erdos884.coprime_squarefree_sum_lower`:
`∃ c₀ > 0, ∃ w₀, ∀ w ≥ w₀, ∀ m ≥ 1 with m ≤ (log w)³,`
`  c₀ · (φ(m)/m)² · (log w)² ≤ Σ_{ℓ ≤ w, squarefree, coprime to m} 2^ω(ℓ)/ℓ`.
-/

namespace Erdos884

open Finset

/-! ## Counting integers coprime to `m` in intervals -/

/-- A general "sum over an injection" helper. -/
lemma cs_sum_le_sum_inj {α β : Type*} [DecidableEq β] {s : Finset α} {t : Finset β}
    (e : α → β) (f : α → ℝ) (g : β → ℝ)
    (hmaps : ∀ a ∈ s, e a ∈ t) (hinj : Set.InjOn e ↑s)
    (hval : ∀ a ∈ s, f a ≤ g (e a)) (hg : ∀ b ∈ t, 0 ≤ g b) :
    ∑ a ∈ s, f a ≤ ∑ b ∈ t, g b := by
  calc ∑ a ∈ s, f a ≤ ∑ a ∈ s, g (e a) := Finset.sum_le_sum hval
    _ = ∑ b ∈ s.image e, g b := (Finset.sum_image hinj).symm
    _ ≤ ∑ b ∈ t, g b := Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.image_subset_iff.mpr hmaps) (fun b hb _ => hg b hb)

/-- Exact count of integers coprime to `m` in a run of `q` full blocks of length `m`. -/
lemma cs_cnt_blocks (m n q : ℕ) :
    ((Finset.Ico n (n + q * m)).filter (fun a => Nat.Coprime a m)).card = q * m.totient := by
  induction q with
  | zero => simp
  | succ k ih =>
    have hblock : ((Finset.Ico (n + k * m) (n + k * m + m)).filter
        (fun a => Nat.Coprime a m)).card = m.totient := by
      rw [show (Finset.filter (fun a => Nat.Coprime a m)
            (Finset.Ico (n + k * m) (n + k * m + m)))
          = (Finset.filter (fun x => Nat.Coprime m x)
            (Finset.Ico (n + k * m) (n + k * m + m))) from
        Finset.filter_congr (fun x _ => Nat.coprime_comm)]
      exact Nat.filter_coprime_Ico_eq_totient m (n + k * m)
    have hkey : n + (k + 1) * m = (n + k * m) + m := by ring
    rw [hkey, ← Finset.Ico_union_Ico_eq_Ico (a := n) (b := n + k * m) (c := n + k * m + m)
        (by omega) (by omega), Finset.filter_union,
      Finset.card_union_of_disjoint
        (Finset.disjoint_filter_filter (Finset.Ico_disjoint_Ico_consecutive _ _ _)),
      ih, hblock]
    ring

/-- Upper bound for the number of integers coprime to `m` in any interval of length `L`. -/
lemma cs_cnt_upper (m : ℕ) (hm : 0 < m) (n L : ℕ) :
    ((Finset.Ico n (n + L)).filter (fun a => Nat.Coprime a m)).card
      ≤ (L / m + 1) * m.totient := by
  have hL : L < (L / m + 1) * m := by
    have h1 := Nat.div_add_mod L m
    have h2 : L % m < m := Nat.mod_lt L hm
    calc L = m * (L / m) + L % m := h1.symm
      _ < m * (L / m) + m := by omega
      _ = (L / m + 1) * m := by ring
  have hsub : Finset.Ico n (n + L) ⊆ Finset.Ico n (n + (L / m + 1) * m) :=
    Finset.Ico_subset_Ico le_rfl (by omega)
  exact le_of_le_of_eq (Finset.card_le_card (Finset.filter_subset_filter _ hsub))
    (cs_cnt_blocks m n (L / m + 1))

/-- Lower bound for the number of integers coprime to `m` in the block `(v, 2v]`. -/
lemma cs_cnt_lower (m v : ℕ) :
    (v / m) * m.totient ≤ ((Finset.Ioc v (2 * v)).filter (fun a => Nat.Coprime a m)).card := by
  have hsub : Finset.Ico (v + 1) (v + 1 + (v / m) * m) ⊆ Finset.Ioc v (2 * v) := by
    intro a ha
    simp only [Finset.mem_Ico] at ha
    simp only [Finset.mem_Ioc]
    have := Nat.div_mul_le_self v m
    omega
  calc (v / m) * m.totient
      = ((Finset.Ico (v + 1) (v + 1 + (v / m) * m)).filter (fun a => Nat.Coprime a m)).card :=
        (cs_cnt_blocks m (v + 1) (v / m)).symm
    _ ≤ _ := Finset.card_le_card (Finset.filter_subset_filter _ hsub)

lemma cs_two_mul_div_le (A c : ℕ) (hc : 0 < c) : 2 * A / c ≤ 2 * (A / c) + 1 := by
  rw [two_mul, Nat.add_div hc]
  split <;> omega

/-- Count of multiples of `c = p²` coprime to `m` in the block `(v, 2v]`. -/
lemma cs_cnt_sq_dvd (m : ℕ) (hm : 0 < m) (v p : ℕ) (hp : 0 < p) :
    ((Finset.Ioc v (2 * v)).filter (fun a => p * p ∣ a ∧ Nat.Coprime a m)).card
      ≤ (v / (p * p) / m + 2) * m.totient := by
  set c := p * p with hcdef
  have hc0 : 0 < c := Nat.mul_pos hp hp
  have hle : v / c ≤ 2 * v / c := Nat.div_le_div_right (by omega)
  -- Step 1: inject `a ↦ a / c` into the coprime elements of `Ioc (v/c) (2v/c)`.
  have hcard : ((Finset.Ioc v (2 * v)).filter (fun a => c ∣ a ∧ Nat.Coprime a m)).card
      ≤ ((Finset.Ioc (v / c) (2 * v / c)).filter (fun b => Nat.Coprime b m)).card := by
    apply Finset.card_le_card_of_injOn (fun a => a / c)
    · intro a ha
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_Ioc] at ha ⊢
      obtain ⟨⟨hva, ha2v⟩, hdvd, hcop⟩ := ha
      refine ⟨⟨?_, Nat.div_le_div_right ha2v⟩, ?_⟩
      · rw [Nat.div_lt_iff_lt_mul hc0, Nat.div_mul_cancel hdvd]
        exact hva
      · exact Nat.Coprime.coprime_dvd_left ⟨c, (Nat.div_mul_cancel hdvd).symm⟩ hcop
    · intro a₁ h₁ a₂ h₂ heq
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_Ioc] at h₁ h₂
      have e₁ : c * (a₁ / c) = a₁ := Nat.mul_div_cancel' h₁.2.1
      have e₂ : c * (a₂ / c) = a₂ := Nat.mul_div_cancel' h₂.2.1
      simp only at heq
      rw [← e₁, ← e₂, heq]
  -- Step 2: bound the target cardinality.
  have hIoc : Finset.Ioc (v / c) (2 * v / c)
      = Finset.Ico (v / c + 1) ((v / c + 1) + (2 * v / c - v / c)) := by
    ext y
    simp only [Finset.mem_Ioc, Finset.mem_Ico]
    omega
  have h2 : ((Finset.Ioc (v / c) (2 * v / c)).filter (fun b => Nat.Coprime b m)).card
      ≤ ((2 * v / c - v / c) / m + 1) * m.totient := by
    rw [hIoc]
    exact cs_cnt_upper m hm _ _
  have h3 : (2 * v / c - v / c) / m + 1 ≤ v / c / m + 2 := by
    have hlen : 2 * v / c - v / c ≤ v / c + 1 := by
      have := cs_two_mul_div_le v c hc0
      omega
    have : (2 * v / c - v / c) / m ≤ (v / c + 1) / m := Nat.div_le_div_right hlen
    have h4 : (v / c + 1) / m ≤ (v / c + m) / m := Nat.div_le_div_right (by omega)
    rw [Nat.add_div_right _ hm] at h4
    omega
  calc ((Finset.Ioc v (2 * v)).filter (fun a => c ∣ a ∧ Nat.Coprime a m)).card
      ≤ ((2 * v / c - v / c) / m + 1) * m.totient := le_trans hcard h2
    _ ≤ (v / c / m + 2) * m.totient := Nat.mul_le_mul_right _ h3

/-! ## Inverse-square sums via telescoping -/

lemma cs_telescope_le (B : ℕ) (f : ℕ → ℝ) (hfB : 0 ≤ f B) :
    ∑ i ∈ Finset.range B, (f i - f (i + 1)) ≤ f 0 := by
  rw [Finset.sum_range_sub' f B]
  linarith

lemma cs_real_ineq1 (x : ℝ) (hx : 0 ≤ x) :
    1 / ((x + 3) * (x + 3)) ≤ 1 / (x + 2) - 1 / (x + 1 + 2) := by
  have h1 : (0:ℝ) < x + 2 := by linarith
  have h2 : (0:ℝ) < x + 3 := by linarith
  have key : 1 / (x + 2) - 1 / (x + 1 + 2) = 1 / ((x + 2) * (x + 3)) := by
    rw [show x + 1 + 2 = x + 3 by ring]
    field_simp
    ring
  rw [key]
  apply one_div_le_one_div_of_le
  · positivity
  · nlinarith

lemma cs_real_ineq2 (x : ℝ) (hx : 0 ≤ x) :
    1 / ((2 * x + 3) * (2 * x + 3)) ≤ 1 / (4 * (x + 1)) - 1 / (4 * (x + 1 + 1)) := by
  have key : 1 / (4 * (x + 1)) - 1 / (4 * (x + 1 + 1)) = 1 / (4 * ((x + 1) * (x + 2))) := by
    rw [show x + 1 + 1 = x + 2 by ring]
    field_simp
    ring
  rw [key]
  apply one_div_le_one_div_of_le
  · positivity
  · nlinarith

/-- Sum of `1/g²` over a finite set of naturals all `≥ 3` is at most `1/2`. -/
lemma cs_inv_sq_sum_ge3 (Q : Finset ℕ) (hQ : ∀ g ∈ Q, 3 ≤ g) :
    ∑ g ∈ Q, (1 : ℝ) / ((g : ℝ) * g) ≤ 1 / 2 := by
  set B := Q.sup id + 1 with hB
  set F : ℕ → ℝ := fun i => (1:ℝ) / ((i:ℝ) + 2) with hF
  have hchain : ∑ g ∈ Q, (1 : ℝ) / ((g : ℝ) * g)
      ≤ ∑ i ∈ Finset.range B, (F i - F (i + 1)) := by
    apply cs_sum_le_sum_inj (fun g => g - 3)
    · intro g hg
      simp only [Finset.mem_range]
      have := Finset.le_sup (f := id) hg
      simp only [id_eq] at this
      omega
    · intro g₁ h₁ g₂ h₂ heq
      simp only [Finset.mem_coe] at h₁ h₂
      have := hQ g₁ h₁
      have := hQ g₂ h₂
      simp only at heq
      omega
    · intro g hg
      obtain ⟨d, rfl⟩ : ∃ d, g = d + 3 := ⟨g - 3, by have := hQ g hg; omega⟩
      simp only [Nat.add_sub_cancel, hF]
      push_cast
      exact cs_real_ineq1 (d:ℝ) (Nat.cast_nonneg d)
    · intro b _
      simp only [hF, sub_nonneg]
      apply one_div_le_one_div_of_le
      · positivity
      · push_cast
        linarith
  have hend : ∑ i ∈ Finset.range B, (F i - F (i + 1)) ≤ F 0 :=
    cs_telescope_le B F (by simp only [hF]; positivity)
  have hF0 : F 0 = 1/2 := by simp only [hF]; norm_num
  exact hchain.trans (hend.trans hF0.le)

/-- Sum of `1/g²` over a finite set of odd naturals all `≥ 3` is at most `1/4`. -/
lemma cs_inv_sq_sum_odd (Q : Finset ℕ) (hQ : ∀ g ∈ Q, 3 ≤ g ∧ g % 2 = 1) :
    ∑ g ∈ Q, (1 : ℝ) / ((g : ℝ) * g) ≤ 1 / 4 := by
  set B := Q.sup id + 1 with hB
  set F : ℕ → ℝ := fun i => (1:ℝ) / (4 * ((i:ℝ) + 1)) with hF
  have hchain : ∑ g ∈ Q, (1 : ℝ) / ((g : ℝ) * g)
      ≤ ∑ i ∈ Finset.range B, (F i - F (i + 1)) := by
    apply cs_sum_le_sum_inj (fun g => (g - 3) / 2)
    · intro g hg
      simp only [Finset.mem_range]
      have := Finset.le_sup (f := id) hg
      simp only [id_eq] at this
      omega
    · intro g₁ h₁ g₂ h₂ heq
      simp only [Finset.mem_coe] at h₁ h₂
      have := hQ g₁ h₁
      have := hQ g₂ h₂
      simp only at heq
      omega
    · intro g hg
      obtain ⟨d, rfl⟩ : ∃ d, g = 2 * d + 3 :=
        ⟨(g - 3) / 2, by have := hQ g hg; omega⟩
      have hidx : (2 * d + 3 - 3) / 2 = d := by omega
      rw [hidx]
      simp only [hF]
      push_cast
      exact cs_real_ineq2 (d:ℝ) (Nat.cast_nonneg d)
    · intro b _
      simp only [hF, sub_nonneg]
      apply one_div_le_one_div_of_le
      · positivity
      · push_cast
        linarith
  have hend : ∑ i ∈ Finset.range B, (F i - F (i + 1)) ≤ F 0 :=
    cs_telescope_le B F (by simp only [hF]; positivity)
  have hF0 : F 0 = 1/4 := by simp only [hF]; norm_num
  exact hchain.trans (hend.trans hF0.le)

/-- Sum of `1/p²` over a finite set of primes is at most `1/2`. -/
lemma cs_prime_inv_sq_sum (P : Finset ℕ) (hP : ∀ p ∈ P, Nat.Prime p) :
    ∑ p ∈ P, (1 : ℝ) / ((p : ℝ) * p) ≤ 1 / 2 := by
  have hodd : ∀ p ∈ P.erase 2, 3 ≤ p ∧ p % 2 = 1 := by
    intro p hp
    obtain ⟨hne, hp'⟩ := Finset.mem_erase.mp hp
    have hprime := hP p hp'
    have h1 : p % 2 = 1 := Nat.odd_iff.mp (hprime.odd_of_ne_two hne)
    have h2 := hprime.two_le
    omega
  by_cases h2 : 2 ∈ P
  · rw [← Finset.sum_erase_add P _ h2]
    have herase := cs_inv_sq_sum_odd _ hodd
    have hval : (1:ℝ) / (((2:ℕ):ℝ) * ((2:ℕ):ℝ)) = 1/4 := by norm_num
    rw [hval]
    linarith
  · have hall : ∀ p ∈ P, 3 ≤ p ∧ p % 2 = 1 := fun p hp =>
      hodd p (Finset.mem_erase.mpr ⟨fun e => h2 (e ▸ hp), hp⟩)
    have := cs_inv_sq_sum_odd P hall
    linarith

/-- Sum of `1/g²` over a finite set of naturals all `≥ 2` is at most `3/4`. -/
lemma cs_inv_sq_sum_ge2 (Q : Finset ℕ) (hQ : ∀ g ∈ Q, 2 ≤ g) :
    ∑ g ∈ Q, (1 : ℝ) / ((g : ℝ) * g) ≤ 3 / 4 := by
  have hge3 : ∀ g ∈ Q.erase 2, 3 ≤ g := by
    intro g hg
    obtain ⟨hne, hg'⟩ := Finset.mem_erase.mp hg
    have := hQ g hg'
    omega
  by_cases h2 : 2 ∈ Q
  · rw [← Finset.sum_erase_add Q _ h2]
    have herase := cs_inv_sq_sum_ge3 _ hge3
    have hval : (1:ℝ) / (((2:ℕ):ℝ) * ((2:ℕ):ℝ)) = 1/4 := by norm_num
    rw [hval]
    linarith
  · have hall : ∀ g ∈ Q, 3 ≤ g := fun g hg =>
      hge3 g (Finset.mem_erase.mpr ⟨fun e => h2 (e ▸ hg), hg⟩)
    have := cs_inv_sq_sum_ge3 Q hall
    linarith

/-! ## Squarefree numbers coprime to `m` in dyadic blocks -/

/-- Non-squarefree coprime elements of `(v, 2v]` are covered by multiples of `p²`, `p ≤ √(2v)`. -/
lemma cs_nonsq_subset (m v : ℕ) :
    (Finset.Ioc v (2 * v)).filter (fun a => ¬ Squarefree a ∧ Nat.Coprime a m) ⊆
      ((Finset.Icc 2 (Nat.sqrt (2 * v))).filter Nat.Prime).biUnion
        (fun p => (Finset.Ioc v (2 * v)).filter (fun a => p * p ∣ a ∧ Nat.Coprime a m)) := by
  intro a ha
  simp only [Finset.mem_filter, Finset.mem_Ioc] at ha
  obtain ⟨⟨hva, ha2v⟩, hnsq, hcop⟩ := ha
  rw [Nat.squarefree_iff_prime_squarefree] at hnsq
  push_neg at hnsq
  obtain ⟨p, hp, hpd⟩ := hnsq
  have hpa : p * p ≤ a := Nat.le_of_dvd (by omega) hpd
  simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ioc]
  exact ⟨p, ⟨⟨hp.two_le, Nat.le_sqrt.mpr (by omega)⟩, hp⟩, ⟨hva, ha2v⟩, hpd, hcop⟩

/-- Real bound on the number of non-squarefree coprime elements of `(v, 2v]`. -/
lemma cs_nonsq_card (m v : ℕ) (hm : 0 < m) :
    (((Finset.Ioc v (2 * v)).filter (fun a => ¬ Squarefree a ∧ Nat.Coprime a m)).card : ℝ)
      ≤ (v : ℝ) * m.totient / (2 * m) + 2 * (Nat.sqrt (2 * v) : ℝ) * m.totient := by
  set P := (Finset.Icc 2 (Nat.sqrt (2 * v))).filter Nat.Prime with hPdef
  have hmR : (0:ℝ) < m := by exact_mod_cast hm
  have hcards : ((Finset.Ioc v (2 * v)).filter (fun a => ¬ Squarefree a ∧ Nat.Coprime a m)).card
      ≤ ∑ p ∈ P, ((Finset.Ioc v (2 * v)).filter (fun a => p * p ∣ a ∧ Nat.Coprime a m)).card :=
    le_trans (Finset.card_le_card (cs_nonsq_subset m v)) Finset.card_biUnion_le
  have hterm : ∀ p ∈ P,
      (((Finset.Ioc v (2 * v)).filter (fun a => p * p ∣ a ∧ Nat.Coprime a m)).card : ℝ)
        ≤ (v:ℝ) * m.totient / m * (1 / ((p:ℝ) * p)) + 2 * m.totient := by
    intro p hp
    have hprime : Nat.Prime p := (Finset.mem_filter.mp hp).2
    have hp0 : 0 < p := hprime.pos
    have hpR : (0:ℝ) < p := by exact_mod_cast hp0
    have h1 := cs_cnt_sq_dvd m hm v p hp0
    have h1R : (((Finset.Ioc v (2 * v)).filter
          (fun a => p * p ∣ a ∧ Nat.Coprime a m)).card : ℝ)
        ≤ (((v / (p * p) / m : ℕ) : ℝ) + 2) * (m.totient : ℝ) := by
      exact_mod_cast h1
    have h2 : ((v / (p * p) / m : ℕ) : ℝ) ≤ (v:ℝ) / ((p:ℝ) * p * m) := by
      rw [Nat.div_div_eq_div_mul]
      calc ((v / (p * p * m) : ℕ) : ℝ) ≤ (v:ℝ) / ((p * p * m : ℕ) : ℝ) := Nat.cast_div_le
        _ = (v:ℝ) / ((p:ℝ) * p * m) := by push_cast; ring
    calc (((Finset.Ioc v (2 * v)).filter
          (fun a => p * p ∣ a ∧ Nat.Coprime a m)).card : ℝ)
        ≤ (((v / (p * p) / m : ℕ) : ℝ) + 2) * (m.totient : ℝ) := h1R
      _ ≤ ((v:ℝ) / ((p:ℝ) * p * m) + 2) * (m.totient : ℝ) :=
          mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ = (v:ℝ) * m.totient / m * (1 / ((p:ℝ) * p)) + 2 * m.totient := by
          field_simp
  have hPcard : (P.card : ℝ) ≤ (Nat.sqrt (2 * v) : ℝ) := by
    have h1 : P.card ≤ (Finset.Icc 2 (Nat.sqrt (2 * v))).card :=
      Finset.card_le_card (Finset.filter_subset _ _)
    rw [Nat.card_Icc] at h1
    have : P.card ≤ Nat.sqrt (2 * v) := by omega
    exact_mod_cast this
  have hsum := cs_prime_inv_sq_sum P (fun p hp => (Finset.mem_filter.mp hp).2)
  calc (((Finset.Ioc v (2 * v)).filter (fun a => ¬ Squarefree a ∧ Nat.Coprime a m)).card : ℝ)
      ≤ ∑ p ∈ P, (((Finset.Ioc v (2 * v)).filter
          (fun a => p * p ∣ a ∧ Nat.Coprime a m)).card : ℝ) := by exact_mod_cast hcards
    _ ≤ ∑ p ∈ P, ((v:ℝ) * m.totient / m * (1 / ((p:ℝ) * p)) + 2 * m.totient) :=
        Finset.sum_le_sum hterm
    _ = (v:ℝ) * m.totient / m * (∑ p ∈ P, 1 / ((p:ℝ) * p)) + P.card * (2 * m.totient) := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul]
    _ ≤ (v:ℝ) * m.totient / m * (1/2) + (Nat.sqrt (2 * v) : ℝ) * (2 * m.totient) := by
        have hnn : (0:ℝ) ≤ (v:ℝ) * m.totient / m := by positivity
        have h1 := mul_le_mul_of_nonneg_left hsum hnn
        have h2 := mul_le_mul_of_nonneg_right hPcard
          (show (0:ℝ) ≤ 2 * m.totient by positivity)
        linarith
    _ = (v : ℝ) * m.totient / (2 * m) + 2 * (Nat.sqrt (2 * v) : ℝ) * m.totient := by ring

/-- The pure real-arithmetic core of the block-count bound. -/
lemma cs_real_block_core (mR vR D s : ℝ) (hm : 1 ≤ mR)
    (hv : 256 * mR^2 ≤ vR) (hD : vR - mR ≤ D * mR) (hs : s ≤ Real.sqrt 2 * Real.sqrt vR) :
    vR/(4*mR) + vR/(2*mR) + 2*s ≤ D := by
  have hm0 : (0:ℝ) < mR := by linarith
  have hv0 : (0:ℝ) ≤ vR := by nlinarith
  set x := Real.sqrt vR with hx
  have hxnn : (0:ℝ) ≤ x := Real.sqrt_nonneg vR
  have hxx : x * x = vR := Real.mul_self_sqrt hv0
  have hx16 : 16 * mR ≤ x := by
    rw [hx]
    rw [show vR = vR from rfl]
    refine (Real.le_sqrt (by positivity) hv0).mpr ?_
    nlinarith
  have hsqrt2 : Real.sqrt 2 ≤ 3/2 := by
    nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2]
  have hs' : s ≤ (3/2) * x := by
    calc s ≤ Real.sqrt 2 * x := hs
      _ ≤ (3/2) * x := mul_le_mul_of_nonneg_right hsqrt2 hxnn
  set u := vR / (4 * mR) with hu
  have h4x : 4 * x ≤ u := by
    rw [hu, le_div_iff₀ (by positivity)]
    nlinarith [mul_nonneg (sub_nonneg.mpr hx16) hxnn]
  have hx1 : (1:ℝ) ≤ x := by nlinarith
  have e2 : vR / (2 * mR) = 2 * u := by
    rw [hu]; field_simp; ring
  have hDm : 4 * u - 1 ≤ D := by
    have h5 : (vR - mR) / mR ≤ D := (div_le_iff₀ hm0).mpr hD
    have e4 : (vR - mR) / mR = 4 * u - 1 := by
      rw [hu]; field_simp
    linarith [e4 ▸ h5]
  have hkey : 1 + 2 * s ≤ u := by
    calc 1 + 2*s ≤ 1 + 3*x := by linarith
      _ ≤ 4*x := by linarith
      _ ≤ u := h4x
  linarith

/-- Core counting bound: the block `(v, 2v]` contains at least `v·φ(m)/(4m)` squarefree
numbers coprime to `m`, provided `v ≥ 256·m²`. -/
lemma cs_block_count (m v : ℕ) (hm : 1 ≤ m) (hv : 256 * m^2 ≤ v) :
    (v : ℝ) * m.totient / (4 * m)
      ≤ (((Finset.Ioc v (2 * v)).filter (fun a => Squarefree a ∧ Nat.Coprime a m)).card : ℝ) := by
  have hm0 : 0 < m := hm
  have hmR : (1:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm
  have hφ : 0 < m.totient := Nat.totient_pos.mpr hm0
  have hφR : (0:ℝ) < (m.totient : ℝ) := by exact_mod_cast hφ
  -- partition of the coprime elements into squarefree / non-squarefree
  have e1 : (Finset.Ioc v (2*v)).filter (fun a => Squarefree a ∧ Nat.Coprime a m)
      = ((Finset.Ioc v (2*v)).filter (fun a => Nat.Coprime a m)).filter Squarefree := by
    rw [Finset.filter_filter]
    exact Finset.filter_congr (fun x _ => and_comm)
  have e2 : (Finset.Ioc v (2*v)).filter (fun a => ¬ Squarefree a ∧ Nat.Coprime a m)
      = ((Finset.Ioc v (2*v)).filter (fun a => Nat.Coprime a m)).filter
          (fun a => ¬ Squarefree a) := by
    rw [Finset.filter_filter]
    exact Finset.filter_congr (fun x _ => and_comm)
  have hpart : ((Finset.Ioc v (2*v)).filter (fun a => Squarefree a ∧ Nat.Coprime a m)).card
      + ((Finset.Ioc v (2*v)).filter (fun a => ¬ Squarefree a ∧ Nat.Coprime a m)).card
      = ((Finset.Ioc v (2*v)).filter (fun a => Nat.Coprime a m)).card := by
    rw [e1, e2]
    exact Finset.card_filter_add_card_filter_not _
  have hcast : (((Finset.Ioc v (2*v)).filter (fun a => Squarefree a ∧ Nat.Coprime a m)).card : ℝ)
      = (((Finset.Ioc v (2*v)).filter (fun a => Nat.Coprime a m)).card : ℝ)
        - (((Finset.Ioc v (2*v)).filter (fun a => ¬ Squarefree a ∧ Nat.Coprime a m)).card : ℝ) := by
    have h := congrArg (Nat.cast : ℕ → ℝ) hpart
    push_cast at h
    linarith
  -- lower bound for the coprime count
  have hDR : ((v / m : ℕ) : ℝ) * (m.totient : ℝ)
      ≤ (((Finset.Ioc v (2*v)).filter (fun a => Nat.Coprime a m)).card : ℝ) := by
    exact_mod_cast cs_cnt_lower m v
  -- upper bound for the non-squarefree coprime count
  have hNS := cs_nonsq_card m v hm0
  -- the real core
  have hD' : (v:ℝ) - m ≤ ((v / m : ℕ) : ℝ) * m := by
    have h1 := Nat.div_add_mod v m
    have h2 : v % m < m := Nat.mod_lt v hm0
    have h3 : (m:ℝ) * ((v / m : ℕ) : ℝ) + ((v % m : ℕ) : ℝ) = (v:ℝ) := by exact_mod_cast h1
    have h4 : ((v % m : ℕ) : ℝ) < m := by exact_mod_cast h2
    nlinarith [mul_comm ((v / m : ℕ) : ℝ) ((m:ℕ) : ℝ)]
  have hs' : ((Nat.sqrt (2 * v) : ℕ) : ℝ) ≤ Real.sqrt 2 * Real.sqrt v := by
    have h1 : (Nat.sqrt (2 * v))^2 ≤ 2 * v := Nat.sqrt_le' (2 * v)
    have h2 : ((Nat.sqrt (2 * v) : ℕ) : ℝ) ≤ Real.sqrt ((2 * v : ℕ) : ℝ) := by
      refine (Real.le_sqrt (by positivity) (by positivity)).mpr ?_
      exact_mod_cast h1
    have h3 : Real.sqrt ((2 * v : ℕ) : ℝ) = Real.sqrt 2 * Real.sqrt v := by
      rw [show ((2 * v : ℕ) : ℝ) = 2 * (v:ℝ) by push_cast; ring]
      exact Real.sqrt_mul (by norm_num) _
    linarith [h3 ▸ h2]
  have hvR : 256 * (m:ℝ)^2 ≤ (v:ℝ) := by exact_mod_cast hv
  have hcore := cs_real_block_core (m:ℝ) (v:ℝ) ((v / m : ℕ) : ℝ)
    ((Nat.sqrt (2 * v) : ℕ) : ℝ) hmR hvR hD' hs'
  -- combine everything
  have hmul := mul_le_mul_of_nonneg_right hcore hφR.le
  have r1 : ((v:ℝ)/(4*(m:ℝ)) + (v:ℝ)/(2*(m:ℝ)) + 2*((Nat.sqrt (2 * v) : ℕ) : ℝ))
        * (m.totient : ℝ)
      = (v:ℝ) * m.totient / (4*m) + (v:ℝ) * m.totient / (2*m)
        + 2 * ((Nat.sqrt (2 * v) : ℕ) : ℝ) * m.totient := by ring
  linarith [hmul, r1, hcast, hDR, hNS]

/-! ## The dyadic harmonic sum -/

/-- Each dyadic block `(2^j, 2^{j+1}]` with `2^j ≥ 256·m²` contributes at least
`φ(m)/(8m)` to the harmonic sum over squarefree numbers coprime to `m`. -/
lemma cs_block_harmonic (m j : ℕ) (hm : 1 ≤ m) (hv : 256 * m^2 ≤ 2^j) :
    (m.totient : ℝ) / (8 * m)
      ≤ ∑ a ∈ (Finset.Ioc (2^j) (2^(j+1))).filter (fun a => Squarefree a ∧ Nat.Coprime a m),
          (1:ℝ)/a := by
  have hmR : (0:ℝ) < m := by exact_mod_cast hm
  have hpow : (2:ℕ)^(j+1) = 2 * 2^j := by rw [pow_succ]; ring
  have hcount := cs_block_count m (2^j) hm hv
  rw [show (2:ℕ) * 2^j = 2^(j+1) from hpow.symm] at hcount
  have hterm : ∀ a ∈ (Finset.Ioc (2^j) (2^(j+1))).filter
      (fun a => Squarefree a ∧ Nat.Coprime a m),
      (1:ℝ)/((2^(j+1) : ℕ) : ℝ) ≤ (1:ℝ)/(a : ℝ) := by
    intro a ha
    obtain ⟨hmem, -⟩ := Finset.mem_filter.mp ha
    obtain ⟨h1, h2⟩ := Finset.mem_Ioc.mp hmem
    have ha0 : 0 < a := by
      have := pow_pos (show 0 < 2 by norm_num) j
      omega
    apply one_div_le_one_div_of_le
    · exact_mod_cast ha0
    · exact_mod_cast h2
  have h5 : ((((Finset.Ioc (2^j) (2^(j+1))).filter
        (fun a => Squarefree a ∧ Nat.Coprime a m)).card : ℝ)) * (1/((2^(j+1) : ℕ) : ℝ))
      ≤ ∑ a ∈ (Finset.Ioc (2^j) (2^(j+1))).filter
          (fun a => Squarefree a ∧ Nat.Coprime a m), (1:ℝ)/a := by
    rw [← nsmul_eq_mul, ← Finset.sum_const]
    exact Finset.sum_le_sum hterm
  have heq : ((2^j : ℕ) : ℝ) * m.totient / (4 * m) * (1/((2^(j+1) : ℕ) : ℝ))
      = (m.totient : ℝ) / (8 * m) := by
    have c1 : ((2^j : ℕ) : ℝ) = (2:ℝ)^j := by push_cast; ring
    have c2 : ((2^(j+1) : ℕ) : ℝ) = 2 * (2:ℝ)^j := by
      rw [hpow]; push_cast; ring
    rw [c1, c2]
    have hne : ((2:ℝ))^j ≠ 0 := by positivity
    have hmne : ((m:ℕ) : ℝ) ≠ 0 := ne_of_gt hmR
    field_simp
    ring
  have h6 := mul_le_mul_of_nonneg_right hcount
    (show (0:ℝ) ≤ 1/((2^(j+1) : ℕ) : ℝ) by positivity)
  calc (m.totient : ℝ)/(8*m)
      = ((2^j : ℕ) : ℝ) * m.totient / (4 * m) * (1/((2^(j+1) : ℕ) : ℝ)) := heq.symm
    _ ≤ _ := h6
    _ ≤ _ := h5

/-- Dyadic decomposition: `j₁ - j₀ + 1` disjoint blocks each contribute `φ(m)/(8m)`. -/
lemma cs_dyadic (m x : ℕ) (hm : 1 ≤ m) (j₀ j₁ : ℕ) (hj : j₀ ≤ j₁)
    (h₀ : 256 * m^2 ≤ 2^j₀) (h₁ : 2^(j₁+1) ≤ x) :
    ((j₁ - j₀ + 1 : ℕ) : ℝ) * m.totient / (8 * m)
      ≤ ∑ a ∈ (Finset.Icc 1 x).filter (fun a => Squarefree a ∧ Nat.Coprime a m), (1:ℝ)/a := by
  have hdisj : (↑(Finset.Icc j₀ j₁) : Set ℕ).PairwiseDisjoint
      (fun j => (Finset.Ioc (2^j) (2^(j+1))).filter
        (fun a => Squarefree a ∧ Nat.Coprime a m)) := by
    have key : ∀ i' j' : ℕ, i' < j' → Disjoint
        ((Finset.Ioc (2^i') (2^(i'+1))).filter (fun a => Squarefree a ∧ Nat.Coprime a m))
        ((Finset.Ioc (2^j') (2^(j'+1))).filter (fun a => Squarefree a ∧ Nat.Coprime a m)) := by
      intro i' j' hij
      apply Finset.disjoint_filter_filter
      rw [Finset.Ioc_disjoint_Ioc]
      calc min (2^(i'+1)) (2^(j'+1)) ≤ 2^(i'+1) := min_le_left _ _
        _ ≤ 2^j' := Nat.pow_le_pow_right (by norm_num) (by omega)
        _ ≤ max (2^i') (2^j') := le_max_right _ _
    intro i _ j _ hne
    rcases lt_or_gt_of_ne hne with h | h
    · exact key i j h
    · exact (key j i h).symm
  have hsub : (Finset.Icc j₀ j₁).biUnion
      (fun j => (Finset.Ioc (2^j) (2^(j+1))).filter
        (fun a => Squarefree a ∧ Nat.Coprime a m))
      ⊆ (Finset.Icc 1 x).filter (fun a => Squarefree a ∧ Nat.Coprime a m) := by
    intro a ha
    simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_Ioc, Finset.mem_Icc] at ha ⊢
    obtain ⟨j, ⟨_, hjj1⟩, ⟨hja, haj⟩, hprops⟩ := ha
    refine ⟨⟨?_, ?_⟩, hprops⟩
    · have := pow_pos (show 0 < 2 by norm_num) j
      omega
    · calc a ≤ 2^(j+1) := haj
        _ ≤ 2^(j₁+1) := Nat.pow_le_pow_right (by norm_num) (by omega)
        _ ≤ x := h₁
  calc ((j₁ - j₀ + 1 : ℕ) : ℝ) * m.totient / (8 * m)
      = ∑ _j ∈ Finset.Icc j₀ j₁, (m.totient : ℝ) / (8 * m) := by
        rw [Finset.sum_const, nsmul_eq_mul, Nat.card_Icc,
          show j₁ + 1 - j₀ = j₁ - j₀ + 1 from by omega]
        ring
    _ ≤ ∑ j ∈ Finset.Icc j₀ j₁, ∑ a ∈ (Finset.Ioc (2^j) (2^(j+1))).filter
          (fun a => Squarefree a ∧ Nat.Coprime a m), (1:ℝ)/a := by
        apply Finset.sum_le_sum
        intro j hjmem
        have hj0 : j₀ ≤ j := (Finset.mem_Icc.mp hjmem).1
        exact cs_block_harmonic m j hm
          (le_trans h₀ (Nat.pow_le_pow_right (by norm_num) hj0))
    _ = ∑ a ∈ (Finset.Icc j₀ j₁).biUnion (fun j => (Finset.Ioc (2^j) (2^(j+1))).filter
          (fun a => Squarefree a ∧ Nat.Coprime a m)), (1:ℝ)/a :=
        (Finset.sum_biUnion hdisj).symm
    _ ≤ ∑ a ∈ (Finset.Icc 1 x).filter (fun a => Squarefree a ∧ Nat.Coprime a m), (1:ℝ)/a := by
        apply Finset.sum_le_sum_of_subset_of_nonneg hsub
        intro a _ _
        positivity

/-! ## From coprime pairs to the weighted sum over products -/

/-- The sum of `1/(ab)` over coprime pairs of squarefree numbers `≤ x` coprime to `m` is
dominated by the sum of `2^ω(ℓ)/ℓ` over squarefree `ℓ ≤ w` coprime to `m`, when `x² ≤ w`. -/
lemma cs_pairs_to_sum (m x w : ℕ) (hxx : x * x ≤ w) :
    ∑ q ∈ (((Finset.Icc 1 x).filter (fun a => Squarefree a ∧ Nat.Coprime a m)) ×ˢ
          ((Finset.Icc 1 x).filter (fun a => Squarefree a ∧ Nat.Coprime a m))).filter
          (fun q => Nat.Coprime q.1 q.2), (1:ℝ)/((q.1 : ℝ) * q.2)
      ≤ ∑ ℓ ∈ (Finset.Icc 1 w).filter (fun ℓ => Squarefree ℓ ∧ Nat.Coprime ℓ m),
          (2:ℝ)^(ℓ.primeFactors.card) / ℓ := by
  classical
  set T := (Finset.Icc 1 x).filter (fun a => Squarefree a ∧ Nat.Coprime a m) with hT
  set Q := (T ×ˢ T).filter (fun q : ℕ × ℕ => Nat.Coprime q.1 q.2) with hQ
  have hmem : ∀ q ∈ Q, (1 ≤ q.1 ∧ q.1 ≤ x ∧ Squarefree q.1 ∧ Nat.Coprime q.1 m) ∧
      (1 ≤ q.2 ∧ q.2 ≤ x ∧ Squarefree q.2 ∧ Nat.Coprime q.2 m) ∧ Nat.Coprime q.1 q.2 := by
    intro q hq
    simp only [hQ, hT, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hq
    tauto
  have himg : Q.image (fun q : ℕ × ℕ => q.1 * q.2)
      ⊆ (Finset.Icc 1 w).filter (fun ℓ => Squarefree ℓ ∧ Nat.Coprime ℓ m) := by
    intro ℓ hℓ
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hℓ
    obtain ⟨⟨h11, h1x, h1sq, h1m⟩, ⟨h21, h2x, h2sq, h2m⟩, h12⟩ := hmem q hq
    simp only [Finset.mem_filter, Finset.mem_Icc]
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
    · exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
    · exact le_trans (Nat.mul_le_mul h1x h2x) hxx
    · exact (Nat.squarefree_mul h12).mpr ⟨h1sq, h2sq⟩
    · exact Nat.Coprime.mul h1m h2m
  have hfiber : ∀ ℓ ∈ Q.image (fun q : ℕ × ℕ => q.1 * q.2),
      ((Q.filter (fun q : ℕ × ℕ => q.1 * q.2 = ℓ)).card : ℝ)
        ≤ (2:ℝ)^(ℓ.primeFactors.card) := by
    intro ℓ hℓ
    have hℓ0 : ℓ ≠ 0 := by
      obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hℓ
      obtain ⟨⟨h11, _, _, _⟩, ⟨h21, _, _, _⟩, _⟩ := hmem q hq
      exact Nat.mul_ne_zero (by omega) (by omega)
    have hcard : (Q.filter (fun q : ℕ × ℕ => q.1 * q.2 = ℓ)).card
        ≤ (ℓ.primeFactors.powerset).card := by
      apply Finset.card_le_card_of_injOn (fun q : ℕ × ℕ => q.1.primeFactors)
      · intro q hq
        simp only [Finset.mem_coe, Finset.mem_filter] at hq
        obtain ⟨hqQ, hqℓ⟩ := hq
        simp only [Finset.mem_coe, Finset.mem_powerset]
        exact Nat.primeFactors_mono ⟨q.2, hqℓ.symm⟩ hℓ0
      · intro q hq q' hq' heq
        simp only [Finset.mem_coe, Finset.mem_filter] at hq hq'
        obtain ⟨hqQ, hqℓ⟩ := hq
        obtain ⟨hq'Q, hq'ℓ⟩ := hq'
        obtain ⟨⟨h11, _, h1sq, _⟩, ⟨h21, _, _, _⟩, _⟩ := hmem q hqQ
        obtain ⟨⟨h11', _, h1sq', _⟩, ⟨h21', _, _, _⟩, _⟩ := hmem q' hq'Q
        have e1 : q.1 = q'.1 := by
          have p1 := Nat.prod_primeFactors_of_squarefree h1sq
          have p2 := Nat.prod_primeFactors_of_squarefree h1sq'
          rw [← p1, ← p2]
          exact Finset.prod_congr heq (fun _ _ => rfl)
        have e2 : q.2 = q'.2 := by
          have h := hqℓ.trans hq'ℓ.symm
          rw [e1] at h
          exact Nat.eq_of_mul_eq_mul_left (by omega) h
        exact Prod.ext e1 e2
    rw [Finset.card_powerset] at hcard
    calc ((Q.filter (fun q : ℕ × ℕ => q.1 * q.2 = ℓ)).card : ℝ)
        ≤ ((2^(ℓ.primeFactors.card) : ℕ) : ℝ) := by exact_mod_cast hcard
      _ = (2:ℝ)^(ℓ.primeFactors.card) := by push_cast; ring
  calc ∑ q ∈ Q, (1:ℝ)/((q.1 : ℝ) * q.2)
      = ∑ q ∈ Q, (fun ℓ : ℕ => (1:ℝ)/(ℓ:ℝ)) (q.1 * q.2) := by
        apply Finset.sum_congr rfl
        intro q _
        push_cast
        ring
    _ = ∑ ℓ ∈ Q.image (fun q : ℕ × ℕ => q.1 * q.2),
          (Q.filter (fun q : ℕ × ℕ => q.1 * q.2 = ℓ)).card • ((1:ℝ)/(ℓ:ℝ)) :=
        Finset.sum_comp (fun ℓ : ℕ => (1:ℝ)/(ℓ:ℝ)) (fun q : ℕ × ℕ => q.1 * q.2)
    _ ≤ ∑ ℓ ∈ Q.image (fun q : ℕ × ℕ => q.1 * q.2), (2:ℝ)^(ℓ.primeFactors.card) / ℓ := by
        apply Finset.sum_le_sum
        intro ℓ hℓ
        rw [nsmul_eq_mul]
        have h1 := hfiber ℓ hℓ
        have h2 : (0:ℝ) ≤ 1/(ℓ:ℝ) := by positivity
        calc ((Q.filter (fun q : ℕ × ℕ => q.1 * q.2 = ℓ)).card : ℝ) * ((1:ℝ)/(ℓ:ℝ))
            ≤ (2:ℝ)^(ℓ.primeFactors.card) * ((1:ℝ)/(ℓ:ℝ)) :=
              mul_le_mul_of_nonneg_right h1 h2
          _ = (2:ℝ)^(ℓ.primeFactors.card) / ℓ := by rw [mul_one_div]
    _ ≤ ∑ ℓ ∈ (Finset.Icc 1 w).filter (fun ℓ => Squarefree ℓ ∧ Nat.Coprime ℓ m),
          (2:ℝ)^(ℓ.primeFactors.card) / ℓ := by
        apply Finset.sum_le_sum_of_subset_of_nonneg himg
        intro ℓ _ _
        positivity

/-- Pairs with a common factor contribute at most `(3/4)·S²`. -/
lemma cs_noncop_bound (m x : ℕ) :
    ∑ q ∈ (((Finset.Icc 1 x).filter (fun a => Squarefree a ∧ Nat.Coprime a m)) ×ˢ
          ((Finset.Icc 1 x).filter (fun a => Squarefree a ∧ Nat.Coprime a m))).filter
          (fun q => ¬ Nat.Coprime q.1 q.2), (1:ℝ)/((q.1 : ℝ) * q.2)
      ≤ 3/4 * ((∑ a ∈ (Finset.Icc 1 x).filter (fun a => Squarefree a ∧ Nat.Coprime a m),
            (1:ℝ)/a)
          * (∑ a ∈ (Finset.Icc 1 x).filter (fun a => Squarefree a ∧ Nat.Coprime a m),
            (1:ℝ)/a)) := by
  classical
  set T := (Finset.Icc 1 x).filter (fun a => Squarefree a ∧ Nat.Coprime a m) with hT
  set S := ∑ a ∈ T, (1:ℝ)/a with hS
  have hbound : ∑ q ∈ (T ×ˢ T).filter (fun q : ℕ × ℕ => ¬ Nat.Coprime q.1 q.2),
        (1:ℝ)/((q.1 : ℝ) * q.2)
      ≤ ∑ r ∈ (Finset.Icc 2 x) ×ˢ (T ×ˢ T),
          (1:ℝ)/((r.1:ℝ) * r.1) * ((1:ℝ)/((r.2.1:ℝ)) * ((1:ℝ)/(r.2.2:ℝ))) := by
    apply cs_sum_le_sum_inj (fun q : ℕ × ℕ =>
      (Nat.gcd q.1 q.2, (q.1 / Nat.gcd q.1 q.2, q.2 / Nat.gcd q.1 q.2)))
    · -- maps to
      intro q hq
      simp only [hT, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hq
      obtain ⟨⟨⟨⟨h11, h1x⟩, h1sq, h1m⟩, ⟨h21, h2x⟩, h2sq, h2m⟩, hncop⟩ := hq
      have hd0 : 0 < Nat.gcd q.1 q.2 := by
        rcases Nat.eq_zero_or_pos (Nat.gcd q.1 q.2) with h | h
        · rw [Nat.gcd_eq_zero_iff] at h
          omega
        · exact h
      have hd2 : 2 ≤ Nat.gcd q.1 q.2 := by
        rcases Nat.lt_or_ge (Nat.gcd q.1 q.2) 2 with h | h
        · have h1 : Nat.gcd q.1 q.2 = 1 := by omega
          exact absurd h1 hncop
        · exact h
      have hdx : Nat.gcd q.1 q.2 ≤ x :=
        le_trans (Nat.le_of_dvd (by omega) (Nat.gcd_dvd_left _ _)) h1x
      have ha1 : q.1 / Nat.gcd q.1 q.2 ∣ q.1 :=
        ⟨Nat.gcd q.1 q.2, (Nat.div_mul_cancel (Nat.gcd_dvd_left _ _)).symm⟩
      have hb1 : q.2 / Nat.gcd q.1 q.2 ∣ q.2 :=
        ⟨Nat.gcd q.1 q.2, (Nat.div_mul_cancel (Nat.gcd_dvd_right _ _)).symm⟩
      simp only [hT, Finset.mem_product, Finset.mem_filter, Finset.mem_Icc]
      refine ⟨⟨hd2, hdx⟩, ⟨⟨?_, ?_⟩, ?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_⟩
      · exact Nat.div_pos (Nat.le_of_dvd (by omega) (Nat.gcd_dvd_left _ _)) hd0
      · exact le_trans (Nat.div_le_self _ _) h1x
      · exact Squarefree.squarefree_of_dvd ha1 h1sq
      · exact Nat.Coprime.coprime_dvd_left ha1 h1m
      · exact Nat.div_pos (Nat.le_of_dvd (by omega) (Nat.gcd_dvd_right _ _)) hd0
      · exact le_trans (Nat.div_le_self _ _) h2x
      · exact Squarefree.squarefree_of_dvd hb1 h2sq
      · exact Nat.Coprime.coprime_dvd_left hb1 h2m
    · -- injective
      intro q hq q' hq' heq
      simp only [Finset.mem_coe, hT, Finset.mem_filter, Finset.mem_product,
        Finset.mem_Icc] at hq hq'
      obtain ⟨⟨⟨⟨h11, _⟩, _, _⟩, ⟨h21, _⟩, _, _⟩, _⟩ := hq
      obtain ⟨⟨⟨⟨h11', _⟩, _, _⟩, ⟨h21', _⟩, _, _⟩, _⟩ := hq'
      simp only [Prod.mk.injEq] at heq
      obtain ⟨hd, h1, h2⟩ := heq
      have a1 : Nat.gcd q.1 q.2 * (q.1 / Nat.gcd q.1 q.2) = q.1 :=
        Nat.mul_div_cancel' (Nat.gcd_dvd_left _ _)
      have a2 : Nat.gcd q'.1 q'.2 * (q'.1 / Nat.gcd q'.1 q'.2) = q'.1 :=
        Nat.mul_div_cancel' (Nat.gcd_dvd_left _ _)
      have b1 : Nat.gcd q.1 q.2 * (q.2 / Nat.gcd q.1 q.2) = q.2 :=
        Nat.mul_div_cancel' (Nat.gcd_dvd_right _ _)
      have b2 : Nat.gcd q'.1 q'.2 * (q'.2 / Nat.gcd q'.1 q'.2) = q'.2 :=
        Nat.mul_div_cancel' (Nat.gcd_dvd_right _ _)
      have e1 : q.1 = q'.1 := by
        calc q.1 = Nat.gcd q.1 q.2 * (q.1 / Nat.gcd q.1 q.2) := a1.symm
          _ = Nat.gcd q'.1 q'.2 * (q'.1 / Nat.gcd q'.1 q'.2) := by rw [h1, hd]
          _ = q'.1 := a2
      have e2 : q.2 = q'.2 := by
        calc q.2 = Nat.gcd q.1 q.2 * (q.2 / Nat.gcd q.1 q.2) := b1.symm
          _ = Nat.gcd q'.1 q'.2 * (q'.2 / Nat.gcd q'.1 q'.2) := by rw [h2, hd]
          _ = q'.2 := b2
      exact Prod.ext e1 e2
    · -- value inequality (in fact equality)
      intro q hq
      simp only [hT, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hq
      obtain ⟨⟨⟨⟨h11, _⟩, _, _⟩, ⟨h21, _⟩, _, _⟩, _⟩ := hq
      have hd0 : 0 < Nat.gcd q.1 q.2 := by
        rcases Nat.eq_zero_or_pos (Nat.gcd q.1 q.2) with h | h
        · rw [Nat.gcd_eq_zero_iff] at h
          omega
        · exact h
      have ha : Nat.gcd q.1 q.2 * (q.1 / Nat.gcd q.1 q.2) = q.1 :=
        Nat.mul_div_cancel' (Nat.gcd_dvd_left _ _)
      have hb : Nat.gcd q.1 q.2 * (q.2 / Nat.gcd q.1 q.2) = q.2 :=
        Nat.mul_div_cancel' (Nat.gcd_dvd_right _ _)
      have ha0 : 0 < q.1 / Nat.gcd q.1 q.2 :=
        Nat.div_pos (Nat.le_of_dvd (by omega) (Nat.gcd_dvd_left _ _)) hd0
      have hb0 : 0 < q.2 / Nat.gcd q.1 q.2 :=
        Nat.div_pos (Nat.le_of_dvd (by omega) (Nat.gcd_dvd_right _ _)) hd0
      have haR : (q.1 : ℝ) = (Nat.gcd q.1 q.2 : ℝ) * ((q.1 / Nat.gcd q.1 q.2 : ℕ) : ℝ) := by
        exact_mod_cast ha.symm
      have hbR : (q.2 : ℝ) = (Nat.gcd q.1 q.2 : ℝ) * ((q.2 / Nat.gcd q.1 q.2 : ℕ) : ℝ) := by
        exact_mod_cast hb.symm
      have hdR : (0:ℝ) < (Nat.gcd q.1 q.2 : ℝ) := by exact_mod_cast hd0
      have haR0 : (0:ℝ) < ((q.1 / Nat.gcd q.1 q.2 : ℕ) : ℝ) := by exact_mod_cast ha0
      have hbR0 : (0:ℝ) < ((q.2 / Nat.gcd q.1 q.2 : ℕ) : ℝ) := by exact_mod_cast hb0
      apply le_of_eq
      rw [haR, hbR]
      field_simp
    · -- nonnegativity on the target
      intro r _
      positivity
  have hinner : ∑ p ∈ T ×ˢ T, ((1:ℝ)/(p.1:ℝ)) * ((1:ℝ)/(p.2:ℝ)) = S * S := by
    calc ∑ p ∈ T ×ˢ T, ((1:ℝ)/(p.1:ℝ)) * ((1:ℝ)/(p.2:ℝ))
        = ∑ a ∈ T, ∑ b ∈ T, ((1:ℝ)/(a:ℝ)) * ((1:ℝ)/(b:ℝ)) := Finset.sum_product _ _ _
      _ = S * S := (Finset.sum_mul_sum T T (fun a => (1:ℝ)/(a:ℝ)) (fun b => (1:ℝ)/(b:ℝ))).symm
  have hteval : ∑ r ∈ (Finset.Icc 2 x) ×ˢ (T ×ˢ T),
        (1:ℝ)/((r.1:ℝ) * r.1) * ((1:ℝ)/((r.2.1:ℝ)) * ((1:ℝ)/(r.2.2:ℝ)))
      = (∑ d ∈ Finset.Icc 2 x, (1:ℝ)/((d:ℝ)*d)) * (S * S) := by
    calc ∑ r ∈ (Finset.Icc 2 x) ×ˢ (T ×ˢ T),
          (1:ℝ)/((r.1:ℝ) * r.1) * ((1:ℝ)/((r.2.1:ℝ)) * ((1:ℝ)/(r.2.2:ℝ)))
        = ∑ d ∈ Finset.Icc 2 x, ∑ p ∈ T ×ˢ T,
            (1:ℝ)/((d:ℝ) * d) * (((1:ℝ)/(p.1:ℝ)) * ((1:ℝ)/(p.2:ℝ))) := Finset.sum_product _ _ _
      _ = ∑ d ∈ Finset.Icc 2 x, (1:ℝ)/((d:ℝ) * d) * (S * S) := by
          apply Finset.sum_congr rfl
          intro d _
          rw [← Finset.mul_sum, hinner]
      _ = (∑ d ∈ Finset.Icc 2 x, (1:ℝ)/((d:ℝ)*d)) * (S * S) :=
          (Finset.sum_mul (Finset.Icc 2 x) (fun d => (1:ℝ)/((d:ℝ)*d)) (S * S)).symm
  have hd34 := cs_inv_sq_sum_ge2 (Finset.Icc 2 x) (fun d hd => (Finset.mem_Icc.mp hd).1)
  have hSS : (0:ℝ) ≤ S * S := mul_self_nonneg S
  calc ∑ q ∈ (T ×ˢ T).filter (fun q : ℕ × ℕ => ¬ Nat.Coprime q.1 q.2),
        (1:ℝ)/((q.1 : ℝ) * q.2)
      ≤ ∑ r ∈ (Finset.Icc 2 x) ×ˢ (T ×ˢ T),
          (1:ℝ)/((r.1:ℝ) * r.1) * ((1:ℝ)/((r.2.1:ℝ)) * ((1:ℝ)/(r.2.2:ℝ))) := hbound
    _ = (∑ d ∈ Finset.Icc 2 x, (1:ℝ)/((d:ℝ)*d)) * (S * S) := hteval
    _ ≤ 3/4 * (S * S) := mul_le_mul_of_nonneg_right hd34 hSS

/-- The coprime-pair sum is at least a quarter of the squared harmonic sum. -/
lemma cs_coprime_pairs_lower (m x : ℕ) :
    (∑ a ∈ (Finset.Icc 1 x).filter (fun a => Squarefree a ∧ Nat.Coprime a m), (1:ℝ)/a)
    * (∑ a ∈ (Finset.Icc 1 x).filter (fun a => Squarefree a ∧ Nat.Coprime a m), (1:ℝ)/a) / 4
      ≤ ∑ q ∈ (((Finset.Icc 1 x).filter (fun a => Squarefree a ∧ Nat.Coprime a m)) ×ˢ
            ((Finset.Icc 1 x).filter (fun a => Squarefree a ∧ Nat.Coprime a m))).filter
            (fun q => Nat.Coprime q.1 q.2), (1:ℝ)/((q.1 : ℝ) * q.2) := by
  classical
  set T := (Finset.Icc 1 x).filter (fun a => Squarefree a ∧ Nat.Coprime a m) with hT
  set S := ∑ a ∈ T, (1:ℝ)/a with hS
  have htotal : ∑ q ∈ T ×ˢ T, (1:ℝ)/((q.1:ℝ) * q.2) = S * S := by
    calc ∑ q ∈ T ×ˢ T, (1:ℝ)/((q.1:ℝ) * q.2)
        = ∑ a ∈ T, ∑ b ∈ T, (1:ℝ)/((a:ℝ) * b) := Finset.sum_product _ _ _
      _ = ∑ a ∈ T, ∑ b ∈ T, ((1:ℝ)/(a:ℝ)) * ((1:ℝ)/(b:ℝ)) := by
          apply Finset.sum_congr rfl
          intro a _
          apply Finset.sum_congr rfl
          intro b _
          rw [div_mul_div_comm, one_mul]
      _ = S * S := (Finset.sum_mul_sum T T (fun a => (1:ℝ)/(a:ℝ)) (fun b => (1:ℝ)/(b:ℝ))).symm
  have hsplit := Finset.sum_filter_add_sum_filter_not (T ×ˢ T)
    (fun q : ℕ × ℕ => Nat.Coprime q.1 q.2) (fun q : ℕ × ℕ => (1:ℝ)/((q.1:ℝ) * q.2))
  have hnon := cs_noncop_bound m x
  rw [← hT, ← hS] at hnon
  linarith [hsplit, htotal, hnon]

/-! ## Choice of dyadic parameters -/

/-- `log y ≤ 2√y - 2` for positive `y`. -/
lemma cs_log_le_two_sqrt (y : ℝ) (hy : 0 < y) : Real.log y ≤ 2 * Real.sqrt y - 2 := by
  have h1 : Real.log (Real.sqrt y) ≤ Real.sqrt y - 1 :=
    Real.log_le_sub_one_of_pos (Real.sqrt_pos.mpr hy)
  have h2 : Real.log (Real.sqrt y) = Real.log y / 2 := Real.log_sqrt hy.le
  linarith

/-- For `w ≥ 2^15000` and `1 ≤ m ≤ (log w)³` there is a long run of dyadic blocks
between `256·m²` and `√w`. -/
lemma cs_params (w m : ℕ) (hw : 2^15000 ≤ w) (hm : 1 ≤ m)
    (hmw : (m:ℝ) ≤ (Real.log w)^3) :
    ∃ j₀ j₁ : ℕ, j₀ ≤ j₁ ∧ 256 * m^2 ≤ 2^j₀ ∧ 2^(j₁+1) ≤ Nat.sqrt w ∧
      Real.log w / 8 ≤ ((j₁ - j₀ + 1 : ℕ) : ℝ) := by
  set x := Nat.sqrt w with hxdef
  set a := Nat.log 2 (256 * m^2) with hadef
  set b := Nat.log 2 x with hbdef
  set L := Real.log w with hLdef
  have hw1 : 1 ≤ w := le_trans Nat.one_le_two_pow hw
  have hwR : (1:ℝ) ≤ (w:ℝ) := by exact_mod_cast hw1
  have hwR0 : (0:ℝ) < (w:ℝ) := by linarith
  have hx1 : 1 ≤ x := by
    rw [hxdef]
    exact Nat.le_sqrt.mpr (by omega)
  have hxR0 : (0:ℝ) < (x:ℝ) := by exact_mod_cast hx1
  have hmR1 : (1:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm
  have hlog2pos : (0:ℝ) < Real.log 2 := by linarith [Real.log_two_gt_d9]
  have h256 : 0 < 256 * m^2 := Nat.mul_pos (by norm_num) (pow_pos hm 2)
  -- `L` is large
  have hL : 10397 ≤ L := by
    have h1 : ((2:ℝ))^(15000:ℕ) ≤ (w:ℝ) := by exact_mod_cast hw
    have h2 : Real.log ((2:ℝ)^(15000:ℕ)) ≤ L := Real.log_le_log (by positivity) h1
    rw [Real.log_pow] at h2
    push_cast at h2
    linarith [Real.log_two_gt_d9]
  have hL0 : (0:ℝ) < L := by linarith
  -- `log x > L/2 - log 2`
  have hXlow : L/2 - Real.log 2 < Real.log x := by
    have h1 := Nat.lt_succ_sqrt w
    simp only [Nat.succ_eq_add_one] at h1
    rw [← hxdef] at h1
    have hxx : w < 4*(x*x) := by
      calc w < (x+1)*(x+1) := h1
        _ ≤ (2*x)*(2*x) := Nat.mul_le_mul (by omega) (by omega)
        _ = 4*(x*x) := by ring
    have hcast : (w:ℝ) < 4*((x:ℝ)*(x:ℝ)) := by exact_mod_cast hxx
    have hxne : (x:ℝ) ≠ 0 := ne_of_gt hxR0
    have h3 : L < Real.log (4*((x:ℝ)*(x:ℝ))) := Real.log_lt_log hwR0 hcast
    rw [Real.log_mul (by norm_num) (mul_ne_zero hxne hxne), Real.log_mul hxne hxne] at h3
    have h4 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4:ℝ) = 2^(2:ℕ) by norm_num, Real.log_pow]
      push_cast
      ring
    linarith
  -- upper bound on `a·log 2`
  have haR : (a:ℝ) * Real.log 2 ≤ 8 * Real.log 2 + 6 * Real.log L := by
    have h1 : (2:ℕ)^(Nat.log 2 (256 * m^2)) ≤ 256 * m^2 := Nat.pow_log_le_self 2 h256.ne'
    rw [← hadef] at h1
    have h2 : ((2:ℝ))^a ≤ ((256 * m^2 : ℕ):ℝ) := by exact_mod_cast h1
    have h3 : Real.log ((2:ℝ)^a) ≤ Real.log ((256*m^2 : ℕ):ℝ) :=
      Real.log_le_log (by positivity) h2
    rw [Real.log_pow] at h3
    have hmne : (m:ℝ) ≠ 0 := by linarith
    have h4 : Real.log ((256*m^2 : ℕ):ℝ) = 8*Real.log 2 + 2*Real.log m := by
      have hc : ((256*m^2 : ℕ):ℝ) = 256 * (m:ℝ)^2 := by push_cast; ring
      rw [hc, Real.log_mul (by norm_num) (pow_ne_zero 2 hmne), Real.log_pow,
        show (256:ℝ) = 2^(8:ℕ) by norm_num, Real.log_pow]
      push_cast
      ring
    have h5 : Real.log (m:ℝ) ≤ 3 * Real.log L := by
      have h6 : Real.log (m:ℝ) ≤ Real.log (L^(3:ℕ)) :=
        Real.log_le_log (by linarith) hmw
      rwa [Real.log_pow, show ((3:ℕ):ℝ) = 3 by norm_num] at h6
    linarith
  -- lower bound on `b·log 2`
  have hbR : Real.log x < (b:ℝ) * Real.log 2 + Real.log 2 := by
    have h1 := Nat.lt_pow_succ_log_self (show (1:ℕ) < 2 by norm_num) x
    simp only [Nat.succ_eq_add_one] at h1
    rw [← hbdef] at h1
    have h2 : (x:ℝ) < (2:ℝ)^(b+1) := by exact_mod_cast h1
    have h3 : Real.log x < Real.log ((2:ℝ)^(b+1)) := Real.log_lt_log hxR0 h2
    rw [Real.log_pow] at h3
    push_cast at h3
    linarith
  -- `√L` bounds
  have hsq : Real.sqrt L * Real.sqrt L = L := Real.mul_self_sqrt hL0.le
  have hsq101 : (101:ℝ) ≤ Real.sqrt L := by
    refine (Real.le_sqrt (by norm_num) hL0.le).mpr ?_
    norm_num
    linarith
  have hsqL : Real.sqrt L ≤ L / 101 := by
    rw [le_div_iff₀ (by norm_num)]
    nlinarith [hsq, hsq101, Real.sqrt_nonneg L]
  have hlogL : Real.log L ≤ 2 * Real.sqrt L - 2 := cs_log_le_two_sqrt L hL0
  have hLlog2 : L * Real.log 2 ≤ 0.6931471808 * L := by
    have := mul_le_mul_of_nonneg_left (le_of_lt Real.log_two_lt_d9) hL0.le
    linarith
  -- `b - a` is large
  have hba : (a:ℝ) + 3 < (b:ℝ) := by
    by_contra hcon
    push_neg at hcon
    have h1 : (b:ℝ) * Real.log 2 ≤ ((a:ℝ) + 3) * Real.log 2 :=
      mul_le_mul_of_nonneg_right hcon hlog2pos.le
    have h2 : ((a:ℝ)+3) * Real.log 2 = (a:ℝ)*Real.log 2 + 3*Real.log 2 := by ring
    linarith [Real.log_two_lt_d9]
  have hban : a + 3 < b := by exact_mod_cast hba
  -- the block count is large
  have hcnt : L/8 + 1 ≤ (b:ℝ) - a := by
    by_contra hcon
    push_neg at hcon
    have h1 : ((b:ℝ) - a) * Real.log 2 ≤ (L/8 + 1) * Real.log 2 :=
      mul_le_mul_of_nonneg_right (le_of_lt hcon) hlog2pos.le
    have h2 : ((b:ℝ) - a) * Real.log 2 = (b:ℝ)*Real.log 2 - (a:ℝ)*Real.log 2 := by ring
    have h3 : (L/8 + 1) * Real.log 2 = L*Real.log 2/8 + Real.log 2 := by ring
    linarith [Real.log_two_lt_d9]
  refine ⟨a + 1, b - 1, by omega, ?_, ?_, ?_⟩
  · have h1 := Nat.lt_pow_succ_log_self (show (1:ℕ) < 2 by norm_num) (256*m^2)
    simp only [Nat.succ_eq_add_one] at h1
    rw [← hadef] at h1
    exact h1.le
  · rw [show b - 1 + 1 = b from by omega, hbdef]
    exact Nat.pow_log_le_self 2 (by omega)
  · rw [show (b - 1) - (a + 1) + 1 = b - a - 1 from by omega]
    have hc : ((b - a - 1 : ℕ):ℝ) = (b:ℝ) - a - 1 := by
      rw [show b - a - 1 = b - (a + 1) from by omega,
        Nat.cast_sub (by omega : a + 1 ≤ b)]
      push_cast
      ring
    rw [hc]
    linarith

/-! ## The exported theorem -/

/-- **Lemma B.3** (blueprint): for all large `w` and all `1 ≤ m ≤ (log w)³`,
`Σ_{ℓ ≤ w, squarefree, coprime to m} 2^ω(ℓ)/ℓ ≥ c₀·(φ(m)/m)²·(log w)²`. -/
theorem coprime_squarefree_sum_lower :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∃ w₀ : ℕ, ∀ w : ℕ, w₀ ≤ w → ∀ m : ℕ, 1 ≤ m → (m : ℝ) ≤ (Real.log w)^3 →
      c₀ * ((Nat.totient m : ℝ)/m)^2 * (Real.log w)^2
        ≤ ∑ ℓ ∈ (Finset.Icc 1 w).filter (fun ℓ => Squarefree ℓ ∧ ℓ.Coprime m),
            (2:ℝ)^(ℓ.primeFactors.card) / ℓ := by
  refine ⟨1/16384, by norm_num, 2^15000, ?_⟩
  intro w hw m hm hmw
  obtain ⟨j₀, j₁, hj, h0, h1, hcount⟩ := cs_params w m hw hm hmw
  have hxx : Nat.sqrt w * Nat.sqrt w ≤ w := by
    have := Nat.sqrt_le' w
    rwa [pow_two] at this
  have hS := cs_dyadic m (Nat.sqrt w) hm j₀ j₁ hj h0 h1
  have hpair := cs_coprime_pairs_lower m (Nat.sqrt w)
  have hsum := cs_pairs_to_sum m (Nat.sqrt w) w hxx
  set S := ∑ a ∈ (Finset.Icc 1 (Nat.sqrt w)).filter
      (fun a => Squarefree a ∧ Nat.Coprime a m), (1:ℝ)/a with hSdef
  set L := Real.log w with hLdef
  set φ := (m.totient : ℝ) with hφdef
  set M := (m : ℝ) with hMdef
  have hM1 : (1:ℝ) ≤ M := by
    rw [hMdef]
    exact_mod_cast hm
  have hM0 : (0:ℝ) < M := by linarith
  have hMne : M ≠ 0 := ne_of_gt hM0
  have hφ0 : (0:ℝ) < φ := by
    rw [hφdef]
    exact_mod_cast Nat.totient_pos.mpr hm
  have hL0 : (0:ℝ) ≤ L := by
    rw [hLdef]
    apply Real.log_nonneg
    have hw1 : 1 ≤ w := le_trans Nat.one_le_two_pow hw
    exact_mod_cast hw1
  have hS0 : (0:ℝ) ≤ S := by
    rw [hSdef]
    exact Finset.sum_nonneg (fun a _ => by positivity)
  have hφM : (0:ℝ) ≤ φ/(8*M) := div_nonneg hφ0.le (by linarith)
  -- S is large
  have hc1 : L/8 * (φ/(8*M)) ≤ ((j₁ - j₀ + 1 : ℕ):ℝ) * (φ/(8*M)) :=
    mul_le_mul_of_nonneg_right hcount hφM
  have he : ((j₁ - j₀ + 1 : ℕ):ℝ) * (φ/(8*M)) = ((j₁ - j₀ + 1 : ℕ):ℝ) * φ/(8*M) := by
    ring
  have hSlow : L/8 * (φ/(8*M)) ≤ S := by linarith [hS, hc1, he]
  have hSlow0 : (0:ℝ) ≤ L/8 * (φ/(8*M)) :=
    mul_nonneg (div_nonneg hL0 (by norm_num)) hφM
  have hsq := mul_self_le_mul_self hSlow0 hSlow
  have heq : 1/16384 * (φ/M)^2 * L^2
      = (L/8 * (φ/(8*M))) * (L/8 * (φ/(8*M))) / 4 := by
    field_simp
    ring
  calc 1/16384 * (φ/M)^2 * L^2
      = (L/8 * (φ/(8*M))) * (L/8 * (φ/(8*M))) / 4 := heq
    _ ≤ S * S / 4 := by linarith [hsq]
    _ ≤ _ := hpair
    _ ≤ _ := hsum

end Erdos884
end

/-! Flattened from Erdos884/PairSieveCore884.lean. -/
section

/-!
# Erdős 884 — the pair sieve (Lemma B, bullets 1–5)

A Selberg sieve detecting prime pairs `(n, n+h)`: we sieve the values `n(n+h)` for
`n ∈ [1, M]` by the primes up to `z`.  The density is `ν(d) = ρ_h(d)/d` where `ρ_h` is
multiplicative with `ρ_h(p) = 1` if `p ∣ 2h` and `2` otherwise (the number of roots of
`X(X+h) mod p` for even `h`; using `2h` instead of `h` makes `ν(2) = 1/2 < 1`
unconditionally, and agrees with the root count whenever `h` is even).
-/

namespace Erdos884

open Finset ArithmeticFunction
open scoped ArithmeticFunction.omega

/-- `ρ_h`: the multiplicative function with `ρ_h(p) = 1` if `p ∣ 2h` and `2` otherwise. -/
noncomputable def rhoFun (h : ℕ) : ArithmeticFunction ℝ :=
  ArithmeticFunction.prodPrimeFactors (fun p => if p ∣ 2 * h then (1 : ℝ) else 2)

lemma rhoFun_apply_prime {p : ℕ} (hp : p.Prime) (h : ℕ) :
    rhoFun h p = if p ∣ 2 * h then (1 : ℝ) else 2 := by
  rw [rhoFun, ArithmeticFunction.prodPrimeFactors_apply hp.ne_zero, hp.primeFactors,
    Finset.prod_singleton]

/-- The density function of the pair sieve: `ν(d) = ρ_h(d)/d`. -/
noncomputable def pairNu (h : ℕ) : ArithmeticFunction ℝ := (rhoFun h).pdiv .id

lemma pairNu_apply (h d : ℕ) : pairNu h d = rhoFun h d / d := by
  simp [pairNu, ArithmeticFunction.pdiv_apply, ArithmeticFunction.natCoe_apply,
    ArithmeticFunction.id_apply]

/-- The Selberg sieve detecting prime pairs `(n, n+h)`, `n ∈ [1,M]`, sieving by primes
`≤ z`.  Support: the values `n(n+h)`; weights `1`; total mass `M`; level `z`. -/
noncomputable def pairSieve (M h : ℕ) (z : ℝ) (hz : 1 ≤ z) : SelbergSieve where
  support := (Finset.Icc 1 M).image (fun n => n * (n + h))
  prodPrimes := primorial ⌊z⌋₊
  prodPrimes_squarefree := Sieve.primorial_squarefree _
  weights := fun _ => 1
  weights_nonneg := fun _ => zero_le_one
  totalMass := (M : ℝ)
  nu := pairNu h
  nu_mult := by unfold pairNu rhoFun; arith_mult
  nu_pos_of_prime := fun p hp _ => by
    simp only [pairNu, ArithmeticFunction.pdiv_apply, rhoFun_apply_prime hp,
      ArithmeticFunction.natCoe_apply, ArithmeticFunction.id_apply]
    have hp0 : (0:ℝ) < p := by exact_mod_cast hp.pos
    split_ifs <;> positivity
  nu_lt_one_of_prime := fun p hp _ => by
    simp only [pairNu, ArithmeticFunction.pdiv_apply, rhoFun_apply_prime hp,
      ArithmeticFunction.natCoe_apply, ArithmeticFunction.id_apply]
    have hp0 : (0:ℝ) < p := by exact_mod_cast hp.pos
    rw [div_lt_one hp0]
    split_ifs with hdvd
    · exact_mod_cast hp.one_lt
    · have hp2 : p ≠ 2 := fun h2 => hdvd (h2 ▸ ⟨h, rfl⟩)
      have h3 : 3 ≤ p := by have := hp.two_le; omega
      exact_mod_cast (by omega : 2 < p)
  level := z
  one_le_level := hz

@[simp] lemma pairSieve_prodPrimes (M h : ℕ) (z : ℝ) (hz : 1 ≤ z) :
    (pairSieve M h z hz).prodPrimes = primorial ⌊z⌋₊ := rfl

@[simp] lemma pairSieve_level (M h : ℕ) (z : ℝ) (hz : 1 ≤ z) :
    (pairSieve M h z hz).level = z := rfl

@[simp] lemma pairSieve_nu (M h : ℕ) (z : ℝ) (hz : 1 ≤ z) :
    (pairSieve M h z hz).nu = pairNu h := rfl

@[simp] lemma pairSieve_totalMass (M h : ℕ) (z : ℝ) (hz : 1 ≤ z) :
    (pairSieve M h z hz).totalMass = (M : ℝ) := rfl

/-- Positivity of the Selberg bounding sum of the pair sieve (re-export of
`SelbergSieve.selbergBoundingSum_pos` for downstream use). -/
theorem pairSieve_boundingSum_pos (M h : ℕ) (z : ℝ) (hz : 1 ≤ z) :
    (pairSieve M h z hz).selbergBoundingSum > 0 :=
  SelbergSieve.selbergBoundingSum_pos _

/-! ## Counting the roots of `X(X+h)` modulo `d` -/

/-- The number of residues `r < d` with `d ∣ r(r+h)`. -/
def nroots (h d : ℕ) : ℕ := ((Finset.range d).filter (fun r => d ∣ r * (r + h))).card

lemma nroots_zero (h : ℕ) : nroots h 0 = 0 := by simp [nroots]

lemma nroots_one (h : ℕ) : nroots h 1 = 1 := by simp [nroots]

/-- Divisibility of `n(n+h)` by `d` only depends on `n mod d`. -/
lemma dvd_shift_iff_mod (d h n : ℕ) : d ∣ n * (n + h) ↔ d ∣ (n % d) * (n % d + h) := by
  have h1 : (n % d) * (n % d + h) ≡ n * (n + h) [MOD d] :=
    (Nat.mod_modEq n d).mul ((Nat.mod_modEq n d).add_right h)
  constructor
  · intro hdvd
    exact Nat.modEq_zero_iff_dvd.mp (h1.trans (Nat.modEq_zero_iff_dvd.mpr hdvd))
  · intro hdvd
    exact Nat.modEq_zero_iff_dvd.mp (h1.symm.trans (Nat.modEq_zero_iff_dvd.mpr hdvd))

/-- The root count as the size of the zero set of `x(x+h)` in `ZMod d`. -/
lemma nroots_eq_card_zmod (h d : ℕ) [NeZero d] :
    nroots h d =
      (Finset.univ.filter (fun x : ZMod d => x * (x + (h : ZMod d)) = 0)).card := by
  unfold nroots
  apply Finset.card_bij (fun (r : ℕ) _ => (r : ZMod d))
  · intro r hr
    simp only [Finset.mem_filter, Finset.mem_range] at hr
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    have hc : ((r * (r + h) : ℕ) : ZMod d) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr hr.2
    push_cast at hc
    exact hc
  · intro r₁ hr₁ r₂ hr₂ heq
    simp only [Finset.mem_filter, Finset.mem_range] at hr₁ hr₂
    have := congrArg ZMod.val heq
    rwa [ZMod.val_cast_of_lt hr₁.1, ZMod.val_cast_of_lt hr₂.1] at this
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
    have hval : x.val ∈ (Finset.range d).filter (fun r => d ∣ r * (r + h)) := by
      simp only [Finset.mem_filter, Finset.mem_range]
      refine ⟨ZMod.val_lt x, (ZMod.natCast_eq_zero_iff _ _).mp ?_⟩
      push_cast
      rw [ZMod.natCast_rightInverse x]
      exact hx
    exact ⟨x.val, hval, ZMod.natCast_rightInverse x⟩

/-- CRT: the root count is multiplicative. -/
lemma nroots_mul (h : ℕ) {m n : ℕ} (hcop : Nat.Coprime m n) :
    nroots h (m * n) = nroots h m * nroots h n := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · have hn1 : n = 1 := by simpa using hcop
    subst hn1; simp [nroots_zero, nroots_one]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have hm1 : m = 1 := by simpa using hcop
    subst hm1; simp [nroots_zero, nroots_one]
  haveI : NeZero m := ⟨hm.ne'⟩
  haveI : NeZero n := ⟨hn.ne'⟩
  haveI : NeZero (m * n) := ⟨by positivity⟩
  rw [nroots_eq_card_zmod, nroots_eq_card_zmod, nroots_eq_card_zmod,
    ← Finset.card_product, ← Finset.filter_product, Finset.univ_product_univ]
  have crt := ZMod.chineseRemainder hcop
  have hiff : ∀ x : ZMod (m * n),
      (x * (x + (h : ZMod (m * n))) = 0) ↔
        ((crt x).1 * ((crt x).1 + (h : ZMod m)) = 0 ∧
          (crt x).2 * ((crt x).2 + (h : ZMod n)) = 0) := by
    intro x
    rw [← EmbeddingLike.map_eq_zero_iff (f := crt), map_mul, map_add, map_natCast,
      Prod.ext_iff]
    simp [Prod.fst_mul, Prod.fst_add, Prod.snd_mul, Prod.snd_add]
  apply Finset.card_bij (fun x _ => crt x)
  · intro x hxmem
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hxmem ⊢
    exact (hiff x).mp hxmem
  · intro x₁ _ x₂ _ heq
    exact crt.injective heq
  · intro y hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
    refine ⟨crt.symm y, ?_, crt.apply_symm_apply y⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [hiff (crt.symm y), crt.apply_symm_apply y]
    exact hy

/-- Root count at a prime: `1` root if `p ∣ 2h`, else `2` (`h` even). -/
lemma nroots_prime {p : ℕ} (hp : p.Prime) {h : ℕ} (heven : 2 ∣ h) :
    nroots h p = if p ∣ 2 * h then 1 else 2 := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  haveI : Fact p.Prime := ⟨hp⟩
  rw [nroots_eq_card_zmod]
  have hset : (Finset.univ.filter (fun x : ZMod p => x * (x + (h : ZMod p)) = 0))
      = {0, -(h : ZMod p)} := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton]
    constructor
    · intro hx
      rcases mul_eq_zero.mp hx with h0 | h1
      · exact Or.inl h0
      · exact Or.inr (eq_neg_of_add_eq_zero_left h1)
    · rintro (rfl | rfl)
      · simp
      · simp
  rw [hset]
  by_cases hph : p ∣ h
  · have h0 : (h : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr hph
    rw [if_pos (hph.mul_left 2), h0, neg_zero]
    simp
  · have h0 : (h : ZMod p) ≠ 0 := fun hc => hph ((ZMod.natCast_eq_zero_iff _ _).mp hc)
    have hnodvd : ¬ p ∣ 2 * h := by
      intro hc
      rcases (Nat.Prime.dvd_mul hp).mp hc with h2 | hh
      · have hp2 : p = 2 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h2
        exact hph (hp2 ▸ heven)
      · exact hph hh
    rw [if_neg hnodvd]
    have hne : (0 : ZMod p) ∉ ({-(h : ZMod p)} : Finset (ZMod p)) := by
      simp only [Finset.mem_singleton]
      intro hc
      exact h0 (neg_eq_zero.mp hc.symm)
    rw [Finset.card_insert_of_notMem hne, Finset.card_singleton]

/-! ## `ρ_h` equals the root count on squarefree numbers (for even `h`) -/

/-- The root count as an arithmetic function. -/
def nrootsA (h : ℕ) : ArithmeticFunction ℕ := ⟨nroots h, nroots_zero h⟩

@[simp] lemma nrootsA_apply (h d : ℕ) : nrootsA h d = nroots h d := rfl

lemma nrootsA_isMultiplicative (h : ℕ) : (nrootsA h).IsMultiplicative := by
  constructor
  · exact nroots_one h
  · intro m n hcop
    exact nroots_mul h hcop

lemma nroots_eq_prod_primeFactors (h : ℕ) {d : ℕ} (hd : Squarefree d) :
    nroots h d = ∏ p ∈ d.primeFactors, nroots h p := by
  have hmap := (nrootsA_isMultiplicative h).map_prod_of_subset_primeFactors d
    d.primeFactors Finset.Subset.rfl
  simp only [nrootsA_apply] at hmap
  conv_lhs => rw [← Nat.prod_primeFactors_of_squarefree hd]
  exact hmap

lemma rhoFun_eq_nroots {h : ℕ} (heven : 2 ∣ h) {d : ℕ} (hd : Squarefree d) :
    rhoFun h d = (nroots h d : ℝ) := by
  rw [rhoFun, ArithmeticFunction.prodPrimeFactors_apply hd.ne_zero,
    nroots_eq_prod_primeFactors h hd]
  push_cast
  apply Finset.prod_congr rfl
  intro p hp
  rw [nroots_prime (Nat.prime_of_mem_primeFactors hp) heven]
  split_ifs <;> norm_num

lemma rhoFun_nonneg (h d : ℕ) : 0 ≤ rhoFun h d := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp
  · rw [rhoFun, ArithmeticFunction.prodPrimeFactors_apply hd.ne']
    apply Finset.prod_nonneg
    intro p _
    split_ifs <;> norm_num

lemma rhoFun_le_two_pow (h : ℕ) {d : ℕ} (hd : d ≠ 0) :
    rhoFun h d ≤ 2 ^ d.primeFactors.card := by
  rw [rhoFun, ArithmeticFunction.prodPrimeFactors_apply hd]
  calc ∏ p ∈ d.primeFactors, (if p ∣ 2 * h then (1:ℝ) else 2)
      ≤ ∏ p ∈ d.primeFactors, (2:ℝ) := by
        apply Finset.prod_le_prod
        · intro p _; split_ifs <;> norm_num
        · intro p _; split_ifs <;> norm_num
    _ = 2 ^ d.primeFactors.card := by rw [Finset.prod_const]

/-! ## Counting a residue class in `[1, M]` -/

lemma range_succ_eq_insert_Icc (M : ℕ) :
    Finset.range (M + 1) = insert 0 (Finset.Icc 1 M) := by
  ext n
  simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
  omega

/-- The number of `n ∈ [1, M]` in a fixed residue class mod `d` is within `1`
of `M/d`. -/
lemma card_Icc_filter_mod (M : ℕ) {d r : ℕ} (hd : 0 < d) (hr : r < d) :
    |(((Finset.Icc 1 M).filter (fun n => n % d = r)).card : ℝ) - M / d| ≤ 1 := by
  have hcount : ((Finset.range (M + 1)).filter (fun n => n % d = r)).card
      = (M + 1) / d + if r < (M + 1) % d then 1 else 0 := by
    have h1 : (Finset.range (M + 1)).filter (fun n => n % d = r)
        = (Finset.range (M + 1)).filter (fun x => x ≡ r [MOD d]) := by
      apply Finset.filter_congr
      intro n _
      simp [Nat.ModEq, Nat.mod_eq_of_lt hr]
    rw [h1, ← Nat.count_eq_card_filter_range, Nat.count_modEq_card _ hd r,
      Nat.mod_eq_of_lt hr]
  have hsplit : ((Finset.range (M + 1)).filter (fun n => n % d = r)).card
      = ((Finset.Icc 1 M).filter (fun n => n % d = r)).card
        + if r = 0 then 1 else 0 := by
    rw [range_succ_eq_insert_Icc, Finset.filter_insert]
    by_cases hr0 : r = 0
    · rw [if_pos (show (0:ℕ) % d = r by rw [Nat.zero_mod, hr0]), if_pos hr0,
        Finset.card_insert_of_notMem (by simp)]
    · rw [if_neg (show ¬ (0:ℕ) % d = r by
        rw [Nat.zero_mod]; exact fun hc => hr0 hc.symm), if_neg hr0, add_zero]
  have hkey : ((Finset.Icc 1 M).filter (fun n => n % d = r)).card
        + (if r = 0 then 1 else 0)
      = (M + 1) / d + if r < (M + 1) % d then 1 else 0 := by
    rw [← hsplit, hcount]
  have hdm : d * ((M + 1) / d) + (M + 1) % d = M + 1 := Nat.div_add_mod (M + 1) d
  have hsd : (M + 1) % d < d := Nat.mod_lt _ hd
  set c := ((Finset.Icc 1 M).filter (fun n => n % d = r)).card with hcdef
  set a := (M + 1) / d with hadef
  set s := (M + 1) % d with hsdef
  have hdR : (0:ℝ) < d := by exact_mod_cast hd
  have hdmR : (d:ℝ) * a + s = M + 1 := by exact_mod_cast hdm
  have hsdR : (s:ℝ) + 1 ≤ d := by exact_mod_cast hsd
  have hs0 : (0:ℝ) ≤ s := by positivity
  have hub : (M:ℝ) / d ≤ c + 1 := by
    rw [div_le_iff₀ hdR]
    rcases eq_or_ne r 0 with hr0 | hr0
    · rw [if_pos hr0] at hkey
      by_cases hε : r < s
      · rw [if_pos hε] at hkey
        have hca : (c:ℝ) = a := by exact_mod_cast (by omega : c = a)
        rw [hca]; nlinarith
      · rw [if_neg hε] at hkey
        have hs0' : s = 0 := by omega
        have hca : (c:ℝ) + 1 = a := by exact_mod_cast hkey
        have : (s:ℝ) = 0 := by exact_mod_cast hs0'
        nlinarith
    · rw [if_neg hr0] at hkey
      by_cases hε : r < s
      · rw [if_pos hε] at hkey
        have hca : (c:ℝ) = a + 1 := by exact_mod_cast hkey
        rw [hca]; nlinarith
      · rw [if_neg hε] at hkey
        have hca : (c:ℝ) = a := by exact_mod_cast (by omega : c = a)
        rw [hca]; nlinarith
  have hlb : (c:ℝ) - 1 ≤ M / d := by
    rw [le_div_iff₀ hdR]
    rcases eq_or_ne r 0 with hr0 | hr0
    · rw [if_pos hr0] at hkey
      by_cases hε : r < s
      · rw [if_pos hε] at hkey
        have hs1 : (1:ℝ) ≤ s := by exact_mod_cast (by omega : 1 ≤ s)
        have hca : (c:ℝ) = a := by exact_mod_cast (by omega : c = a)
        rw [hca]; nlinarith
      · rw [if_neg hε] at hkey
        have hca : (c:ℝ) + 1 = a := by exact_mod_cast hkey
        nlinarith
    · rw [if_neg hr0] at hkey
      by_cases hε : r < s
      · rw [if_pos hε] at hkey
        have hs1 : (1:ℝ) ≤ s := by exact_mod_cast (by omega : 1 ≤ s)
        have hca : (c:ℝ) = a + 1 := by exact_mod_cast hkey
        rw [hca]; nlinarith
      · rw [if_neg hε] at hkey
        have hca : (c:ℝ) = a := by exact_mod_cast (by omega : c = a)
        rw [hca]; nlinarith
  rw [abs_le]
  constructor <;> linarith

/-! ## The multiplicity sum and remainder of the pair sieve -/

@[simp] lemma pairSieve_support (M h : ℕ) (z : ℝ) (hz : 1 ≤ z) :
    (pairSieve M h z hz).support = (Finset.Icc 1 M).image (fun n => n * (n + h)) := rfl

@[simp] lemma pairSieve_weights (M h : ℕ) (z : ℝ) (hz : 1 ≤ z) :
    (pairSieve M h z hz).weights = fun _ => 1 := rfl

lemma mul_shift_injOn (h M : ℕ) :
    Set.InjOn (fun n => n * (n + h)) ((Finset.Icc 1 M : Finset ℕ) : Set ℕ) := by
  intro a ha b hb heq
  simp only [Finset.coe_Icc, Set.mem_Icc] at ha hb
  dsimp only at heq
  rcases Nat.lt_trichotomy a b with hab | hab | hab
  · exact absurd heq
      (Nat.ne_of_lt (mul_lt_mul'' hab (by omega) (Nat.zero_le _) (Nat.zero_le _)))
  · exact hab
  · exact absurd heq.symm
      (Nat.ne_of_lt (mul_lt_mul'' hab (by omega) (Nat.zero_le _) (Nat.zero_le _)))

lemma pairSieve_multSum (M h : ℕ) (z : ℝ) (hz : 1 ≤ z) (d : ℕ) :
    BoundingSieve.multSum (s := (pairSieve M h z hz).toBoundingSieve) d
      = (((Finset.Icc 1 M).filter (fun n => d ∣ n * (n + h))).card : ℝ) := by
  unfold BoundingSieve.multSum
  simp only [pairSieve_support, pairSieve_weights]
  rw [Finset.sum_image (mul_shift_injOn h M)]
  simp only [Finset.sum_boole]

/-- The key remainder estimate: for squarefree `d` and even `h`,
`|multSum d − ν(d)·M| ≤ 2^ω(d)`. -/
lemma pairSieve_abs_rem_le (M h : ℕ) (z : ℝ) (hz : 1 ≤ z) (heven : 2 ∣ h)
    {d : ℕ} (hd : Squarefree d) :
    |BoundingSieve.rem (s := (pairSieve M h z hz).toBoundingSieve) d|
      ≤ 2 ^ d.primeFactors.card := by
  have hd0 : 0 < d := Nat.pos_of_ne_zero hd.ne_zero
  have hmaps : Set.MapsTo (fun n => n % d)
      (((Finset.Icc 1 M).filter (fun n => d ∣ n * (n + h)) : Finset ℕ) : Set ℕ)
      (((Finset.range d).filter (fun r => d ∣ r * (r + h)) : Finset ℕ) : Set ℕ) := by
    intro n hn
    rw [Finset.mem_coe, Finset.mem_filter] at hn
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_range]
    exact ⟨Nat.mod_lt n hd0, (dvd_shift_iff_mod d h n).mp hn.2⟩
  have hdecomp := Finset.card_eq_sum_card_fiberwise hmaps
  have hfib : ∀ r ∈ (Finset.range d).filter (fun r => d ∣ r * (r + h)),
      (((Finset.Icc 1 M).filter (fun n => d ∣ n * (n + h))).filter
          (fun n => n % d = r))
        = (Finset.Icc 1 M).filter (fun n => n % d = r) := by
    intro r hr
    rw [Finset.mem_filter, Finset.mem_range] at hr
    rw [Finset.filter_filter]
    apply Finset.filter_congr
    intro n _
    constructor
    · exact fun hx => hx.2
    · intro hx
      exact ⟨(dvd_shift_iff_mod d h n).mpr (by rw [hx]; exact hr.2), hx⟩
  have hdecomp' : (((Finset.Icc 1 M).filter (fun n => d ∣ n * (n + h))).card : ℝ)
      = ∑ r ∈ (Finset.range d).filter (fun r => d ∣ r * (r + h)),
          (((Finset.Icc 1 M).filter (fun n => n % d = r)).card : ℝ) := by
    rw [hdecomp, Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro r hr
    rw [hfib r hr]
  have hnu : pairNu h d * (M : ℝ)
      = ∑ _r ∈ (Finset.range d).filter (fun r => d ∣ r * (r + h)), (M : ℝ) / d := by
    rw [Finset.sum_const, nsmul_eq_mul, pairNu_apply, rhoFun_eq_nroots heven hd]
    have hcard : (((Finset.range d).filter (fun r => d ∣ r * (r + h))).card : ℝ)
        = (nroots h d : ℝ) := rfl
    rw [hcard]
    ring
  unfold BoundingSieve.rem
  rw [pairSieve_multSum, pairSieve_nu, pairSieve_totalMass]
  calc |(((Finset.Icc 1 M).filter (fun n => d ∣ n * (n + h))).card : ℝ)
        - pairNu h d * (M : ℝ)|
      = |∑ r ∈ (Finset.range d).filter (fun r => d ∣ r * (r + h)),
          ((((Finset.Icc 1 M).filter (fun n => n % d = r)).card : ℝ) - (M : ℝ) / d)| := by
        rw [hdecomp', hnu, Finset.sum_sub_distrib]
    _ ≤ ∑ r ∈ (Finset.range d).filter (fun r => d ∣ r * (r + h)),
          |(((Finset.Icc 1 M).filter (fun n => n % d = r)).card : ℝ) - (M : ℝ) / d| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _r ∈ (Finset.range d).filter (fun r => d ∣ r * (r + h)), (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro r hr
        rw [Finset.mem_filter, Finset.mem_range] at hr
        exact card_Icc_filter_mod M hd0 hr.1
    _ = (nroots h d : ℝ) := by
        rw [Finset.sum_const, nsmul_eq_mul, mul_one]
        rfl
    _ = rhoFun h d := (rhoFun_eq_nroots heven hd).symm
    _ ≤ 2 ^ d.primeFactors.card := rhoFun_le_two_pow h hd.ne_zero

/-! ## The error sum bound -/

lemma omega_eq_card_primeFactors (d : ℕ) :
    ArithmeticFunction.cardDistinctFactors d = d.primeFactors.card := by
  rw [ArithmeticFunction.cardDistinctFactors_apply, ← List.card_toFinset]
  rfl

/-! ## Prime pairs land in the sifted set -/

open scoped Classical in
lemma pairs_card_le_siftedSum_add (M h : ℕ) (z : ℝ) (hz : 1 ≤ z) (hh : 0 < h)
    (hM : 1 ≤ M) :
    (((Finset.Icc 1 M).filter (fun n => Nat.Prime n ∧ Nat.Prime (n + h))).card : ℝ)
      ≤ BoundingSieve.siftedSum (s := (pairSieve M h z hz).toBoundingSieve) + (z + 1) := by
  have hsift := Sieve.siftedSum_eq (pairSieve M h z hz) (fun _ _ => rfl) z hz rfl
  set A := (Finset.Icc 1 M).filter (fun n => Nat.Prime n ∧ Nat.Prime (n + h)) with hA
  have hsplit : A.card = (A.filter (fun n : ℕ => (n:ℝ) ≤ z)).card
      + (A.filter (fun n : ℕ => ¬ ((n:ℝ) ≤ z))).card :=
    (Finset.card_filter_add_card_filter_not (fun n : ℕ => (n:ℝ) ≤ z)).symm
  have h1 : (A.filter (fun n : ℕ => (n:ℝ) ≤ z)).card ≤ ⌊z⌋₊ := by
    have hsub : A.filter (fun n : ℕ => (n:ℝ) ≤ z) ⊆ Finset.Icc 1 ⌊z⌋₊ := by
      intro n hn
      rw [Finset.mem_filter, hA, Finset.mem_filter, Finset.mem_Icc] at hn
      rw [Finset.mem_Icc]
      exact ⟨hn.1.1.1, Nat.le_floor hn.2⟩
    calc (A.filter (fun n : ℕ => (n:ℝ) ≤ z)).card ≤ (Finset.Icc 1 ⌊z⌋₊).card :=
          Finset.card_le_card hsub
      _ = ⌊z⌋₊ := by rw [Nat.card_Icc]; omega
  have h2 : (A.filter (fun n : ℕ => ¬ ((n:ℝ) ≤ z))).card
      ≤ (((pairSieve M h z hz).support).filter
          (fun d => ∀ p : ℕ, p.Prime → (p:ℝ) ≤ z → ¬ p ∣ d)).card := by
    apply Finset.card_le_card_of_injOn (fun n => n * (n + h))
    · intro n hn
      have hn' : n ∈ A.filter (fun n : ℕ => ¬ ((n:ℝ) ≤ z)) := hn
      rw [Finset.mem_filter, hA, Finset.mem_filter, Finset.mem_Icc] at hn'
      obtain ⟨⟨⟨hn1, hnM⟩, hp, hq⟩, hzn⟩ := hn'
      have hgoal : n * (n + h) ∈ ((pairSieve M h z hz).support).filter
          (fun d => ∀ p : ℕ, p.Prime → (p:ℝ) ≤ z → ¬ p ∣ d) := by
        rw [Finset.mem_filter]
        constructor
        · rw [pairSieve_support]
          exact Finset.mem_image_of_mem _ (Finset.mem_Icc.mpr ⟨hn1, hnM⟩)
        · intro p hpp hpz hpdvd
          rcases (Nat.Prime.dvd_mul hpp).mp hpdvd with hd | hd
          · rcases (Nat.prime_dvd_prime_iff_eq hpp hp).mp hd with rfl
            exact hzn hpz
          · have hpn : p = n + h := (Nat.prime_dvd_prime_iff_eq hpp hq).mp hd
            apply hzn
            have hle : ((n + h : ℕ) : ℝ) ≤ z := by rw [← hpn]; exact hpz
            push_cast at hle
            have hh0 : (0:ℝ) ≤ h := by positivity
            linarith
      exact hgoal
    · apply (mul_shift_injOn h M).mono
      intro n hn
      have hn' : n ∈ A.filter (fun n : ℕ => ¬ ((n:ℝ) ≤ z)) := hn
      have hnA : n ∈ A := Finset.mem_of_mem_filter _ hn'
      rw [hA] at hnA
      exact Finset.mem_coe.mpr (Finset.mem_of_mem_filter _ hnA)
  rw [hsift]
  have hfloor : ((⌊z⌋₊ : ℕ) : ℝ) ≤ z := Nat.floor_le (by linarith)
  have h1R : ((A.filter (fun n : ℕ => (n:ℝ) ≤ z)).card : ℝ) ≤ z :=
    le_trans (by exact_mod_cast h1) hfloor
  have h2R : ((A.filter (fun n : ℕ => ¬ ((n:ℝ) ≤ z))).card : ℝ)
      ≤ ((((pairSieve M h z hz).support).filter
          (fun d => ∀ p : ℕ, p.Prime → (p:ℝ) ≤ z → ¬ p ∣ d)).card : ℝ) := by
    exact_mod_cast h2
  have hAR : (A.card : ℝ) = ((A.filter (fun n : ℕ => (n:ℝ) ≤ z)).card : ℝ)
      + ((A.filter (fun n : ℕ => ¬ ((n:ℝ) ≤ z))).card : ℝ) := by
    exact_mod_cast hsplit
  rw [hAR]
  linarith

/-! ## The main sieve bound for prime pairs -/

theorem pairSieve_pairs_le (M h : ℕ) (z : ℝ) (hz : 1 ≤ z) (heven : 2 ∣ h) (hh : 0 < h)
    (hM : 1 ≤ M) :
    (((Finset.Icc 1 M).filter (fun n => Nat.Prime n ∧ Nat.Prime (n+h))).card : ℝ)
      ≤ (M : ℝ) / (pairSieve M h z hz).selbergBoundingSum
        + ∑ d ∈ Finset.Icc 1 ⌊z⌋₊, (6:ℝ)^(d.primeFactors.card) + (z + 1) := by
  have hpairs := pairs_card_le_siftedSum_add M h z hz hh hM
  refine hpairs.trans ?_
  have hb := SelbergSieve.selberg_bound_simple (pairSieve M h z hz)
  simp only [pairSieve_totalMass, pairSieve_prodPrimes] at hb
  refine ((add_le_add_iff_right (z + 1)).mpr hb).trans ?_
  refine (add_le_add_iff_right (z + 1)).mpr ?_
  refine (add_le_add_iff_left _).mpr ?_
  -- error sum ≤ ∑_{d ≤ ⌊z⌋} 6^ω(d)
  refine le_trans (Finset.sum_le_sum
    (g := fun d : ℕ =>
      if (d : ℝ) ≤ (pairSieve M h z hz).level
      then (6 : ℝ) ^ d.primeFactors.card else 0) ?_) ?_
  · intro d hd
    have hsq : Squarefree d :=
      (Sieve.primorial_squarefree _).squarefree_of_dvd (Nat.dvd_of_mem_divisors hd)
    split_ifs with hdz
    · calc (3:ℝ) ^ (ω d)
            * |BoundingSieve.rem (s := (pairSieve M h z hz).toBoundingSieve) d|
          ≤ (3:ℝ) ^ (ω d) * 2 ^ d.primeFactors.card := by
            apply mul_le_mul_of_nonneg_left (pairSieve_abs_rem_le M h z hz heven hsq)
            positivity
        _ = (6:ℝ) ^ d.primeFactors.card := by
            rw [omega_eq_card_primeFactors, ← mul_pow]
            norm_num
    · exact le_rfl
  · rw [← Finset.sum_filter]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro d hd
      rw [Finset.mem_filter] at hd
      rw [Finset.mem_Icc]
      have hdz : (d : ℝ) ≤ z := by
        simpa only [pairSieve_level] using hd.2
      exact ⟨Nat.pos_of_mem_divisors hd.1, Nat.le_floor hdz⟩
    · intro d _ _
      positivity

/-! ## Lower bound for the Selberg bounding sum -/

theorem pairSieve_boundingSum_ge (M h : ℕ) (z : ℝ) (hz : 1 ≤ z) (heven : 2 ∣ h)
    (hh : 0 < h) :
    ∑ ℓ ∈ (Finset.Icc 1 ⌊Real.sqrt z⌋₊).filter
        (fun ℓ => Squarefree ℓ ∧ ℓ.Coprime (2*h)),
        (2:ℝ)^(ℓ.primeFactors.card) / ℓ
      ≤ (pairSieve M h z hz).selbergBoundingSum := by
  have hz0 : (0:ℝ) ≤ z := by linarith
  -- every ℓ in the index set is a divisor of the primorial with ℓ² ≤ z
  have hmem : ∀ ℓ ∈ (Finset.Icc 1 ⌊Real.sqrt z⌋₊).filter
      (fun ℓ => Squarefree ℓ ∧ ℓ.Coprime (2*h)),
      ℓ ∈ (primorial ⌊z⌋₊).divisors.filter (fun l : ℕ => (l:ℝ)^2 ≤ z) := by
    intro ℓ hℓ
    rw [Finset.mem_filter, Finset.mem_Icc] at hℓ
    obtain ⟨⟨hℓ1, hℓsqrt⟩, hℓsq, hℓcop⟩ := hℓ
    have hℓR : (ℓ:ℝ) ≤ Real.sqrt z :=
      le_trans (Nat.cast_le.mpr hℓsqrt) (Nat.floor_le (Real.sqrt_nonneg z))
    have hsq : ((ℓ:ℝ))^2 ≤ z := by
      calc ((ℓ:ℝ))^2 ≤ (Real.sqrt z)^2 := by gcongr
        _ = z := Real.sq_sqrt hz0
    have hdvd : ℓ ∣ primorial ⌊z⌋₊ := by
      rw [← Nat.prod_primeFactors_of_squarefree hℓsq]
      apply Sieve.prod_primes_dvd_of_dvd
      · intro p hp
        rw [Sieve.prime_dvd_primorial_iff _ _ (Nat.prime_of_mem_primeFactors hp)]
        have hpl : p ≤ ℓ := Nat.le_of_dvd (by omega) (Nat.dvd_of_mem_primeFactors hp)
        have hsz : Real.sqrt z ≤ z := Sieve.sqrt_le_self z hz
        exact le_trans hpl (le_trans hℓsqrt (Nat.floor_mono hsz))
      · intro p hp
        exact Nat.prime_of_mem_primeFactors hp
    rw [Finset.mem_filter, Nat.mem_divisors]
    exact ⟨⟨hdvd, (Sieve.primorial_squarefree _).ne_zero⟩, hsq⟩
  -- termwise: 2^ω(ℓ)/ℓ = ν(ℓ) ≤ g(ℓ)
  have hterm : ∀ ℓ ∈ (Finset.Icc 1 ⌊Real.sqrt z⌋₊).filter
      (fun ℓ => Squarefree ℓ ∧ ℓ.Coprime (2*h)),
      (2:ℝ)^(ℓ.primeFactors.card) / ℓ
        ≤ SelbergSieve.selbergTerms (pairSieve M h z hz).toBoundingSieve ℓ := by
    intro ℓ hℓ
    have hℓdvd : ℓ ∣ primorial ⌊z⌋₊ := by
      have hm := hmem ℓ hℓ
      rw [Finset.mem_filter, Nat.mem_divisors] at hm
      exact hm.1.1
    rw [Finset.mem_filter, Finset.mem_Icc] at hℓ
    obtain ⟨⟨hℓ1, _⟩, hℓsq, hℓcop⟩ := hℓ
    have hnu_eq : pairNu h ℓ = (2:ℝ)^(ℓ.primeFactors.card) / ℓ := by
      rw [pairNu_apply, rhoFun, ArithmeticFunction.prodPrimeFactors_apply hℓsq.ne_zero]
      congr 1
      calc (∏ p ∈ ℓ.primeFactors, if p ∣ 2*h then (1:ℝ) else 2)
          = ∏ _p ∈ ℓ.primeFactors, (2:ℝ) := by
            apply Finset.prod_congr rfl
            intro p hp
            rw [if_neg]
            intro hpdvd
            have hpp := Nat.prime_of_mem_primeFactors hp
            have hone : p ∣ 1 :=
              hℓcop ▸ Nat.dvd_gcd (Nat.dvd_of_mem_primeFactors hp) hpdvd
            exact hpp.ne_one (Nat.dvd_one.mp hone)
        _ = (2:ℝ) ^ ℓ.primeFactors.card := by rw [Finset.prod_const]
    rw [SelbergSieve.selbergTerms_apply, pairSieve_nu, ← hnu_eq]
    have hν : 0 ≤ pairNu h ℓ := by rw [hnu_eq]; positivity
    have hfac : ∀ p ∈ ℓ.primeFactors, (1:ℝ) ≤ 1 / (1 - pairNu h p) := by
      intro p hp
      have hpp := Nat.prime_of_mem_primeFactors hp
      have hpP : p ∣ primorial ⌊z⌋₊ := (Nat.dvd_of_mem_primeFactors hp).trans hℓdvd
      have h1 : 0 < pairNu h p := by
        have hpos := BoundingSieve.nu_pos_of_dvd_prodPrimes
          (s := (pairSieve M h z hz).toBoundingSieve) (d := p) hpP
        simpa [pairSieve_nu] using hpos
      have h2 : pairNu h p < 1 := by
        have hlt := (pairSieve M h z hz).nu_lt_one_of_prime p hpp hpP
        simpa [pairSieve_nu] using hlt
      have hpos : 0 < 1 - pairNu h p := by linarith
      rw [le_div_iff₀ hpos, one_mul]
      linarith
    have hprod : (1:ℝ) ≤ ∏ p ∈ ℓ.primeFactors, 1 / (1 - pairNu h p) := by
      have hle : ∏ _p ∈ ℓ.primeFactors, (1:ℝ)
          ≤ ∏ p ∈ ℓ.primeFactors, 1 / (1 - pairNu h p) := by
        apply Finset.prod_le_prod
        · intro p _
          norm_num
        · intro p hp
          exact hfac p hp
      simpa using hle
    linarith [mul_le_mul_of_nonneg_left hprod hν]
  calc ∑ ℓ ∈ (Finset.Icc 1 ⌊Real.sqrt z⌋₊).filter
        (fun ℓ => Squarefree ℓ ∧ ℓ.Coprime (2*h)),
        (2:ℝ)^(ℓ.primeFactors.card) / ℓ
      ≤ ∑ ℓ ∈ (Finset.Icc 1 ⌊Real.sqrt z⌋₊).filter
          (fun ℓ => Squarefree ℓ ∧ ℓ.Coprime (2*h)),
          SelbergSieve.selbergTerms (pairSieve M h z hz).toBoundingSieve ℓ :=
        Finset.sum_le_sum hterm
    _ ≤ ∑ l ∈ (primorial ⌊z⌋₊).divisors.filter (fun l : ℕ => (l:ℝ)^2 ≤ z),
          SelbergSieve.selbergTerms (pairSieve M h z hz).toBoundingSieve l := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (fun ℓ hℓ => hmem ℓ hℓ)
        intro l hl _
        apply le_of_lt
        apply SelbergSieve.selbergTerms_pos
        rw [Finset.mem_filter, Nat.mem_divisors] at hl
        exact hl.1.1
    _ = (pairSieve M h z hz).selbergBoundingSum := by
        rw [Finset.sum_filter]
        simp only [SelbergSieve.selbergBoundingSum, pairSieve_prodPrimes, pairSieve_level]
        apply Finset.sum_congr rfl
        intro l _
        by_cases hlz : (l : ℝ) ^ 2 ≤ z <;> simp [hlz]

end Erdos884
end

/-! Flattened from Erdos884/Bridge884.lean. -/
section

/-!
# Erdős Problem 884 — bridge to the official formal-conjectures statement

The two `abbrev`s below are VERBATIM the definitions from
google-deepmind/formal-conjectures `ErdosProblems/884.lean`.  We identify them (for `n ≠ 0`)
with `pairSum n.divisors` and `gapSum n.divisors` from the shared interface, using that
`Nat.nth (· ∣ n)` is the increasing enumeration of `n.divisors`.
-/

namespace Erdos884

noncomputable abbrev sumDivisorInvPairwiseDifference (n : ℕ) : ℝ :=
    ∑ j : Fin n.divisors.card, ∑ i : Fin j,
    (1 : ℚ) / (Nat.nth (· ∣ n) j - Nat.nth (· ∣ n) i)

noncomputable abbrev sumDivisorInvConsecutiveDifference (n : ℕ) : ℝ :=
    ∑ i : Fin (n.divisors.card - 1),
    (1 : ℚ) / (Nat.nth (· ∣ n) (i + 1) - Nat.nth (· ∣ n) i)

/-! ### `Nat.nth (· ∣ n)` enumerates `n.divisors` -/

private lemma finite_dvd {n : ℕ} (hn : n ≠ 0) : (Set.ofPred (· ∣ n)).Finite :=
  (Set.finite_Iic n).subset fun _ hd => Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hd

private lemma toFinset_dvd {n : ℕ} (hn : n ≠ 0)
    (hf : (Set.ofPred (· ∣ n)).Finite) :
    hf.toFinset = n.divisors := by
  ext d
  simp [Set.Finite.mem_toFinset, Set.mem_ofPred_eq, Nat.mem_divisors, hn]

private lemma lt_card_dvd {n : ℕ} (hn : n ≠ 0) {i : ℕ} (hi : i < n.divisors.card) :
    ∀ hf : (Set.ofPred (· ∣ n)).Finite, i < hf.toFinset.card := fun hf => by
  rw [toFinset_dvd hn hf]
  exact hi

private lemma nth_dvd_mem {n : ℕ} (hn : n ≠ 0) {i : ℕ} (hi : i < n.divisors.card) :
    Nat.nth (· ∣ n) i ∈ n.divisors :=
  Nat.mem_divisors.2 ⟨Nat.nth_mem (p := fun x => x ∣ n) i (lt_card_dvd hn hi), hn⟩

private lemma nth_dvd_lt {n : ℕ} (hn : n ≠ 0) {i j : ℕ} (hij : i < j)
    (hj : j < n.divisors.card) :
    Nat.nth (· ∣ n) i < Nat.nth (· ∣ n) j :=
  Nat.nth_lt_nth_of_lt_card (finite_dvd hn) hij
    (lt_card_dvd hn hj (finite_dvd hn))

private lemma count_dvd_lt_card {n : ℕ} (hn : n ≠ 0) {d : ℕ} (hd : d ∈ n.divisors) :
    Nat.count (· ∣ n) d < n.divisors.card := by
  have h := Nat.count_lt_card (finite_dvd hn) (Nat.mem_divisors.1 hd).1
  rwa [toFinset_dvd hn (finite_dvd hn)] at h

private lemma nth_count_dvd {n d : ℕ} (hd : d ∈ n.divisors) :
    Nat.nth (· ∣ n) (Nat.count (· ∣ n) d) = d :=
  Nat.nth_count (Nat.mem_divisors.1 hd).1

private lemma count_nth_dvd {n : ℕ} (hn : n ≠ 0) {i : ℕ} (hi : i < n.divisors.card) :
    Nat.count (· ∣ n) (Nat.nth (· ∣ n) i) = i :=
  Nat.count_nth (p := fun x => x ∣ n) (lt_card_dvd hn hi)

private lemma count_dvd_lt_count {n : ℕ} (hn : n ≠ 0) {a b : ℕ} (ha : a ∈ n.divisors)
    (hb : b ∈ n.divisors) (hab : a < b) :
    Nat.count (· ∣ n) a < Nat.count (· ∣ n) b := by
  by_contra h
  push_neg at h
  have h1 : Nat.nth (· ∣ n) (Nat.count (· ∣ n) b) ≤ Nat.nth (· ∣ n) (Nat.count (· ∣ n) a) := by
    rcases eq_or_lt_of_le h with heq | hlt
    · rw [heq]
    · exact (nth_dvd_lt hn hlt (count_dvd_lt_card hn ha)).le
  rw [nth_count_dvd hb, nth_count_dvd ha] at h1
  omega

/-! ### The pairwise bridge -/

theorem sumDivisorInvPairwiseDifference_eq {n : ℕ} (hn : n ≠ 0) :
    sumDivisorInvPairwiseDifference n = pairSum n.divisors := by
  classical
  have h1 : sumDivisorInvPairwiseDifference n =
      ∑ j ∈ Finset.range n.divisors.card, ∑ i ∈ Finset.range j,
        invGap (Nat.nth (· ∣ n) i) (Nat.nth (· ∣ n) j) := by
    simp only [sumDivisorInvPairwiseDifference, Rat.cast_one, one_div]
    exact Eq.trans
      (Finset.sum_congr rfl fun j _ => Fin.sum_univ_eq_sum_range
        (fun i => invGap (Nat.nth (· ∣ n) i) (Nat.nth (· ∣ n) (j : ℕ))) (j : ℕ))
      (Fin.sum_univ_eq_sum_range
        (fun j => ∑ i ∈ Finset.range j, invGap (Nat.nth (· ∣ n) i) (Nat.nth (· ∣ n) j))
        n.divisors.card)
  rw [h1, Finset.sum_sigma']
  unfold pairSum pairSumOn
  refine Finset.sum_nbij'
      (fun x : (_ : ℕ) × ℕ => (Nat.nth (· ∣ n) x.2, Nat.nth (· ∣ n) x.1))
      (fun p : ℕ × ℕ => ⟨Nat.count (· ∣ n) p.2, Nat.count (· ∣ n) p.1⟩)
      ?_ ?_ ?_ ?_ (fun x _ => rfl)
  · rintro ⟨j, i⟩ hx
    simp only [Finset.mem_sigma, Finset.mem_range] at hx
    simp only [Finset.mem_filter, Finset.mem_product, and_true]
    exact ⟨⟨nth_dvd_mem hn (hx.2.trans hx.1), nth_dvd_mem hn hx.1⟩,
      nth_dvd_lt hn hx.2 hx.1⟩
  · rintro ⟨a, b⟩ hp
    simp only [Finset.mem_filter, Finset.mem_product, and_true] at hp
    obtain ⟨⟨ha, hb⟩, hab⟩ := hp
    simp only [Finset.mem_sigma, Finset.mem_range]
    exact ⟨count_dvd_lt_card hn hb, count_dvd_lt_count hn ha hb hab⟩
  · rintro ⟨j, i⟩ hx
    simp only [Finset.mem_sigma, Finset.mem_range] at hx
    simp only [count_nth_dvd hn hx.1, count_nth_dvd hn (hx.2.trans hx.1)]
  · rintro ⟨a, b⟩ hp
    simp only [Finset.mem_filter, Finset.mem_product, and_true] at hp
    obtain ⟨⟨ha, hb⟩, hab⟩ := hp
    simp only [nth_count_dvd ha, nth_count_dvd hb]

/-! ### The consecutive bridge -/

theorem sumDivisorInvConsecutiveDifference_eq {n : ℕ} (hn : n ≠ 0) :
    sumDivisorInvConsecutiveDifference n = gapSum n.divisors := by
  classical
  have h1 : sumDivisorInvConsecutiveDifference n =
      ∑ i ∈ Finset.range (n.divisors.card - 1),
        invGap (Nat.nth (· ∣ n) i) (Nat.nth (· ∣ n) (i + 1)) := by
    simp only [sumDivisorInvConsecutiveDifference, Rat.cast_one, one_div]
    exact Fin.sum_univ_eq_sum_range
      (fun i => invGap (Nat.nth (· ∣ n) i) (Nat.nth (· ∣ n) (i + 1))) _
  rw [h1]
  unfold gapSum pairSumOn
  refine Finset.sum_nbij'
      (fun i : ℕ => (Nat.nth (· ∣ n) i, Nat.nth (· ∣ n) (i + 1)))
      (fun p : ℕ × ℕ => Nat.count (· ∣ n) p.1)
      ?_ ?_ ?_ ?_ (fun x _ => rfl)
  · intro i hi
    rw [Finset.mem_range] at hi
    have hi1 : i + 1 < n.divisors.card := by omega
    have hi0 : i < n.divisors.card := by omega
    have hcons : IsConsecutive n.divisors (Nat.nth (· ∣ n) i) (Nat.nth (· ∣ n) (i + 1)) := by
      refine ⟨nth_dvd_mem hn hi0, nth_dvd_mem hn hi1, nth_dvd_lt hn (by omega) hi1, ?_⟩
      rintro c hc ⟨h1c, h2c⟩
      have e1 : i < Nat.count (· ∣ n) c := by
        have h := count_dvd_lt_count hn (nth_dvd_mem hn hi0) hc h1c
        rwa [count_nth_dvd hn hi0] at h
      have e2 : Nat.count (· ∣ n) c < i + 1 := by
        have h := count_dvd_lt_count hn hc (nth_dvd_mem hn hi1) h2c
        rwa [count_nth_dvd hn hi1] at h
      omega
    simp only [Finset.mem_filter, Finset.mem_product]
    exact ⟨⟨nth_dvd_mem hn hi0, nth_dvd_mem hn hi1⟩, nth_dvd_lt hn (by omega) hi1, hcons⟩
  · rintro ⟨a, b⟩ hp
    simp only [Finset.mem_filter, Finset.mem_product] at hp
    obtain ⟨⟨ha, hb⟩, hab, -⟩ := hp
    simp only [Finset.mem_range]
    have h1 := count_dvd_lt_count hn ha hb hab
    have h2 := count_dvd_lt_card hn hb
    omega
  · intro i hi
    rw [Finset.mem_range] at hi
    simp only [count_nth_dvd hn (show i < n.divisors.card by omega)]
  · rintro ⟨a, b⟩ hp
    simp only [Finset.mem_filter, Finset.mem_product] at hp
    obtain ⟨⟨ha, hb⟩, hab, hcons⟩ := hp
    have hca : Nat.count (· ∣ n) a < Nat.count (· ∣ n) b := count_dvd_lt_count hn ha hb hab
    have hcb : Nat.count (· ∣ n) b < n.divisors.card := count_dvd_lt_card hn hb
    have hkey : Nat.count (· ∣ n) a + 1 = Nat.count (· ∣ n) b := by
      by_contra hne
      have hlt : Nat.count (· ∣ n) a + 1 < Nat.count (· ∣ n) b := by omega
      have hmem' : Nat.nth (· ∣ n) (Nat.count (· ∣ n) a + 1) ∈ n.divisors :=
        nth_dvd_mem hn (by omega)
      have hgt : a < Nat.nth (· ∣ n) (Nat.count (· ∣ n) a + 1) := by
        conv_lhs => rw [← nth_count_dvd ha]
        exact nth_dvd_lt hn (by omega) (by omega)
      have hlt2 : Nat.nth (· ∣ n) (Nat.count (· ∣ n) a + 1) < b := by
        conv_rhs => rw [← nth_count_dvd hb]
        exact nth_dvd_lt hn hlt hcb
      exact hcons.2.2.2 _ hmem' ⟨hgt, hlt2⟩
    simp only [nth_count_dvd ha, hkey, nth_count_dvd hb]

/-! ### Nonnegativity corollaries -/

theorem sumDivisorInvPairwise_nonneg (n : ℕ) (hn : n ≠ 0) :
    0 ≤ sumDivisorInvPairwiseDifference n := by
  rw [sumDivisorInvPairwiseDifference_eq hn]
  exact pairSum_nonneg _

theorem sumDivisorInvConsecutive_nonneg (n : ℕ) (hn : n ≠ 0) :
    0 ≤ sumDivisorInvConsecutiveDifference n := by
  rw [sumDivisorInvConsecutiveDifference_eq hn]
  exact gapSum_nonneg _

end Erdos884
end

/-! Flattened from Erdos884/PairCount884.lean. -/
section

/-!
# Erdős 884 — Lemma B: counting prime pairs with small gap

Exports `Erdos884.prime_pairs_bound`: the number of prime pairs `(p, q)` with
`p < q ≤ 9t` and `q - p ≤ N ≤ (log t)²` is at most `C_B · N · t / (log t)²`.

Route: fiber the pairs over the gap `h = q - p`.  Odd gaps contribute at most `1`
each (`p = 2` forced).  Even gaps are handled by the Selberg pair sieve
(`pairSieve_pairs_le`), whose bounding sum is bounded below via
`pairSieve_boundingSum_ge` + `coprime_squarefree_sum_lower`; the sum of the
resulting `(2h/φ(2h))²` weights is controlled by `sum_totient_ratio_sq_le`.
-/

namespace Erdos884

/-! ## Fibering the pair count over the gap `h` -/

lemma pc_pair_fiber (M N : ℕ) :
    ((Finset.Icc 1 M ×ˢ Finset.Icc 1 M).filter
        (fun pq => Nat.Prime pq.1 ∧ Nat.Prime pq.2 ∧ pq.1 < pq.2 ∧ pq.2 - pq.1 ≤ N)).card
      ≤ ∑ h ∈ Finset.Icc 1 N,
          ((Finset.Icc 1 M).filter (fun n => Nat.Prime n ∧ Nat.Prime (n + h))).card := by
  have hsub : (Finset.Icc 1 M ×ˢ Finset.Icc 1 M).filter
        (fun pq => Nat.Prime pq.1 ∧ Nat.Prime pq.2 ∧ pq.1 < pq.2 ∧ pq.2 - pq.1 ≤ N)
      ⊆ (Finset.Icc 1 N).biUnion (fun h =>
          ((Finset.Icc 1 M).filter (fun n => Nat.Prime n ∧ Nat.Prime (n + h))).image
            (fun p => (p, p + h))) := by
    intro pq hpq
    obtain ⟨a, b⟩ := pq
    rw [Finset.mem_filter, Finset.mem_product] at hpq
    obtain ⟨⟨h1, h2⟩, hp, hq, hlt, hle⟩ := hpq
    rw [Finset.mem_Icc] at h1 h2
    rw [Finset.mem_biUnion]
    refine ⟨b - a, Finset.mem_Icc.mpr ⟨by omega, hle⟩, ?_⟩
    rw [Finset.mem_image]
    have he : a + (b - a) = b := by omega
    refine ⟨a, ?_, ?_⟩
    · rw [Finset.mem_filter, Finset.mem_Icc]
      exact ⟨⟨h1.1, h1.2⟩, hp, by rw [he]; exact hq⟩
    · rw [he]
  calc ((Finset.Icc 1 M ×ˢ Finset.Icc 1 M).filter
        (fun pq => Nat.Prime pq.1 ∧ Nat.Prime pq.2 ∧ pq.1 < pq.2 ∧ pq.2 - pq.1 ≤ N)).card
      ≤ ((Finset.Icc 1 N).biUnion (fun h =>
          ((Finset.Icc 1 M).filter (fun n => Nat.Prime n ∧ Nat.Prime (n + h))).image
            (fun p => (p, p + h)))).card := Finset.card_le_card hsub
    _ ≤ ∑ h ∈ Finset.Icc 1 N, (((Finset.Icc 1 M).filter
          (fun n => Nat.Prime n ∧ Nat.Prime (n + h))).image (fun p => (p, p + h))).card :=
        Finset.card_biUnion_le
    _ ≤ _ := Finset.sum_le_sum (fun h _ => Finset.card_image_le)

/-! ## Odd gaps: at most one pair -/

lemma pc_odd_card (M h : ℕ) (hodd : ¬ 2 ∣ h) :
    ((Finset.Icc 1 M).filter (fun n => Nat.Prime n ∧ Nat.Prime (n + h))).card ≤ 1 := by
  have hmem : ∀ n ∈ (Finset.Icc 1 M).filter (fun n => Nat.Prime n ∧ Nat.Prime (n + h)),
      n = 2 := by
    intro n hn
    rw [Finset.mem_filter] at hn
    obtain ⟨-, hp, hq⟩ := hn
    by_contra hne
    have hn3 : 3 ≤ n := by have := hp.two_le; omega
    have hnodd : n % 2 = 1 := Nat.odd_iff.mp (hp.odd_of_ne_two hne)
    have hdvd : 2 ∣ n + h := by omega
    rcases hq.eq_one_or_self_of_dvd 2 hdvd with h1 | h1 <;> omega
  rw [Finset.card_le_one]
  intro a ha b hb
  rw [hmem a ha, hmem b hb]

/-! ## The error-sum bound -/

lemma pc_err_sum (z : ℝ) (hz : 1 ≤ z) :
    ∑ d ∈ Finset.Icc 1 ⌊z⌋₊, (6:ℝ)^(d.primeFactors.card) ≤ z * (1 + Real.log z)^5 := by
  have h0 := sum_pow_primeFactors_le 6 ⌊z⌋₊ (by norm_num)
  norm_num at h0
  have h1 : (1:ℝ) ≤ ((⌊z⌋₊ : ℕ) : ℝ) := by
    have : (1:ℕ) ≤ ⌊z⌋₊ := Nat.le_floor (by exact_mod_cast hz)
    exact_mod_cast this
  have h2 : ((⌊z⌋₊ : ℕ) : ℝ) ≤ z := Nat.floor_le (by linarith)
  have h3 : Real.log ((⌊z⌋₊ : ℕ) : ℝ) ≤ Real.log z := Real.log_le_log (by linarith) h2
  have h4 : (0:ℝ) ≤ 1 + Real.log ((⌊z⌋₊ : ℕ) : ℝ) := by
    have := Real.log_nonneg h1
    linarith
  refine h0.trans ?_
  exact mul_le_mul h2 (pow_le_pow_left₀ h4 (by linarith) 5) (pow_nonneg h4 5) (by linarith)

/-! ## The totient-ratio sum over even gaps -/

lemma pc_totient_sum (N : ℕ) :
    ∑ h ∈ (Finset.Icc 1 N).filter (fun h => 2 ∣ h),
        (((2*h : ℕ) : ℝ) / (Nat.totient (2*h) : ℝ))^2 ≤ 400 * N := by
  have h1 : ∑ h ∈ (Finset.Icc 1 N).filter (fun h => 2 ∣ h),
        (((2*h : ℕ) : ℝ) / (Nat.totient (2*h) : ℝ))^2
      ≤ ∑ h' ∈ Finset.Icc 1 (2*N), ((h' : ℝ) / (Nat.totient h' : ℝ))^2 := by
    apply cs_sum_le_sum_inj (fun h => 2*h)
    · intro a ha
      rw [Finset.mem_filter, Finset.mem_Icc] at ha
      rw [Finset.mem_Icc]
      omega
    · intro a _ b _ hab
      simp only at hab
      omega
    · intro a _
      exact le_rfl
    · intro b _
      positivity
  have h2 := sum_totient_ratio_sq_le (2*N)
  have h3 : (200:ℝ) * ((2*N : ℕ) : ℝ) = 400 * N := by push_cast; ring
  linarith

/-! ## Junk-term absorption: `4√t(1+log t)⁵ ≤ t/(log t)²` for large `t` -/

lemma pc_sqrt_lower (t : ℝ) (ht : 1 ≤ t) (hL : (2:ℝ)^40 ≤ Real.log t) :
    4 * (1 + Real.log t)^5 * (Real.log t)^2 ≤ Real.sqrt t := by
  set L := Real.log t with hLdef
  have hL1 : (1:ℝ) ≤ L := le_trans (by norm_num) hL
  have hL0 : (0:ℝ) < L := by linarith
  have ht0 : (0:ℝ) < t := by linarith
  have hspos : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht0
  -- `√t = exp (L/2) ≥ (L/16)⁸`
  have hlogs : Real.log (Real.sqrt t) = L / 2 := by
    rw [Real.log_sqrt ht0.le]
  have hs_eq : Real.sqrt t = Real.exp (L / 2) := by
    rw [← hlogs, Real.exp_log hspos]
  have hexp8 : Real.exp (L/16) ^ 8 = Real.exp (L / 2) := by
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  have he3 : L/16 ≤ Real.exp (L/16) := by
    linarith [Real.add_one_le_exp (L/16)]
  have hexp_low : (L/16)^8 ≤ Real.exp (L / 2) := by
    calc (L/16)^8 ≤ Real.exp (L/16) ^ 8 := pow_le_pow_left₀ (by positivity) he3 8
      _ = Real.exp (L / 2) := hexp8
  have hmid : 128 * L^7 ≤ (L/16)^8 := by
    have hpow : (L/16)^8 = L^8 / 16^8 := by
      rw [div_pow]
    rw [hpow, le_div_iff₀ (by positivity : (0:ℝ) < 16^8)]
    have hLbig : (128:ℝ) * 16^8 ≤ L := by
      norm_num at hL ⊢
      linarith
    calc 128 * L^7 * 16^8 = (128 * 16^8) * L^7 := by ring
      _ ≤ L * L^7 := mul_le_mul_of_nonneg_right hLbig (by positivity)
      _ = L^8 := by ring
  calc 4 * (1 + L)^5 * L^2
      ≤ 4 * (2*L)^5 * L^2 := by
        have h5 : (1 + L)^5 ≤ (2*L)^5 := pow_le_pow_left₀ (by linarith) (by linarith) 5
        have := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left h5 (by norm_num : (0:ℝ) ≤ 4))
          (by positivity : (0:ℝ) ≤ L^2)
        linarith
    _ = 128 * L^7 := by ring
    _ ≤ (L/16)^8 := hmid
    _ ≤ Real.exp (L / 2) := hexp_low
    _ = Real.sqrt t := hs_eq.symm

lemma pc_junk_le (t : ℝ) (ht : 1 ≤ t) (hL : (2:ℝ)^40 ≤ Real.log t) :
    4 * Real.sqrt t * (1 + Real.log t)^5 ≤ t / (Real.log t)^2 := by
  set L := Real.log t with hLdef
  have hL0 : (0:ℝ) < L := lt_of_lt_of_le (by norm_num) hL
  have key := pc_sqrt_lower t ht hL
  have hs : Real.sqrt t * Real.sqrt t = t := Real.mul_self_sqrt (by linarith)
  rw [le_div_iff₀ (by positivity : (0:ℝ) < L^2)]
  calc 4 * Real.sqrt t * (1 + L)^5 * L^2
      = Real.sqrt t * (4 * (1 + L)^5 * L^2) := by ring
    _ ≤ Real.sqrt t * Real.sqrt t :=
        mul_le_mul_of_nonneg_left key (Real.sqrt_nonneg t)
    _ = t := hs

/-! ## The main theorem -/

theorem prime_pairs_bound :
    ∃ C_B : ℝ, 1 ≤ C_B ∧ ∃ T_B : ℝ, 3 ≤ T_B ∧ ∀ t : ℝ, T_B ≤ t → ∀ N : ℕ, 2 ≤ N →
      (N:ℝ) ≤ (Real.log t)^2 →
      (((Finset.Icc 1 ⌊9*t⌋₊ ×ˢ Finset.Icc 1 ⌊9*t⌋₊).filter
          (fun pq => Nat.Prime pq.1 ∧ Nat.Prime pq.2 ∧ pq.1 < pq.2 ∧ pq.2 - pq.1 ≤ N)).card : ℝ)
        ≤ C_B * N * t / (Real.log t)^2 := by
  obtain ⟨c₀, hc₀, w₀, hlower⟩ := coprime_squarefree_sum_lower
  have hCB1 : (1:ℝ) ≤ 90000 / c₀ + 1 := by
    have : (0:ℝ) ≤ 90000 / c₀ := by positivity
    linarith
  have hTB3 : (3:ℝ) ≤ max (Real.exp ((2:ℝ)^40)) (((w₀:ℝ)+1)^4) := by
    have h1 : (3:ℝ) ≤ Real.exp ((2:ℝ)^40) := by
      have h2 := Real.add_one_le_exp ((2:ℝ)^40)
      have h3 : (3:ℝ) ≤ (2:ℝ)^40 + 1 := by norm_num
      linarith
    exact le_trans h1 (le_max_left _ _)
  refine ⟨90000 / c₀ + 1, hCB1, max (Real.exp ((2:ℝ)^40)) (((w₀:ℝ)+1)^4), hTB3, ?_⟩
  intro t ht N hN2 hNlog
  -- basic facts about `t`
  have htexp : Real.exp ((2:ℝ)^40) ≤ t := le_trans (le_max_left _ _) ht
  have htw : ((w₀:ℝ)+1)^4 ≤ t := le_trans (le_max_right _ _) ht
  have hL : (2:ℝ)^40 ≤ Real.log t := by
    have h1 := Real.log_le_log (Real.exp_pos _) htexp
    rwa [Real.log_exp] at h1
  set L := Real.log t with hLdef
  have hL0 : (0:ℝ) < L := lt_of_lt_of_le (by norm_num) hL
  have hL250 : (250:ℝ) ≤ L := le_trans (by norm_num) hL
  have ht16 : (16:ℝ) ≤ t := by
    have h1 := Real.add_one_le_exp ((2:ℝ)^40)
    have h2 : (16:ℝ) ≤ (2:ℝ)^40 + 1 := by norm_num
    linarith
  have ht1 : (1:ℝ) ≤ t := by linarith
  have ht0 : (0:ℝ) < t := by linarith
  -- the sieve level `z = √t`
  set z := Real.sqrt t with hzdef
  have hz : (1:ℝ) ≤ z := by
    rw [hzdef]
    refine (Real.le_sqrt (by norm_num) (by linarith)).mpr ?_
    norm_num
    linarith
  have hz4 : (4:ℝ) ≤ z := by
    rw [hzdef]
    refine (Real.le_sqrt (by norm_num) (by linarith)).mpr ?_
    norm_num
    linarith
  have hlogz : Real.log z = L / 2 := by
    rw [hzdef, Real.log_sqrt ht0.le]
  -- the total mass `M = ⌊9t⌋₊`
  set M := ⌊9*t⌋₊ with hMdef
  have hM1 : 1 ≤ M := Nat.le_floor (by push_cast; linarith)
  have hM9t : (M:ℝ) ≤ 9*t := Nat.floor_le (by linarith)
  -- the fourth-root scale `w = ⌊√z⌋₊`
  have hu2 : (2:ℝ) ≤ Real.sqrt z := by
    refine (Real.le_sqrt (by norm_num) (by linarith)).mpr ?_
    norm_num
    linarith
  have hfloorw : Real.sqrt z / 2 ≤ ((⌊Real.sqrt z⌋₊ : ℕ) : ℝ) := by
    have h1 := Nat.lt_floor_add_one (Real.sqrt z)
    linarith
  have hw₀w : w₀ ≤ ⌊Real.sqrt z⌋₊ := by
    apply Nat.le_floor
    have hx4 : (((w₀:ℝ)+1)^2)^2 ≤ t := by
      calc (((w₀:ℝ)+1)^2)^2 = ((w₀:ℝ)+1)^4 := by ring
        _ ≤ t := htw
    have hx2 : ((w₀:ℝ)+1)^2 ≤ z := by
      rw [hzdef]
      exact (Real.le_sqrt (by positivity) (by linarith)).mpr hx4
    have hx1 : (w₀:ℝ)+1 ≤ Real.sqrt z :=
      (Real.le_sqrt (by positivity) (by linarith)).mpr hx2
    linarith
  have hw1R : (1:ℝ) ≤ ((⌊Real.sqrt z⌋₊ : ℕ) : ℝ) := by linarith
  have hlogw : L/5 ≤ Real.log ((⌊Real.sqrt z⌋₊ : ℕ) : ℝ) := by
    have hlogu : Real.log (Real.sqrt z) = L/4 := by
      rw [Real.log_sqrt (by linarith : (0:ℝ) ≤ z), hlogz]
      ring
    have h1 : Real.log (Real.sqrt z / 2) ≤ Real.log ((⌊Real.sqrt z⌋₊ : ℕ) : ℝ) :=
      Real.log_le_log (by linarith) hfloorw
    have h2 : Real.log (Real.sqrt z / 2) = L/4 - Real.log 2 := by
      rw [Real.log_div (ne_of_gt (by linarith : (0:ℝ) < Real.sqrt z)) (by norm_num), hlogu]
    have h3 : Real.log 2 < 1 := by linarith [Real.log_two_lt_d9]
    linarith
  -- the per-`h` bound for even gaps
  have hkey : ∀ h ∈ (Finset.Icc 1 N).filter (fun h => 2 ∣ h),
      (((Finset.Icc 1 M).filter (fun n => Nat.Prime n ∧ Nat.Prime (n + h))).card : ℝ)
        ≤ 225 * t / (c₀ * L^2) * (((2*h : ℕ) : ℝ) / (Nat.totient (2*h) : ℝ))^2
          + (z * (1 + L)^5 + (z + 1)) := by
    intro h hh
    rw [Finset.mem_filter, Finset.mem_Icc] at hh
    obtain ⟨⟨hh1, hhN⟩, heven⟩ := hh
    have hh0 : 0 < h := hh1
    have hbound := pairSieve_pairs_le M h z hz heven hh0 hM1
    have hSpos := pairSieve_boundingSum_pos M h z hz
    have hge := pairSieve_boundingSum_ge M h z hz heven hh0
    -- lower bound on the Selberg bounding sum
    have hm1 : 1 ≤ 2*h := by omega
    have hmw : ((2*h : ℕ) : ℝ) ≤ (Real.log ((⌊Real.sqrt z⌋₊ : ℕ) : ℝ))^3 := by
      have h1 : ((2*h : ℕ) : ℝ) ≤ 2*(N:ℝ) := by
        push_cast
        have : (h:ℝ) ≤ (N:ℝ) := by exact_mod_cast hhN
        linarith
      have h2 : 2*(N:ℝ) ≤ 2*L^2 := by linarith
      have h3 : 2*L^2 ≤ (L/5)^3 := by
        have h4 := mul_le_mul_of_nonneg_right hL250 (sq_nonneg L)
        nlinarith [h4]
      have h5 : (L/5)^3 ≤ (Real.log ((⌊Real.sqrt z⌋₊ : ℕ) : ℝ))^3 :=
        pow_le_pow_left₀ (by linarith) hlogw 3
      linarith
    have hlow := hlower ⌊Real.sqrt z⌋₊ hw₀w (2*h) hm1 hmw
    have hφpos : (0:ℝ) < (Nat.totient (2*h) : ℝ) := by
      exact_mod_cast Nat.totient_pos.mpr (by omega : 0 < 2*h)
    have hmpos : (0:ℝ) < ((2*h : ℕ) : ℝ) := by
      exact_mod_cast (by omega : 0 < 2*h)
    have hlow2 : c₀ * ((Nat.totient (2*h) : ℝ) / ((2*h : ℕ) : ℝ))^2 * (L/5)^2
        ≤ (pairSieve M h z hz).selbergBoundingSum := by
      have hsq : (L/5)^2 ≤ (Real.log ((⌊Real.sqrt z⌋₊ : ℕ) : ℝ))^2 :=
        pow_le_pow_left₀ (by linarith) hlogw 2
      calc c₀ * ((Nat.totient (2*h) : ℝ) / ((2*h : ℕ) : ℝ))^2 * (L/5)^2
          ≤ c₀ * ((Nat.totient (2*h) : ℝ) / ((2*h : ℕ) : ℝ))^2
              * (Real.log ((⌊Real.sqrt z⌋₊ : ℕ) : ℝ))^2 :=
            mul_le_mul_of_nonneg_left hsq (by positivity)
        _ ≤ ∑ ℓ ∈ (Finset.Icc 1 ⌊Real.sqrt z⌋₊).filter
              (fun ℓ => Squarefree ℓ ∧ ℓ.Coprime (2*h)),
              (2:ℝ)^(ℓ.primeFactors.card) / ℓ := hlow
        _ ≤ _ := hge
    -- `M / S ≤ 225·t·(2h/φ(2h))²/(c₀ L²)`
    have hX0 : (0:ℝ) ≤ 225 * t / (c₀ * L^2)
        * (((2*h : ℕ) : ℝ) / (Nat.totient (2*h) : ℝ))^2 := by positivity
    have hXlow : (225 * t / (c₀ * L^2) * (((2*h : ℕ) : ℝ) / (Nat.totient (2*h) : ℝ))^2)
          * (c₀ * ((Nat.totient (2*h) : ℝ) / ((2*h : ℕ) : ℝ))^2 * (L/5)^2) = 9 * t := by
      field_simp
      ring
    have hMX : (M:ℝ) / (pairSieve M h z hz).selbergBoundingSum
        ≤ 225 * t / (c₀ * L^2) * (((2*h : ℕ) : ℝ) / (Nat.totient (2*h) : ℝ))^2 := by
      rw [div_le_iff₀ hSpos]
      calc (M:ℝ) ≤ 9 * t := hM9t
        _ = _ := hXlow.symm
        _ ≤ _ := mul_le_mul_of_nonneg_left hlow2 hX0
    -- the error term
    have herr : ∑ d ∈ Finset.Icc 1 ⌊z⌋₊, (6:ℝ)^(d.primeFactors.card) ≤ z * (1 + L)^5 := by
      have h1 := pc_err_sum z hz
      have h2 : (0:ℝ) ≤ 1 + Real.log z := by
        have := Real.log_nonneg hz
        linarith
      calc ∑ d ∈ Finset.Icc 1 ⌊z⌋₊, (6:ℝ)^(d.primeFactors.card)
          ≤ z * (1 + Real.log z)^5 := h1
        _ ≤ z * (1 + L)^5 := by
            have h3 : (1 + Real.log z)^5 ≤ (1 + L)^5 :=
              pow_le_pow_left₀ h2 (by rw [hlogz]; linarith) 5
            exact mul_le_mul_of_nonneg_left h3 (by linarith)
    calc (((Finset.Icc 1 M).filter (fun n => Nat.Prime n ∧ Nat.Prime (n + h))).card : ℝ)
        ≤ (M:ℝ) / (pairSieve M h z hz).selbergBoundingSum
          + ∑ d ∈ Finset.Icc 1 ⌊z⌋₊, (6:ℝ)^(d.primeFactors.card) + (z + 1) := hbound
      _ ≤ 225 * t / (c₀ * L^2) * (((2*h : ℕ) : ℝ) / (Nat.totient (2*h) : ℝ))^2
          + (z * (1 + L)^5 + (z + 1)) := by linarith
  -- assemble: fiber the pair count over the gap
  have hfiberR : (((Finset.Icc 1 M ×ˢ Finset.Icc 1 M).filter
        (fun pq => Nat.Prime pq.1 ∧ Nat.Prime pq.2 ∧ pq.1 < pq.2 ∧ pq.2 - pq.1 ≤ N)).card : ℝ)
      ≤ ∑ h ∈ Finset.Icc 1 N, (((Finset.Icc 1 M).filter
          (fun n => Nat.Prime n ∧ Nat.Prime (n + h))).card : ℝ) := by
    exact_mod_cast pc_pair_fiber M N
  have hsplit : ∑ h ∈ Finset.Icc 1 N, (((Finset.Icc 1 M).filter
        (fun n => Nat.Prime n ∧ Nat.Prime (n + h))).card : ℝ)
      = ∑ h ∈ (Finset.Icc 1 N).filter (fun h => 2 ∣ h), (((Finset.Icc 1 M).filter
          (fun n => Nat.Prime n ∧ Nat.Prime (n + h))).card : ℝ)
        + ∑ h ∈ (Finset.Icc 1 N).filter (fun h => ¬ 2 ∣ h), (((Finset.Icc 1 M).filter
          (fun n => Nat.Prime n ∧ Nat.Prime (n + h))).card : ℝ) :=
    (Finset.sum_filter_add_sum_filter_not (Finset.Icc 1 N) (fun h => 2 ∣ h) _).symm
  -- even gaps
  have hJ0 : (0:ℝ) ≤ z * (1 + L)^5 + (z + 1) := by
    have := mul_nonneg (show (0:ℝ) ≤ z by linarith)
      (pow_nonneg (show (0:ℝ) ≤ 1 + L by linarith) 5)
    linarith
  have heven_sum : ∑ h ∈ (Finset.Icc 1 N).filter (fun h => 2 ∣ h),
        (((Finset.Icc 1 M).filter (fun n => Nat.Prime n ∧ Nat.Prime (n + h))).card : ℝ)
      ≤ 225 * t / (c₀ * L^2) * (400 * N) + (N:ℝ) * (z * (1 + L)^5 + (z + 1)) := by
    calc ∑ h ∈ (Finset.Icc 1 N).filter (fun h => 2 ∣ h),
          (((Finset.Icc 1 M).filter (fun n => Nat.Prime n ∧ Nat.Prime (n + h))).card : ℝ)
        ≤ ∑ h ∈ (Finset.Icc 1 N).filter (fun h => 2 ∣ h),
            (225 * t / (c₀ * L^2) * (((2*h : ℕ) : ℝ) / (Nat.totient (2*h) : ℝ))^2
              + (z * (1 + L)^5 + (z + 1))) := Finset.sum_le_sum hkey
      _ = 225 * t / (c₀ * L^2) * (∑ h ∈ (Finset.Icc 1 N).filter (fun h => 2 ∣ h),
            (((2*h : ℕ) : ℝ) / (Nat.totient (2*h) : ℝ))^2)
          + (((Finset.Icc 1 N).filter (fun h => 2 ∣ h)).card : ℝ)
            * (z * (1 + L)^5 + (z + 1)) := by
          rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_const, nsmul_eq_mul]
      _ ≤ 225 * t / (c₀ * L^2) * (400 * N) + (N:ℝ) * (z * (1 + L)^5 + (z + 1)) := by
          have hE400 := pc_totient_sum N
          have hEcard : ((Finset.Icc 1 N).filter (fun h => 2 ∣ h)).card ≤ N := by
            calc ((Finset.Icc 1 N).filter (fun h => 2 ∣ h)).card
                ≤ (Finset.Icc 1 N).card := Finset.card_filter_le _ _
              _ = N := by rw [Nat.card_Icc]; omega
          have hEcardR : (((Finset.Icc 1 N).filter (fun h => 2 ∣ h)).card : ℝ) ≤ (N:ℝ) := by
            exact_mod_cast hEcard
          have t1 := mul_le_mul_of_nonneg_left hE400
            (show (0:ℝ) ≤ 225 * t / (c₀ * L^2) by positivity)
          have t2 := mul_le_mul_of_nonneg_right hEcardR hJ0
          linarith
  -- odd gaps
  have hodd_sum : ∑ h ∈ (Finset.Icc 1 N).filter (fun h => ¬ 2 ∣ h),
        (((Finset.Icc 1 M).filter (fun n => Nat.Prime n ∧ Nat.Prime (n + h))).card : ℝ)
      ≤ (N:ℝ) := by
    calc ∑ h ∈ (Finset.Icc 1 N).filter (fun h => ¬ 2 ∣ h),
          (((Finset.Icc 1 M).filter (fun n => Nat.Prime n ∧ Nat.Prime (n + h))).card : ℝ)
        ≤ ∑ _h ∈ (Finset.Icc 1 N).filter (fun h => ¬ 2 ∣ h), (1:ℝ) := by
          apply Finset.sum_le_sum
          intro h hh
          rw [Finset.mem_filter] at hh
          exact_mod_cast pc_odd_card M h hh.2
      _ = (((Finset.Icc 1 N).filter (fun h => ¬ 2 ∣ h)).card : ℝ) := by
          rw [Finset.sum_const, nsmul_eq_mul, mul_one]
      _ ≤ (N:ℝ) := by
          have h1 : ((Finset.Icc 1 N).filter (fun h => ¬ 2 ∣ h)).card ≤ N := by
            calc ((Finset.Icc 1 N).filter (fun h => ¬ 2 ∣ h)).card
                ≤ (Finset.Icc 1 N).card := Finset.card_filter_le _ _
              _ = N := by rw [Nat.card_Icc]; omega
          exact_mod_cast h1
  -- absorb the junk terms
  have hjunk := pc_junk_le t ht1 hL
  rw [← hzdef] at hjunk
  have hp1 : (1:ℝ) ≤ (1 + L)^5 := by
    have := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 1) (by linarith : (1:ℝ) ≤ 1 + L) 5
    simpa using this
  have h1z : (1:ℝ) ≤ z * (1 + L)^5 := by
    have := mul_le_mul hz hp1 (by norm_num) (by linarith)
    linarith
  have hzz : z ≤ z * (1 + L)^5 :=
    le_mul_of_one_le_right (by linarith) hp1
  have hjunk2 : (N:ℝ) * (z * (1 + L)^5 + (z + 1)) + (N:ℝ) ≤ (N:ℝ) * (t / L^2) := by
    have hN0 : (0:ℝ) ≤ (N:ℝ) := Nat.cast_nonneg N
    have hchain : z * (1 + L)^5 + (z + 1) + 1 ≤ 4 * (z * (1 + L)^5) := by linarith
    calc (N:ℝ) * (z * (1 + L)^5 + (z + 1)) + (N:ℝ)
        = (N:ℝ) * (z * (1 + L)^5 + (z + 1) + 1) := by ring
      _ ≤ (N:ℝ) * (4 * (z * (1 + L)^5)) := mul_le_mul_of_nonneg_left hchain hN0
      _ ≤ (N:ℝ) * (t / L^2) := by
          apply mul_le_mul_of_nonneg_left _ hN0
          linarith [hjunk]
  -- conclusion
  have hmain : 225 * t / (c₀ * L^2) * (400 * (N:ℝ)) = 90000/c₀ * ((N:ℝ) * (t / L^2)) := by
    field_simp
    ring
  have hfinal : 90000/c₀ * ((N:ℝ) * (t / L^2)) + (N:ℝ) * (t / L^2)
      = (90000 / c₀ + 1) * (N:ℝ) * t / L^2 := by
    ring
  calc (((Finset.Icc 1 M ×ˢ Finset.Icc 1 M).filter
        (fun pq => Nat.Prime pq.1 ∧ Nat.Prime pq.2 ∧ pq.1 < pq.2 ∧ pq.2 - pq.1 ≤ N)).card : ℝ)
      ≤ ∑ h ∈ Finset.Icc 1 N, (((Finset.Icc 1 M).filter
          (fun n => Nat.Prime n ∧ Nat.Prime (n + h))).card : ℝ) := hfiberR
    _ ≤ 225 * t / (c₀ * L^2) * (400 * N) + (N:ℝ) * (z * (1 + L)^5 + (z + 1)) + (N:ℝ) := by
        rw [hsplit]
        linarith
    _ ≤ 90000/c₀ * ((N:ℝ) * (t / L^2)) + (N:ℝ) * (t / L^2) := by
        rw [← hmain]
        linarith
    _ = (90000 / c₀ + 1) * (N:ℝ) * t / L^2 := hfinal

end Erdos884
end

/-! Flattened from Erdos884/OneScale884.lean. -/
section

/-!
# Erdős 884 — one-scale gap-sum bounds (Lemmas G/H/I of the blueprint)

For a window `B` of `K` primes in `(x₀, x₀+H]` with pairwise gaps `> N`, and
`m := ∏ p ∈ B, p`, we bound the gap sum of `m.divisors` by classifying the
consecutive divisor pairs `(a, b)` by `(ω a, ω b)`:

* both prime (class 1): `oneScale_primePart_le`   — bound `K/N`;
* `2 ≤ ω a = ω b` (class 2): `oneScale_sameCard_le` — bound `2K(1+log K)/N² + 2·4^K/x₀`;
* `ω a ≠ ω b` (class 3): `oneScale_diffCard_le`   — bound `2^(K+3)·K/x₀`;
* the trichotomy glue: `oneScale_gapSum_le`.

All internal helpers are prefixed `os_`.
-/

namespace Erdos884

/-! ### Generic extraction lemma for `pairSumOn` bounds -/

/-- To bound `pairSumOn A C`, it suffices to bound `∑ invGap` over an arbitrary finite set of
pairs each of which lies in `A ×ˢ A`, is increasing, and satisfies `C`. -/
lemma os_pairSumOn_le_of_forall {A : Finset ℕ} {C : ℕ → ℕ → Prop} {r : ℝ}
    (h : ∀ S : Finset (ℕ × ℕ),
      (∀ p ∈ S, p.1 ∈ A ∧ p.2 ∈ A ∧ p.1 < p.2 ∧ C p.1 p.2) →
      ∑ p ∈ S, invGap p.1 p.2 ≤ r) :
    pairSumOn A C ≤ r := by
  have memf : ∀ {q : ℕ × ℕ → Prop} {inst : DecidablePred q} {s : Finset (ℕ × ℕ)} {x : ℕ × ℕ},
      x ∈ @Finset.filter _ q inst s ↔ x ∈ s ∧ q x := by
    intro q inst s x
    letI := inst
    exact Finset.mem_filter
  unfold pairSumOn
  refine h _ fun p hp => ?_
  have hp' := memf.mp hp
  have hpq := Finset.mem_product.mp hp'.1
  exact ⟨hpq.1, hpq.2, hp'.2.1, hp'.2.2⟩

/-! ### Uniqueness of successors and predecessors among consecutive pairs -/

lemma os_consec_succ_unique {A : Finset ℕ} {a b b' : ℕ}
    (h : IsConsecutive A a b) (h' : IsConsecutive A a b') : b = b' := by
  by_contra hne
  rcases Nat.lt_or_ge b b' with hlt | hge
  · exact h'.2.2.2 b h.2.1 ⟨h.2.2.1, hlt⟩
  · have hlt : b' < b := by omega
    exact h.2.2.2 b' h'.2.1 ⟨h'.2.2.1, hlt⟩

lemma os_consec_pred_unique {A : Finset ℕ} {a a' b : ℕ}
    (h : IsConsecutive A a b) (h' : IsConsecutive A a' b) : a = a' := by
  by_contra hne
  rcases Nat.lt_or_ge a a' with hlt | hge
  · exact h.2.2.2 a' h'.1 ⟨hlt, h'.2.2.1⟩
  · have hlt : a' < a := by omega
    exact h'.2.2.2 a h.1 ⟨hlt, h.2.2.1⟩

/-! ### Divisors of `∏ p ∈ B, p` -/

lemma os_prodB_ne_zero {B : Finset ℕ} (hB : ∀ p ∈ B, p.Prime) : (∏ p ∈ B, p) ≠ 0 :=
  (Finset.prod_pos fun p hp => (hB p hp).pos).ne'

lemma os_primeFactors_subset {B : Finset ℕ} (hB : ∀ p ∈ B, p.Prime) {d : ℕ}
    (hd : d ∈ (∏ p ∈ B, p).divisors) : d.primeFactors ⊆ B := by
  have hdvd := (Nat.mem_divisors.mp hd).1
  calc d.primeFactors ⊆ (∏ p ∈ B, p).primeFactors :=
        Nat.primeFactors_mono hdvd (os_prodB_ne_zero hB)
    _ = B := primeFactors_prodPrimes hB

lemma os_prod_primeFactors {B : Finset ℕ} (hB : ∀ p ∈ B, p.Prime) {d : ℕ}
    (hd : d ∈ (∏ p ∈ B, p).divisors) : ∏ p ∈ d.primeFactors, p = d :=
  Nat.prod_primeFactors_of_squarefree
    (Squarefree.squarefree_of_dvd (Nat.mem_divisors.mp hd).1 (squarefree_prodPrimes hB))

lemma os_cast_eq_prod {B : Finset ℕ} (hB : ∀ p ∈ B, p.Prime) {d : ℕ}
    (hd : d ∈ (∏ p ∈ B, p).divisors) :
    (d:ℝ) = ∏ p ∈ d.primeFactors, (p:ℝ) := by
  conv_lhs => rw [← os_prod_primeFactors hB hd]
  push_cast
  rfl

lemma os_mem_B_of_card_one {B : Finset ℕ} (hB : ∀ p ∈ B, p.Prime) {d : ℕ}
    (hd : d ∈ (∏ p ∈ B, p).divisors) (h1 : d.primeFactors.card = 1) : d ∈ B := by
  obtain ⟨p, hp⟩ := Finset.card_eq_one.mp h1
  have hpB : p ∈ B := os_primeFactors_subset hB hd (by rw [hp]; exact Finset.mem_singleton_self p)
  have hdp : d = p := by
    have h := os_prod_primeFactors hB hd
    rw [hp, Finset.prod_singleton] at h
    exact h.symm
  exact hdp ▸ hpB

lemma os_eq_one_of_card_zero {B : Finset ℕ} (hB : ∀ p ∈ B, p.Prime) {d : ℕ}
    (hd : d ∈ (∏ p ∈ B, p).divisors) (h0 : d.primeFactors.card = 0) : d = 1 := by
  have hpf : d.primeFactors = ∅ := Finset.card_eq_zero.mp h0
  have h := os_prod_primeFactors hB hd
  rw [hpf, Finset.prod_empty] at h
  exact h.symm

/-! ### Class 1: consecutive pairs of primes -/

theorem oneScale_primePart_le {B : Finset ℕ} {N K : ℕ}
    (hprime : ∀ p ∈ B, p.Prime) (hcard : B.card = K)
    (hsep : ∀ p ∈ B, ∀ q ∈ B, p < q → N < q - p) (hN : 1 ≤ N) :
    pairSumOn ((∏ p ∈ B, p).divisors)
        (fun a b => a ∈ B ∧ b ∈ B ∧ IsConsecutive ((∏ p ∈ B, p).divisors) a b)
      ≤ (K:ℝ)/N := by
  have hNR : (0:ℝ) < N := by exact_mod_cast hN
  refine os_pairSumOn_le_of_forall fun S hS => ?_
  have hterm : ∀ p ∈ S, invGap p.1 p.2 ≤ (N:ℝ)⁻¹ := by
    intro p hp
    obtain ⟨-, -, hlt, hpB, hqB, -⟩ := hS p hp
    refine invGap_le hNR ?_
    have hgap := hsep p.1 hpB p.2 hqB hlt
    have h1 : p.1 + N < p.2 := by omega
    have h2 : (p.1:ℝ) + N < (p.2:ℝ) := by exact_mod_cast h1
    linarith
  have hcardS : S.card ≤ K := by
    rw [← hcard]
    apply Finset.card_le_card_of_injOn (fun p => p.1)
    · intro p hp
      exact (hS p hp).2.2.2.1
    · intro p hp q hq hpq
      simp only [Finset.mem_coe] at hp hq
      obtain ⟨-, -, -, -, -, hc⟩ := hS p hp
      obtain ⟨-, -, -, -, -, hc'⟩ := hS q hq
      have h1 : p.1 = q.1 := hpq
      have h2 : p.2 = q.2 := os_consec_succ_unique (h1 ▸ hc) hc'
      exact Prod.ext h1 h2
  calc ∑ p ∈ S, invGap p.1 p.2 ≤ ∑ _p ∈ S, (N:ℝ)⁻¹ := Finset.sum_le_sum hterm
    _ = (S.card : ℝ) * (N:ℝ)⁻¹ := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (K:ℝ) * (N:ℝ)⁻¹ := by
        have : (S.card : ℝ) ≤ (K:ℝ) := by exact_mod_cast hcardS
        gcongr
    _ = (K:ℝ)/N := by rw [div_eq_mul_inv]

/-! ### Size bounds for divisors in terms of `ω` -/

/-- Window powers are at most twice the base power: `(x₀+H)^k ≤ 2·x₀^k` when `2KH ≤ x₀`. -/
lemma os_window_pow_le {x₀ H K : ℕ} (h0 : 0 < x₀) (hKH : 2*K*H ≤ x₀) {k : ℕ} (hk : k ≤ K) :
    ((x₀:ℝ) + H) ^ k ≤ 2 * (x₀:ℝ) ^ k := by
  have hx : (0:ℝ) < x₀ := by exact_mod_cast h0
  have hu : (0:ℝ) ≤ (H:ℝ)/x₀ := by positivity
  have hbound : 2 * (k:ℝ) * ((H:ℝ)/x₀) ≤ 1 := by
    have h1 : 2 * k * H ≤ x₀ := le_trans (by
      have : 2 * k * H ≤ 2 * K * H := by
        have := Nat.mul_le_mul_right H (Nat.mul_le_mul_left 2 hk)
        omega
      exact this) hKH
    have h2 : (2 * (k:ℝ) * H) ≤ (x₀:ℝ) := by exact_mod_cast h1
    rw [show 2 * (k:ℝ) * ((H:ℝ)/x₀) = (2 * (k:ℝ) * H) / x₀ by ring, div_le_one hx]
    exact h2
  have heq : (x₀:ℝ) + H = x₀ * (1 + (H:ℝ)/x₀) := by field_simp
  have hpk : (0:ℝ) ≤ (x₀:ℝ)^k := by positivity
  calc ((x₀:ℝ) + H) ^ k = (x₀:ℝ)^k * (1 + (H:ℝ)/x₀)^k := by rw [heq, mul_pow]
    _ ≤ (x₀:ℝ)^k * (1 + 2 * (k:ℝ) * ((H:ℝ)/x₀)) :=
        mul_le_mul_of_nonneg_left (one_add_pow_le_aux hu k hbound) hpk
    _ ≤ (x₀:ℝ)^k * 2 := mul_le_mul_of_nonneg_left (by linarith) hpk
    _ = 2 * (x₀:ℝ)^k := by ring

lemma os_le_prod {B : Finset ℕ} {x₀ H : ℕ} (hB : ∀ p ∈ B, p.Prime)
    (hwin : ∀ p ∈ B, x₀ < p ∧ p ≤ x₀ + H) {d : ℕ} (hd : d ∈ (∏ p ∈ B, p).divisors) :
    (x₀:ℝ) ^ d.primeFactors.card ≤ (d:ℝ) := by
  rw [os_cast_eq_prod hB hd, ← Finset.prod_const]
  refine Finset.prod_le_prod (fun p _ => by positivity) fun p hp => ?_
  have h := (hwin p (os_primeFactors_subset hB hd hp)).1
  exact_mod_cast h.le

lemma os_prod_le {B : Finset ℕ} {x₀ H : ℕ} (hB : ∀ p ∈ B, p.Prime)
    (hwin : ∀ p ∈ B, x₀ < p ∧ p ≤ x₀ + H) {d : ℕ} (hd : d ∈ (∏ p ∈ B, p).divisors) :
    (d:ℝ) ≤ ((x₀:ℝ) + H) ^ d.primeFactors.card := by
  rw [os_cast_eq_prod hB hd, ← Finset.prod_const]
  refine Finset.prod_le_prod (fun p _ => by positivity) fun p hp => ?_
  have h := (hwin p (os_primeFactors_subset hB hd hp)).2
  exact_mod_cast h

/-- A divisor with strictly more prime factors is at least twice as large. -/
lemma os_double_of_omega_lt {B : Finset ℕ} {x₀ H K : ℕ} (hB : ∀ p ∈ B, p.Prime)
    (hcard : B.card = K) (hwin : ∀ p ∈ B, x₀ < p ∧ p ≤ x₀ + H)
    (hKH : 2*K*H ≤ x₀) (hx₀ : 4 ≤ x₀)
    {d e : ℕ} (hd : d ∈ (∏ p ∈ B, p).divisors) (he : e ∈ (∏ p ∈ B, p).divisors)
    (hlt : d.primeFactors.card < e.primeFactors.card) :
    2 * (d:ℝ) ≤ (e:ℝ) := by
  have h0 : 0 < x₀ := by omega
  have hx4 : (4:ℝ) ≤ (x₀:ℝ) := by exact_mod_cast hx₀
  have hkK : d.primeFactors.card ≤ K := by
    rw [← hcard]; exact Finset.card_le_card (os_primeFactors_subset hB hd)
  have hup : (d:ℝ) ≤ 2 * (x₀:ℝ) ^ d.primeFactors.card :=
    le_trans (os_prod_le hB hwin hd) (os_window_pow_le h0 hKH hkK)
  have hlow : (x₀:ℝ) ^ (d.primeFactors.card + 1) ≤ (e:ℝ) := by
    refine le_trans ?_ (os_le_prod hB hwin he)
    exact pow_le_pow_right₀ (by linarith) hlt
  have hpow : (0:ℝ) ≤ (x₀:ℝ) ^ d.primeFactors.card := by positivity
  calc 2 * (d:ℝ) ≤ 2 * (2 * (x₀:ℝ) ^ d.primeFactors.card) := by linarith
    _ = 4 * (x₀:ℝ) ^ d.primeFactors.card := by ring
    _ ≤ (x₀:ℝ) * (x₀:ℝ) ^ d.primeFactors.card := by nlinarith
    _ = (x₀:ℝ) ^ (d.primeFactors.card + 1) := by rw [pow_succ]; ring
    _ ≤ (e:ℝ) := hlow

/-! ### Class 3: consecutive pairs with different `ω` -/

theorem oneScale_diffCard_le {B : Finset ℕ} {x₀ H K : ℕ}
    (hprime : ∀ p ∈ B, p.Prime) (hcard : B.card = K)
    (hwin : ∀ p ∈ B, x₀ < p ∧ p ≤ x₀ + H)
    (hKH : 2*K*H ≤ x₀) (hx₀ : 4 ≤ x₀) (hH : 1 ≤ H) (hK : 1 ≤ K) :
    pairSumOn ((∏ p ∈ B, p).divisors)
        (fun a b => a.primeFactors.card ≠ b.primeFactors.card)
      ≤ (2:ℝ)^(K+3)*K/x₀ := by
  classical
  set A := (∏ p ∈ B, p).divisors with hA
  set g : ℕ → ℝ := fun b => if b = 1 then 0 else 2/(b:ℝ) with hg
  have h0 : 0 < x₀ := by omega
  have hx0R : (0:ℝ) < (x₀:ℝ) := by exact_mod_cast h0
  have hgnn : ∀ b : ℕ, 0 ≤ g b := by
    intro b
    simp only [hg]
    split <;> positivity
  -- Step B: the sum of `g` over the divisors
  have hgsum : ∑ b ∈ A, g b ≤ 4 * (K:ℝ) / x₀ := by
    have h1mem : 1 ∈ A := Nat.one_mem_divisors.mpr (os_prodB_ne_zero hprime)
    have hsplit : g 1 + ∑ b ∈ A.erase 1, g b = ∑ b ∈ A, g b :=
      Finset.add_sum_erase A g h1mem
    have hg1 : g 1 = 0 := by simp [hg]
    have herase : ∑ b ∈ A.erase 1, g b = 2 * ∑ b ∈ A.erase 1, ((b:ℝ))⁻¹ := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun b hb => ?_
      have hb1 : b ≠ 1 := Finset.ne_of_mem_erase hb
      simp only [hg, if_neg hb1]
      rw [div_eq_mul_inv]
    have hinv : ∑ b ∈ A.erase 1, ((b:ℝ))⁻¹ ≤ 2 * (K:ℝ) / x₀ := by
      have := sum_inv_divisors_erase_one_le hprime
        (fun p hp => (hwin p hp).1.le)
        (by rw [hcard]; calc 2*K ≤ 2*K*H := by nlinarith
              _ ≤ x₀ := hKH) h0
      rw [hcard] at this
      exact this
    calc ∑ b ∈ A, g b = g 1 + ∑ b ∈ A.erase 1, g b := hsplit.symm
      _ = 2 * ∑ b ∈ A.erase 1, ((b:ℝ))⁻¹ := by rw [hg1, herase, zero_add]
      _ ≤ 2 * (2 * (K:ℝ) / x₀) := by
          have hnn : 0 ≤ ∑ b ∈ A.erase 1, ((b:ℝ))⁻¹ :=
            Finset.sum_nonneg fun b _ => by positivity
          linarith
      _ = 4 * (K:ℝ) / x₀ := by ring
  -- Step A: bound the pair sum by `card A * ∑ g`
  have hmain : pairSumOn A (fun a b => a.primeFactors.card ≠ b.primeFactors.card)
      ≤ (A.card : ℝ) * ∑ b ∈ A, g b := by
    refine os_pairSumOn_le_of_forall fun S hS => ?_
    have hterm : ∀ p ∈ S, invGap p.1 p.2 ≤ g p.2 := by
      intro p hp
      obtain ⟨ha, hb, hlt, hne⟩ := hS p hp
      have ha1 : 1 ≤ p.1 := Nat.pos_of_mem_divisors ha
      have hb1 : p.2 ≠ 1 := by omega
      have hbR : (1:ℝ) ≤ (p.2:ℝ) := by exact_mod_cast Nat.pos_of_mem_divisors hb
      have habR : (p.1:ℝ) < (p.2:ℝ) := by exact_mod_cast hlt
      have hdouble : 2 * (p.1:ℝ) ≤ (p.2:ℝ) := by
        rcases Nat.lt_or_ge p.1.primeFactors.card p.2.primeFactors.card with hω | hω
        · exact os_double_of_omega_lt hprime hcard hwin hKH hx₀ ha hb hω
        · have hω' : p.2.primeFactors.card < p.1.primeFactors.card := by omega
          have h2 := os_double_of_omega_lt hprime hcard hwin hKH hx₀ hb ha hω'
          linarith
      have hgap : (p.2:ℝ)/2 ≤ (p.2:ℝ) - p.1 := by linarith
      have hhalf : (0:ℝ) < (p.2:ℝ)/2 := by linarith
      calc invGap p.1 p.2 ≤ ((p.2:ℝ)/2)⁻¹ := inv_anti₀ hhalf hgap
        _ = 2/(p.2:ℝ) := by rw [inv_div]
        _ = g p.2 := by simp [hg, if_neg hb1]
    have hsub : S ⊆ A ×ˢ A := by
      intro p hp
      exact Finset.mem_product.mpr ⟨(hS p hp).1, (hS p hp).2.1⟩
    calc ∑ p ∈ S, invGap p.1 p.2 ≤ ∑ p ∈ S, g p.2 := Finset.sum_le_sum hterm
      _ ≤ ∑ p ∈ A ×ˢ A, g p.2 :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub fun p _ _ => hgnn p.2
      _ = ∑ a ∈ A, ∑ b ∈ A, g b := Finset.sum_product A A (fun p => g p.2)
      _ = (A.card : ℝ) * ∑ b ∈ A, g b := by rw [Finset.sum_const, nsmul_eq_mul]
  -- assemble
  have hAcard : (A.card : ℝ) = (2:ℝ)^K := by
    rw [hA, card_divisors_prodPrimes hprime, hcard]
    push_cast
    rfl
  have hsumnn : (0:ℝ) ≤ ∑ b ∈ A, g b := Finset.sum_nonneg fun b _ => hgnn b
  calc pairSumOn A (fun a b => a.primeFactors.card ≠ b.primeFactors.card)
      ≤ (A.card : ℝ) * ∑ b ∈ A, g b := hmain
    _ = (2:ℝ)^K * ∑ b ∈ A, g b := by rw [hAcard]
    _ ≤ (2:ℝ)^K * (4 * (K:ℝ) / x₀) := by
        have : (0:ℝ) ≤ (2:ℝ)^K := by positivity
        exact mul_le_mul_of_nonneg_left hgsum this
    _ = (2:ℝ)^(K+2) * (K:ℝ) / x₀ := by rw [pow_add]; ring
    _ ≤ (2:ℝ)^(K+3)*K/x₀ := by
        have h1 : (2:ℝ)^(K+2) ≤ (2:ℝ)^(K+3) :=
          pow_le_pow_right₀ (by norm_num) (by omega)
        have h2 : (0:ℝ) ≤ (K:ℝ) := Nat.cast_nonneg K
        have h3 : (0:ℝ) ≤ ((x₀:ℝ))⁻¹ := by positivity
        rw [div_eq_mul_inv, div_eq_mul_inv]
        have := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right h1 h2) h3
        exact this

/-! ### The minimum element and the gap product `D(v)` -/

/-- The minimum of a finset of naturals, defaulting to `0` on the empty set. -/
def os_min (v : Finset ℕ) : ℕ := if h : v.Nonempty then v.min' h else 0

lemma os_min_eq {v : Finset ℕ} (h : v.Nonempty) : os_min v = v.min' h := dif_pos h

lemma os_min_mem {v : Finset ℕ} (h : v.Nonempty) : os_min v ∈ v := by
  rw [os_min_eq h]; exact v.min'_mem h

lemma os_min_le {v : Finset ℕ} {p : ℕ} (hp : p ∈ v) : os_min v ≤ p := by
  rw [os_min_eq ⟨p, hp⟩]; exact v.min'_le p hp

/-- The gap product `D(v) := ∏_{p ∈ v \ {min v}} (p - min v)` as a real number. -/
noncomputable def os_D (v : Finset ℕ) : ℝ :=
  ∏ p ∈ v.erase (os_min v), ((p:ℝ) - (os_min v : ℝ))

lemma os_lt_of_mem_erase_min {v : Finset ℕ} {p : ℕ} (hp : p ∈ v.erase (os_min v)) :
    os_min v < p :=
  lt_of_le_of_ne (os_min_le (Finset.mem_of_mem_erase hp))
    (Ne.symm (Finset.ne_of_mem_erase hp))

lemma os_D_factor_ge {B : Finset ℕ} {N : ℕ}
    (hsep : ∀ p ∈ B, ∀ q ∈ B, p < q → N < q - p) {v : Finset ℕ} (hv : v ⊆ B)
    (hvne : v.Nonempty) {p : ℕ} (hp : p ∈ v.erase (os_min v)) :
    (N:ℝ) + 1 ≤ (p:ℝ) - (os_min v : ℝ) := by
  have hlt := os_lt_of_mem_erase_min hp
  have hminB : os_min v ∈ B := hv (os_min_mem hvne)
  have hpB : p ∈ B := hv (Finset.mem_of_mem_erase hp)
  have hgap := hsep _ hminB _ hpB hlt
  have h1 : os_min v + (N + 1) ≤ p := by omega
  have h2 : ((os_min v : ℕ):ℝ) + ((N:ℝ)+1) ≤ (p:ℝ) := by exact_mod_cast h1
  linarith

lemma os_D_pos {B : Finset ℕ} {N : ℕ}
    (hsep : ∀ p ∈ B, ∀ q ∈ B, p < q → N < q - p) {v : Finset ℕ} (hv : v ⊆ B)
    (hvne : v.Nonempty) : 0 < os_D v := by
  unfold os_D
  refine Finset.prod_pos fun p hp => ?_
  have h := os_D_factor_ge hsep hv hvne hp
  have hN : (0:ℝ) ≤ (N:ℝ) := Nat.cast_nonneg N
  linarith

/-! ### The elementary-symmetric counting bound -/

/-- `∑_{w ⊆ S, |w| = j} ∏_{p ∈ w} f p ≤ (∑_{p ∈ S} f p)^j` for nonnegative `f`. -/
lemma os_esymm_le_pow_sum {S : Finset ℕ} {f : ℕ → ℝ} (hf : ∀ p ∈ S, 0 ≤ f p) :
    ∀ j : ℕ, ∑ w ∈ S.powerset.filter (fun w => w.card = j), ∏ p ∈ w, f p
      ≤ (∑ p ∈ S, f p) ^ j := by
  classical
  intro j
  induction j with
  | zero =>
    have h : S.powerset.filter (fun w => w.card = 0) = {∅} := by
      ext u
      simp only [Finset.mem_filter, Finset.mem_powerset, Finset.card_eq_zero,
        Finset.mem_singleton]
      exact ⟨fun h => h.2, fun h => ⟨h ▸ Finset.empty_subset S, h⟩⟩
    rw [h, Finset.sum_singleton, Finset.prod_empty, pow_zero]
  | succ j ih =>
    set T := S.powerset.filter (fun w => w.card = j + 1) with hT
    set U := S ×ˢ (S.powerset.filter (fun w => w.card = j)) with hU
    have hTmem : ∀ w ∈ T, w ⊆ S ∧ w.card = j + 1 := by
      intro w hw
      have := Finset.mem_filter.mp hw
      exact ⟨Finset.mem_powerset.mp this.1, this.2⟩
    have hTne : ∀ w ∈ T, w.Nonempty := by
      intro w hw
      exact Finset.card_pos.mp (by rw [(hTmem w hw).2]; omega)
    have hstep1 : ∀ w ∈ T, ∏ p ∈ w, f p
        = f (os_min w) * ∏ p ∈ w.erase (os_min w), f p := fun w hw =>
      (Finset.mul_prod_erase w f (os_min_mem (hTne w hw))).symm
    have hinj : ∀ w ∈ T, ∀ w' ∈ T,
        (os_min w, w.erase (os_min w)) = (os_min w', w'.erase (os_min w')) → w = w' := by
      intro w hw w' hw' heq
      have h1 : os_min w = os_min w' := (Prod.mk.injEq _ _ _ _).mp heq |>.1
      have h2 : w.erase (os_min w) = w'.erase (os_min w') :=
        (Prod.mk.injEq _ _ _ _).mp heq |>.2
      calc w = insert (os_min w) (w.erase (os_min w)) :=
            (Finset.insert_erase (os_min_mem (hTne w hw))).symm
        _ = insert (os_min w') (w'.erase (os_min w')) := by rw [h2, h1]
        _ = w' := Finset.insert_erase (os_min_mem (hTne w' hw'))
    have himg : ∀ w ∈ T, (os_min w, w.erase (os_min w)) ∈ U := by
      intro w hw
      obtain ⟨hws, hwc⟩ := hTmem w hw
      refine Finset.mem_product.mpr ⟨hws (os_min_mem (hTne w hw)), ?_⟩
      refine Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr
        (fun p hp => hws (Finset.mem_of_mem_erase hp)), ?_⟩
      rw [Finset.card_erase_of_mem (os_min_mem (hTne w hw)), hwc]
      omega
    have hsum0 : (0:ℝ) ≤ ∑ p ∈ S, f p := Finset.sum_nonneg hf
    calc ∑ w ∈ T, ∏ p ∈ w, f p
        = ∑ w ∈ T, f (os_min w) * ∏ p ∈ w.erase (os_min w), f p :=
          Finset.sum_congr rfl hstep1
      _ = ∑ x ∈ T.image (fun w => (os_min w, w.erase (os_min w))),
            f x.1 * ∏ p ∈ x.2, f p :=
          (Finset.sum_image (f := fun x : ℕ × Finset ℕ => f x.1 * ∏ p ∈ x.2, f p)
            hinj).symm
      _ ≤ ∑ x ∈ U, f x.1 * ∏ p ∈ x.2, f p := by
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
          · intro x hx
            obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hx
            exact himg w hw
          · intro x hx _
            have hx' := Finset.mem_product.mp hx
            refine mul_nonneg (hf x.1 hx'.1) (Finset.prod_nonneg fun p hp => ?_)
            exact hf p (Finset.mem_powerset.mp (Finset.mem_filter.mp hx'.2).1 hp)
      _ = (∑ p ∈ S, f p) * ∑ w ∈ S.powerset.filter (fun w => w.card = j), ∏ p ∈ w, f p := by
          rw [Finset.sum_mul_sum]
          exact Finset.sum_product _ _ _
      _ ≤ (∑ p ∈ S, f p) * (∑ p ∈ S, f p) ^ j :=
          mul_le_mul_of_nonneg_left ih hsum0
      _ = (∑ p ∈ S, f p) ^ (j + 1) := by rw [pow_succ]; ring

/-! ### Separated elements grow linearly -/

/-- In an `N`-separated set of primes, the maximum of any `n`-element subset above `p₀`
is at least `p₀ + n(N+1)`. -/
lemma os_ge_of_card_le {B : Finset ℕ} {N p₀ : ℕ}
    (hsep : ∀ p ∈ B, ∀ q ∈ B, p < q → N < q - p) (hp₀ : p₀ ∈ B) :
    ∀ n : ℕ, ∀ S : Finset ℕ, S ⊆ B → (∀ p ∈ S, p₀ < p) → n ≤ S.card →
      ∀ hS : S.Nonempty, p₀ + n * (N+1) ≤ S.max' hS := by
  intro n
  induction n with
  | zero =>
    intro S _ hall _ hS
    have := hall _ (S.max'_mem hS)
    omega
  | succ n ih =>
    intro S hSB hall hcard hS
    have hqS : S.max' hS ∈ S := S.max'_mem hS
    have hqB : S.max' hS ∈ B := hSB hqS
    rcases (S.erase (S.max' hS)).eq_empty_or_nonempty with hemp | hne
    · have hc1 : (S.erase (S.max' hS)).card = S.card - 1 :=
        Finset.card_erase_of_mem hqS
      rw [hemp] at hc1
      simp only [Finset.card_empty] at hc1
      have hn0 : n = 0 := by omega
      subst hn0
      have hgap := hsep p₀ hp₀ _ hqB (hall _ hqS)
      omega
    · have hsub : S.erase (S.max' hS) ⊆ B :=
        fun p hp => hSB (Finset.mem_of_mem_erase hp)
      have hall' : ∀ p ∈ S.erase (S.max' hS), p₀ < p :=
        fun p hp => hall p (Finset.mem_of_mem_erase hp)
      have hcard' : n ≤ (S.erase (S.max' hS)).card := by
        rw [Finset.card_erase_of_mem hqS]
        omega
      have hih := ih _ hsub hall' hcard' hne
      have hq'S : (S.erase (S.max' hS)).max' hne ∈ S.erase (S.max' hS) :=
        (S.erase (S.max' hS)).max'_mem hne
      have hq'B : (S.erase (S.max' hS)).max' hne ∈ B := hsub hq'S
      have hq'lt : (S.erase (S.max' hS)).max' hne < S.max' hS := by
        have h1 := Finset.mem_of_mem_erase hq'S
        have h2 := Finset.ne_of_mem_erase hq'S
        have h3 := S.le_max' _ h1
        omega
      have hgap := hsep _ hq'B _ hqB hq'lt
      calc p₀ + (n+1) * (N+1) = (p₀ + n * (N+1)) + (N+1) := by ring
        _ ≤ (S.erase (S.max' hS)).max' hne + (N+1) := Nat.add_le_add_right hih _
        _ ≤ S.max' hS := by omega

/-! ### The separated reciprocal sum is at most a harmonic sum -/

lemma os_sum_inv_le_harmonic {B : Finset ℕ} {N p₀ : ℕ}
    (hsep : ∀ p ∈ B, ∀ q ∈ B, p < q → N < q - p) (hp₀ : p₀ ∈ B) (hN : 1 ≤ N) :
    ∀ n : ℕ, ∀ S : Finset ℕ, S ⊆ B → (∀ p ∈ S, p₀ < p) → S.card = n →
      ∑ p ∈ S, ((p:ℝ) - (p₀:ℝ))⁻¹ ≤ (N:ℝ)⁻¹ * ∑ j ∈ Finset.Icc 1 n, ((j:ℝ))⁻¹ := by
  intro n
  induction n with
  | zero =>
    intro S _ _ hcard
    rw [Finset.card_eq_zero.mp hcard]
    simp
  | succ n ih =>
    intro S hSB hall hcard
    have hS : S.Nonempty := Finset.card_pos.mp (by omega)
    have hqS : S.max' hS ∈ S := S.max'_mem hS
    have hNR : (0:ℝ) < (N:ℝ) := by exact_mod_cast hN
    -- lower bound on the largest gap
    have hqmax := os_ge_of_card_le hsep hp₀ (n+1) S hSB hall (le_of_eq hcard.symm) hS
    have hgapN : (n+1) * N + p₀ ≤ S.max' hS := by
      have h1 : (n+1) * N ≤ (n+1) * (N+1) := Nat.mul_le_mul_left _ (by omega)
      omega
    have hgapR : ((n:ℝ)+1) * N ≤ (S.max' hS : ℝ) - p₀ := by
      have h2 : (((n+1) * N + p₀ : ℕ) : ℝ) ≤ ((S.max' hS : ℕ) : ℝ) := by
        exact_mod_cast hgapN
      push_cast at h2
      linarith
    have hpos : (0:ℝ) < ((n:ℝ)+1) * N := by positivity
    have hterm : ((S.max' hS : ℝ) - (p₀:ℝ))⁻¹ ≤ (N:ℝ)⁻¹ * ((n:ℝ)+1)⁻¹ := by
      calc ((S.max' hS : ℝ) - (p₀:ℝ))⁻¹ ≤ (((n:ℝ)+1) * N)⁻¹ := inv_anti₀ hpos hgapR
        _ = (N:ℝ)⁻¹ * ((n:ℝ)+1)⁻¹ := by rw [mul_inv]; ring
    -- induction on the rest
    have hih := ih (S.erase (S.max' hS))
      (fun p hp => hSB (Finset.mem_of_mem_erase hp))
      (fun p hp => hall p (Finset.mem_of_mem_erase hp))
      (by rw [Finset.card_erase_of_mem hqS, hcard]; omega)
    have hsplit : ((S.max' hS : ℝ) - (p₀:ℝ))⁻¹
        + ∑ p ∈ S.erase (S.max' hS), ((p:ℝ) - (p₀:ℝ))⁻¹
        = ∑ p ∈ S, ((p:ℝ) - (p₀:ℝ))⁻¹ :=
      Finset.add_sum_erase S (fun p => ((p:ℝ) - (p₀:ℝ))⁻¹) hqS
    have htop : ∑ j ∈ Finset.Icc 1 (n+1), ((j:ℝ))⁻¹
        = ∑ j ∈ Finset.Icc 1 n, ((j:ℝ))⁻¹ + ((n:ℝ)+1)⁻¹ := by
      rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ n + 1)]
      push_cast
      ring
    calc ∑ p ∈ S, ((p:ℝ) - (p₀:ℝ))⁻¹
        = ((S.max' hS : ℝ) - (p₀:ℝ))⁻¹
          + ∑ p ∈ S.erase (S.max' hS), ((p:ℝ) - (p₀:ℝ))⁻¹ := hsplit.symm
      _ ≤ (N:ℝ)⁻¹ * ((n:ℝ)+1)⁻¹ + (N:ℝ)⁻¹ * ∑ j ∈ Finset.Icc 1 n, ((j:ℝ))⁻¹ :=
          add_le_add hterm hih
      _ = (N:ℝ)⁻¹ * (∑ j ∈ Finset.Icc 1 n, ((j:ℝ))⁻¹ + ((n:ℝ)+1)⁻¹) := by ring
      _ = (N:ℝ)⁻¹ * ∑ j ∈ Finset.Icc 1 (n+1), ((j:ℝ))⁻¹ := by rw [htop]

/-- The key reciprocal-gap sum bound: `∑_{p ∈ B, p > p₀} 1/(p - p₀) ≤ (1 + log K)/N`. -/
lemma os_sep_sum_inv {B : Finset ℕ} {N K p₀ : ℕ} (hcard : B.card = K)
    (hsep : ∀ p ∈ B, ∀ q ∈ B, p < q → N < q - p) (hN : 1 ≤ N) (hp₀ : p₀ ∈ B) :
    ∑ p ∈ B.filter (fun p => p₀ < p), ((p:ℝ) - (p₀:ℝ))⁻¹ ≤ (1 + Real.log K) / N := by
  classical
  have h1 := os_sum_inv_le_harmonic hsep hp₀ hN (B.filter (fun p => p₀ < p)).card
    (B.filter (fun p => p₀ < p)) (Finset.filter_subset _ _)
    (fun p hp => (Finset.mem_filter.mp hp).2) rfl
  have h2 : ∑ j ∈ Finset.Icc 1 (B.filter (fun p => p₀ < p)).card, ((j:ℝ))⁻¹
      ≤ ∑ j ∈ Finset.Icc 1 K, ((j:ℝ))⁻¹ := by
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun j _ _ => by positivity)
    apply Finset.Icc_subset_Icc le_rfl
    rw [← hcard]
    exact Finset.card_le_card (Finset.filter_subset _ _)
  have h3 := sum_inv_le_one_add_log K
  have hNinv : (0:ℝ) ≤ (N:ℝ)⁻¹ := by positivity
  calc ∑ p ∈ B.filter (fun p => p₀ < p), ((p:ℝ) - (p₀:ℝ))⁻¹
      ≤ (N:ℝ)⁻¹ * ∑ j ∈ Finset.Icc 1 (B.filter (fun p => p₀ < p)).card, ((j:ℝ))⁻¹ := h1
    _ ≤ (N:ℝ)⁻¹ * (1 + Real.log K) :=
        mul_le_mul_of_nonneg_left (le_trans h2 h3) hNinv
    _ = (1 + Real.log K) / N := by rw [div_eq_mul_inv, mul_comm]

/-! ### Geometric tail -/

lemma os_geom_le_two {q : ℝ} (h0 : 0 ≤ q) (h2 : q ≤ 1/2) :
    ∀ n : ℕ, ∑ i ∈ Finset.range n, q ^ i ≤ 2 := by
  intro n
  induction n with
  | zero => norm_num
  | succ n ih =>
    rw [Finset.sum_range_succ']
    have h3 : ∑ i ∈ Finset.range n, q ^ (i+1) = q * ∑ i ∈ Finset.range n, q ^ i := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by rw [pow_succ]; ring
    rw [h3, pow_zero]
    have ha : q * ∑ i ∈ Finset.range n, q ^ i ≤ q * 2 := mul_le_mul_of_nonneg_left ih h0
    have hb : q * 2 ≤ 1 := by linarith
    linarith

lemma os_geom_tail_le {q : ℝ} (h0 : 0 ≤ q) (h2 : q ≤ 1/2) (K : ℕ) :
    ∑ k ∈ Finset.Icc 2 K, q ^ (k-1) ≤ 2 * q := by
  have h1 : ∑ k ∈ Finset.Icc 2 K, q ^ (k-1) = ∑ k ∈ Finset.Icc 2 K, q * q^(k-2) := by
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk2 : 2 ≤ k := (Finset.mem_Icc.mp hk).1
    have he : k - 1 = (k-2) + 1 := by omega
    rw [he, pow_succ]
    ring
  rw [h1, ← Finset.mul_sum]
  have h3 : ∑ k ∈ Finset.Icc 2 K, q^(k-2) ≤ 2 := by
    have hIcc : Finset.Icc 2 K = Finset.Ico 2 (K+1) := by
      ext x
      simp only [Finset.mem_Icc, Finset.mem_Ico]
      omega
    rw [hIcc, Finset.sum_Ico_eq_sum_range]
    have hcongr : ∀ i ∈ Finset.range (K+1-2), q^((2+i)-2) = q^i := fun i _ => by
      congr 1
      omega
    rw [Finset.sum_congr rfl hcongr]
    exact os_geom_le_two h0 h2 _
  calc q * ∑ k ∈ Finset.Icc 2 K, q^(k-2) ≤ q * 2 := mul_le_mul_of_nonneg_left h3 h0
    _ = 2 * q := by ring

/-! ### Summing `1/D(v)` over subsets with a given minimum and cardinality -/

lemma os_fiber_D_inv_le {B : Finset ℕ} {N K : ℕ} (hcard : B.card = K)
    (hsep : ∀ p ∈ B, ∀ q ∈ B, p < q → N < q - p) (hN : 1 ≤ N)
    {p₀ : ℕ} (hp₀ : p₀ ∈ B) {k : ℕ} (hk : 1 ≤ k) :
    ∑ v ∈ (B.powerset.filter (fun v => v.card = k)).filter (fun v => os_min v = p₀),
        (os_D v)⁻¹
      ≤ ((1 + Real.log K) / N) ^ (k - 1) := by
  classical
  have hfnn : ∀ p ∈ B.filter (fun p => p₀ < p), (0:ℝ) ≤ ((p:ℝ) - (p₀:ℝ))⁻¹ := by
    intro p hp
    have h1 : p₀ < p := (Finset.mem_filter.mp hp).2
    have h2 : (p₀:ℝ) < (p:ℝ) := by exact_mod_cast h1
    exact inv_nonneg.mpr (by linarith)
  have hFmem : ∀ v ∈ (B.powerset.filter (fun v => v.card = k)).filter
      (fun v => os_min v = p₀), v ⊆ B ∧ v.card = k ∧ os_min v = p₀ := by
    intro v hv
    obtain ⟨hv1, hv2⟩ := Finset.mem_filter.mp hv
    obtain ⟨hv3, hv4⟩ := Finset.mem_filter.mp hv1
    exact ⟨Finset.mem_powerset.mp hv3, hv4, hv2⟩
  have hp₀v : ∀ v ∈ (B.powerset.filter (fun v => v.card = k)).filter
      (fun v => os_min v = p₀), p₀ ∈ v := by
    intro v hv
    have hne : v.Nonempty := Finset.card_pos.mp (by rw [(hFmem v hv).2.1]; omega)
    exact (hFmem v hv).2.2 ▸ os_min_mem hne
  have hterm : ∀ v ∈ (B.powerset.filter (fun v => v.card = k)).filter
      (fun v => os_min v = p₀), (os_D v)⁻¹ = ∏ p ∈ v.erase p₀, ((p:ℝ) - (p₀:ℝ))⁻¹ := by
    intro v hv
    unfold os_D
    rw [(hFmem v hv).2.2, ← Finset.prod_inv_distrib]
  have hinj : Set.InjOn (fun v : Finset ℕ => v.erase p₀)
      ↑((B.powerset.filter (fun v => v.card = k)).filter (fun v => os_min v = p₀)) := by
    intro v hv v' hv' he
    have hv1 := Finset.mem_coe.mp hv
    have hv'1 := Finset.mem_coe.mp hv'
    have he' : v.erase p₀ = v'.erase p₀ := he
    calc v = insert p₀ (v.erase p₀) := (Finset.insert_erase (hp₀v v hv1)).symm
      _ = insert p₀ (v'.erase p₀) := by rw [he']
      _ = v' := Finset.insert_erase (hp₀v v' hv'1)
  have himg : ∀ v ∈ (B.powerset.filter (fun v => v.card = k)).filter
      (fun v => os_min v = p₀), v.erase p₀ ∈
        (B.filter (fun p => p₀ < p)).powerset.filter (fun w => w.card = k - 1) := by
    intro v hv
    obtain ⟨hvB, hvc, hvm⟩ := hFmem v hv
    refine Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr ?_, ?_⟩
    · intro p hp
      refine Finset.mem_filter.mpr ⟨hvB (Finset.mem_of_mem_erase hp), ?_⟩
      have h1 : os_min v ≤ p := os_min_le (Finset.mem_of_mem_erase hp)
      have h2 : p ≠ p₀ := Finset.ne_of_mem_erase hp
      omega
    · rw [Finset.card_erase_of_mem (hp₀v v hv), hvc]
  calc ∑ v ∈ (B.powerset.filter (fun v => v.card = k)).filter
        (fun v => os_min v = p₀), (os_D v)⁻¹
      = ∑ v ∈ (B.powerset.filter (fun v => v.card = k)).filter
          (fun v => os_min v = p₀), ∏ p ∈ v.erase p₀, ((p:ℝ) - (p₀:ℝ))⁻¹ :=
        Finset.sum_congr rfl hterm
    _ = ∑ w ∈ ((B.powerset.filter (fun v => v.card = k)).filter
          (fun v => os_min v = p₀)).image (fun v : Finset ℕ => v.erase p₀),
            ∏ p ∈ w, (((p:ℕ):ℝ) - (p₀:ℝ))⁻¹ :=
        (Finset.sum_image
          (f := fun w : Finset ℕ => ∏ p ∈ w, ((p:ℝ) - (p₀:ℝ))⁻¹) hinj).symm
    _ ≤ ∑ w ∈ (B.filter (fun p => p₀ < p)).powerset.filter (fun w => w.card = k - 1),
          ∏ p ∈ w, ((p:ℝ) - (p₀:ℝ))⁻¹ := by
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
        · intro w hw
          obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hw
          exact himg v hv
        · intro w hw _
          refine Finset.prod_nonneg fun p hp => ?_
          exact hfnn p (Finset.mem_powerset.mp (Finset.mem_filter.mp hw).1 hp)
    _ ≤ (∑ p ∈ B.filter (fun p => p₀ < p), ((p:ℝ) - (p₀:ℝ))⁻¹) ^ (k-1) :=
        os_esymm_le_pow_sum hfnn (k-1)
    _ ≤ ((1 + Real.log K) / N) ^ (k-1) := by
        refine pow_le_pow_left₀ (Finset.sum_nonneg hfnn) ?_ _
        exact os_sep_sum_inv hcard hsep hN hp₀

/-- Summing `1/D(v)` over all `k`-element subsets of `B`. -/
lemma os_sum_D_inv_le {B : Finset ℕ} {N K : ℕ} (hcard : B.card = K)
    (hsep : ∀ p ∈ B, ∀ q ∈ B, p < q → N < q - p) (hN : 1 ≤ N) {k : ℕ} (hk : 1 ≤ k) :
    ∑ v ∈ B.powerset.filter (fun v => v.card = k), (os_D v)⁻¹
      ≤ (K:ℝ) * ((1 + Real.log K) / N) ^ (k - 1) := by
  classical
  have hmaps : ∀ v ∈ B.powerset.filter (fun v => v.card = k), os_min v ∈ B := by
    intro v hv
    obtain ⟨hv1, hv2⟩ := Finset.mem_filter.mp hv
    have hne : v.Nonempty := Finset.card_pos.mp (by omega)
    exact Finset.mem_powerset.mp hv1 (os_min_mem hne)
  have hfib := (Finset.sum_fiberwise_of_maps_to hmaps (fun v => (os_D v)⁻¹)).symm
  rw [hfib]
  calc ∑ p₀ ∈ B, ∑ v ∈ (B.powerset.filter (fun v => v.card = k)).filter
        (fun v => os_min v = p₀), (os_D v)⁻¹
      ≤ ∑ p₀ ∈ B, ((1 + Real.log K) / N) ^ (k - 1) :=
        Finset.sum_le_sum fun p₀ hp₀ => os_fiber_D_inv_le hcard hsep hN hp₀ hk
    _ = (B.card : ℝ) * ((1 + Real.log K) / N) ^ (k - 1) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ = (K:ℝ) * ((1 + Real.log K) / N) ^ (k - 1) := by rw [hcard]

/-! ### Negated root sets: bridging to `F_const_gap` -/

lemma os_neg_injective : Function.Injective (fun p : ℕ => -(p:ℝ)) := by
  intro p q h
  have h' : -(p:ℝ) = -(q:ℝ) := h
  have h2 : (p:ℝ) = (q:ℝ) := by linarith
  exact_mod_cast h2

lemma os_neg_injOn (v : Finset ℕ) : Set.InjOn (fun p : ℕ => -(p:ℝ)) ↑v :=
  fun p _ q _ h => os_neg_injective h

lemma os_prod_neg_image (v : Finset ℕ) (x : ℝ) :
    ∏ c ∈ v.image (fun p : ℕ => -(p:ℝ)), (x - c) = ∏ p ∈ v, (x + (p:ℝ)) := by
  rw [Finset.prod_image (os_neg_injOn v)]
  exact Finset.prod_congr rfl fun p _ => by ring

lemma os_max_image_neg {v : Finset ℕ} (hv : v.Nonempty) :
    (v.image (fun p : ℕ => -(p:ℝ))).max' (hv.image _) = -((v.min' hv : ℕ) : ℝ) := by
  apply le_antisymm
  · apply Finset.max'_le
    intro y hy
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hy
    have h1 : v.min' hv ≤ p := v.min'_le p hp
    have h2 : ((v.min' hv : ℕ) : ℝ) ≤ (p:ℝ) := by exact_mod_cast h1
    simp only [neg_le_neg_iff]
    exact h2
  · apply Finset.le_max'
    exact Finset.mem_image.mpr ⟨v.min' hv, v.min'_mem hv, rfl⟩

/-- Class-2(ii) gap bound: if a consecutive same-`ω` pair has all shifted elementary
symmetric sums equal below the cardinality, then `b - a ≥ N · D(b.primeFactors)`. -/
lemma os_const_gap_ge {B : Finset ℕ} {x₀ N : ℕ}
    (hprime : ∀ p ∈ B, p.Prime) (hwin : ∀ p ∈ B, x₀ < p)
    (hsep : ∀ p ∈ B, ∀ q ∈ B, p < q → N < q - p)
    {a b : ℕ} (ha : a ∈ (∏ p ∈ B, p).divisors) (hb : b ∈ (∏ p ∈ B, p).divisors)
    (hab : a < b) (hcard2 : 2 ≤ a.primeFactors.card)
    (hcardeq : a.primeFactors.card = b.primeFactors.card)
    (heq : ∀ j, j < a.primeFactors.card →
      esymmShift x₀ a.primeFactors j = esymmShift x₀ b.primeFactors j) :
    (N:ℝ) * os_D b.primeFactors ≤ (b:ℝ) - (a:ℝ) := by
  have hu : a.primeFactors ⊆ B := os_primeFactors_subset hprime ha
  have hv : b.primeFactors ⊆ B := os_primeFactors_subset hprime hb
  have hune : a.primeFactors.Nonempty := Finset.card_pos.mp (by omega)
  have hvne : b.primeFactors.Nonempty := Finset.card_pos.mp (by omega)
  have hcasta : (a:ℝ) = ∏ p ∈ a.primeFactors, (p:ℝ) := os_cast_eq_prod hprime ha
  have hcastb : (b:ℝ) = ∏ p ∈ b.primeFactors, (p:ℝ) := os_cast_eq_prod hprime hb
  have hℓ : (0:ℝ) < (b:ℝ) - (a:ℝ) := by
    have h1 : (a:ℝ) < (b:ℝ) := by exact_mod_cast hab
    linarith
  have hconst := F_const_of_esymm_eq (x₀ := x₀) (s := b.primeFactors) (s' := a.primeFactors)
    (fun p hp => (hwin p (hv hp)).le) (fun p hp => (hwin p (hu hp)).le)
    hcardeq.symm
    (fun j hj => (heq j (by omega)).symm)
  have heqF : ∀ x : ℝ,
      ∏ c ∈ b.primeFactors.image (fun p : ℕ => -(p:ℝ)), (x - c)
      = (∏ c ∈ a.primeFactors.image (fun p : ℕ => -(p:ℝ)), (x - c)) + ((b:ℝ) - (a:ℝ)) := by
    intro x
    rw [os_prod_neg_image, os_prod_neg_image, hconst x, ← hcasta, ← hcastb]
  obtain ⟨hltmax, hgap⟩ := F_const_gap (hvne.image _) (hune.image _) hℓ heqF
  rw [os_max_image_neg hvne, os_max_image_neg hune] at hltmax hgap
  -- the minimum of `b`'s factors exceeds the minimum of `a`'s by more than `N`
  have hminlt : a.primeFactors.min' hune < b.primeFactors.min' hvne := by
    have h1 : ((a.primeFactors.min' hune : ℕ) : ℝ) < ((b.primeFactors.min' hvne : ℕ):ℝ) := by
      linarith
    exact_mod_cast h1
  have hminB_a : a.primeFactors.min' hune ∈ B := hu (a.primeFactors.min'_mem hune)
  have hminB_b : b.primeFactors.min' hvne ∈ B := hv (b.primeFactors.min'_mem hvne)
  have hsepmin := hsep _ hminB_a _ hminB_b hminlt
  have hgapmin : (N:ℝ) + 1 ≤ ((b.primeFactors.min' hvne : ℕ):ℝ)
      - ((a.primeFactors.min' hune : ℕ):ℝ) := by
    have h1 : a.primeFactors.min' hune + (N+1) ≤ b.primeFactors.min' hvne := by omega
    have h2 : ((a.primeFactors.min' hune : ℕ):ℝ) + ((N:ℝ)+1)
        ≤ ((b.primeFactors.min' hvne : ℕ):ℝ) := by exact_mod_cast h1
    linarith
  -- identify the product in `hgap` with `os_D b.primeFactors`
  have hprodD : ∏ c ∈ (b.primeFactors.image (fun p : ℕ => -(p:ℝ))).erase
        (-((b.primeFactors.min' hvne : ℕ):ℝ)),
        (-((b.primeFactors.min' hvne : ℕ):ℝ) - c) = os_D b.primeFactors := by
    have h1 : (b.primeFactors.image (fun p : ℕ => -(p:ℝ))).erase
        (-((b.primeFactors.min' hvne : ℕ):ℝ))
        = (b.primeFactors.erase (b.primeFactors.min' hvne)).image (fun p : ℕ => -(p:ℝ)) :=
      (Finset.image_erase os_neg_injective b.primeFactors (b.primeFactors.min' hvne)).symm
    rw [h1, os_prod_neg_image]
    have hosmin : os_min b.primeFactors = b.primeFactors.min' hvne := os_min_eq hvne
    unfold os_D
    rw [hosmin]
    exact Finset.prod_congr rfl fun p _ => by ring
  rw [hprodD] at hgap
  have hDnn : 0 ≤ os_D b.primeFactors := (os_D_pos hsep hv hvne).le
  calc (N:ℝ) * os_D b.primeFactors
      ≤ (-((a.primeFactors.min' hune : ℕ):ℝ) - -((b.primeFactors.min' hvne : ℕ):ℝ))
          * os_D b.primeFactors := by
        refine mul_le_mul_of_nonneg_right ?_ hDnn
        linarith
    _ ≤ (b:ℝ) - (a:ℝ) := hgap

/-! ### Class 2, sub-case (ii): the weighted divisor sum -/

lemma os_gsum_le {B : Finset ℕ} {N K : ℕ} (hprime : ∀ p ∈ B, p.Prime)
    (hcard : B.card = K) (hN : 1 ≤ N)
    (hsep : ∀ p ∈ B, ∀ q ∈ B, p < q → N < q - p)
    (hlogK : 2 * (1 + Real.log K) ≤ N) :
    ∑ b ∈ (∏ p ∈ B, p).divisors,
        (if 2 ≤ b.primeFactors.card then ((N:ℝ) * os_D b.primeFactors)⁻¹ else 0)
      ≤ 2*K*(1 + Real.log K)/N^2 := by
  classical
  have hN0 : (0:ℝ) < N := by exact_mod_cast hN
  have hNne : (N:ℝ) ≠ 0 := hN0.ne'
  have hq0 : (0:ℝ) ≤ (1 + Real.log K)/N :=
    div_nonneg (one_add_log_natCast_nonneg K) (Nat.cast_nonneg N)
  have hq2 : (1 + Real.log K)/N ≤ 1/2 := by
    rw [div_le_div_iff₀ hN0 (by norm_num : (0:ℝ) < 2)]
    linarith
  have hstep1 : ∑ b ∈ (∏ p ∈ B, p).divisors,
      (if 2 ≤ b.primeFactors.card then ((N:ℝ) * os_D b.primeFactors)⁻¹ else 0)
      = ∑ v ∈ B.powerset.filter (fun v => 2 ≤ v.card), ((N:ℝ) * os_D v)⁻¹ := by
    rw [divisors_prodPrimes hprime,
      Finset.sum_image (f := fun b => if 2 ≤ b.primeFactors.card
        then ((N:ℝ) * os_D b.primeFactors)⁻¹ else 0) (prodPrimes_injOn hprime),
      Finset.sum_filter]
    refine Finset.sum_congr rfl fun v hv => ?_
    rw [primeFactors_prodPrimes fun p hp => hprime p (Finset.mem_powerset.mp hv hp)]
  rw [hstep1]
  have hmaps : ∀ v ∈ B.powerset.filter (fun v => 2 ≤ v.card),
      v.card ∈ Finset.Icc 2 K := by
    intro v hv
    obtain ⟨h1, h2⟩ := Finset.mem_filter.mp hv
    refine Finset.mem_Icc.mpr ⟨h2, ?_⟩
    rw [← hcard]
    exact Finset.card_le_card (Finset.mem_powerset.mp h1)
  rw [← Finset.sum_fiberwise_of_maps_to hmaps (fun v => ((N:ℝ) * os_D v)⁻¹)]
  have hperk : ∀ k ∈ Finset.Icc 2 K,
      ∑ v ∈ (B.powerset.filter (fun v => 2 ≤ v.card)).filter (fun v => v.card = k),
        ((N:ℝ) * os_D v)⁻¹
      ≤ (N:ℝ)⁻¹ * ((K:ℝ) * ((1 + Real.log K) / N) ^ (k - 1)) := by
    intro k hk
    obtain ⟨hk2, hkK⟩ := Finset.mem_Icc.mp hk
    have hDpos : ∀ v ∈ B.powerset.filter (fun v => v.card = k), (0:ℝ) < os_D v := by
      intro v hv
      obtain ⟨h1, h2⟩ := Finset.mem_filter.mp hv
      exact os_D_pos hsep (Finset.mem_powerset.mp h1)
        (Finset.card_pos.mp (by omega))
    calc ∑ v ∈ (B.powerset.filter (fun v => 2 ≤ v.card)).filter (fun v => v.card = k),
          ((N:ℝ) * os_D v)⁻¹
        ≤ ∑ v ∈ B.powerset.filter (fun v => v.card = k), ((N:ℝ) * os_D v)⁻¹ := by
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
          · intro v hv
            obtain ⟨h1, h2⟩ := Finset.mem_filter.mp hv
            exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp h1).1, h2⟩
          · intro v hv _
            have hD := hDpos v hv
            positivity
      _ = (N:ℝ)⁻¹ * ∑ v ∈ B.powerset.filter (fun v => v.card = k), (os_D v)⁻¹ := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun v hv => by rw [mul_inv]
      _ ≤ (N:ℝ)⁻¹ * ((K:ℝ) * ((1 + Real.log K) / N) ^ (k - 1)) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact os_sum_D_inv_le hcard hsep hN (by omega)
  calc ∑ k ∈ Finset.Icc 2 K,
        ∑ v ∈ (B.powerset.filter (fun v => 2 ≤ v.card)).filter (fun v => v.card = k),
          ((N:ℝ) * os_D v)⁻¹
      ≤ ∑ k ∈ Finset.Icc 2 K, (N:ℝ)⁻¹ * ((K:ℝ) * ((1 + Real.log K)/N) ^ (k-1)) :=
        Finset.sum_le_sum hperk
    _ = (N:ℝ)⁻¹ * (K:ℝ) * ∑ k ∈ Finset.Icc 2 K, ((1 + Real.log K)/N) ^ (k-1) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun k _ => by ring
    _ ≤ (N:ℝ)⁻¹ * (K:ℝ) * (2 * ((1 + Real.log K)/N)) :=
        mul_le_mul_of_nonneg_left (os_geom_tail_le hq0 hq2 K) (by positivity)
    _ = 2*K*(1 + Real.log K)/N^2 := by
        field_simp

/-- Class 2, sub-case (ii): consecutive same-`ω ≥ 2` pairs with all shifted symmetric
sums equal. -/
lemma os_sameCard_ii_le {B : Finset ℕ} {x₀ H N K : ℕ}
    (hprime : ∀ p ∈ B, p.Prime) (hcard : B.card = K) (hN : 1 ≤ N)
    (hwin : ∀ p ∈ B, x₀ < p ∧ p ≤ x₀ + H)
    (hsep : ∀ p ∈ B, ∀ q ∈ B, p < q → N < q - p)
    (hlogK : 2 * (1 + Real.log K) ≤ N) :
    pairSumOn ((∏ p ∈ B, p).divisors)
        (fun a b => 2 ≤ a.primeFactors.card ∧ a.primeFactors.card = b.primeFactors.card ∧
          IsConsecutive ((∏ p ∈ B, p).divisors) a b ∧
          ∀ j, j < a.primeFactors.card →
            esymmShift x₀ a.primeFactors j = esymmShift x₀ b.primeFactors j)
      ≤ 2*K*(1 + Real.log K)/N^2 := by
  classical
  have hN0 : (0:ℝ) < N := by exact_mod_cast hN
  have hgnn : ∀ b ∈ (∏ p ∈ B, p).divisors,
      (0:ℝ) ≤ (if 2 ≤ b.primeFactors.card then ((N:ℝ) * os_D b.primeFactors)⁻¹ else 0) := by
    intro b hb
    split
    · rename_i h2
      have hD := os_D_pos hsep (os_primeFactors_subset hprime hb)
        (Finset.card_pos.mp (by omega))
      positivity
    · exact le_rfl
  refine le_trans (os_pairSumOn_le_of_forall fun S hS => ?_)
    (os_gsum_le hprime hcard hN hsep hlogK)
  have hterm : ∀ p ∈ S, invGap p.1 p.2
      ≤ (if 2 ≤ p.2.primeFactors.card then ((N:ℝ) * os_D p.2.primeFactors)⁻¹ else 0) := by
    intro p hp
    obtain ⟨ha, hb, hlt, h2, hceq, hcons, hall⟩ := hS p hp
    have hgap := os_const_gap_ge hprime (fun q hq => (hwin q hq).1) hsep
      ha hb hlt h2 hceq hall
    have hDpos := os_D_pos hsep (os_primeFactors_subset hprime hb)
      (Finset.card_pos.mp (by omega : 0 < p.2.primeFactors.card))
    have hND : (0:ℝ) < (N:ℝ) * os_D p.2.primeFactors := by positivity
    have h2b : 2 ≤ p.2.primeFactors.card := by omega
    rw [if_pos h2b]
    exact inv_anti₀ hND hgap
  have hinj : Set.InjOn (fun p : ℕ × ℕ => p.2) ↑S := by
    intro p hp p' hp' he
    have hp1 := hS p (Finset.mem_coe.mp hp)
    have hp'1 := hS p' (Finset.mem_coe.mp hp')
    have he' : p.2 = p'.2 := he
    obtain ⟨-, -, -, -, -, hcons, -⟩ := hp1
    obtain ⟨-, -, -, -, -, hcons', -⟩ := hp'1
    have h1 : p.1 = p'.1 := os_consec_pred_unique hcons (he' ▸ hcons')
    exact Prod.ext h1 he'
  calc ∑ p ∈ S, invGap p.1 p.2
      ≤ ∑ p ∈ S, (if 2 ≤ p.2.primeFactors.card
          then ((N:ℝ) * os_D p.2.primeFactors)⁻¹ else 0) := Finset.sum_le_sum hterm
    _ = ∑ b ∈ S.image (fun p : ℕ × ℕ => p.2), (if 2 ≤ b.primeFactors.card
          then ((N:ℝ) * os_D b.primeFactors)⁻¹ else 0) :=
        (Finset.sum_image (f := fun b : ℕ => if 2 ≤ b.primeFactors.card
          then ((N:ℝ) * os_D b.primeFactors)⁻¹ else 0) hinj).symm
    _ ≤ ∑ b ∈ (∏ p ∈ B, p).divisors, (if 2 ≤ b.primeFactors.card
          then ((N:ℝ) * os_D b.primeFactors)⁻¹ else 0) := by
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun b hb _ => hgnn b hb
        intro b hb
        obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hb
        exact (hS p hp).2.1

/-- Class 2, sub-case (i): some shifted symmetric sum differs, so the gap is at
least `x₀/2`. -/
lemma os_sameCard_i_le {B : Finset ℕ} {x₀ H K : ℕ}
    (hprime : ∀ p ∈ B, p.Prime) (hcard : B.card = K) (hH : 1 ≤ H)
    (hwin : ∀ p ∈ B, x₀ < p ∧ p ≤ x₀ + H)
    (hbig : 8 * (2*H)^(K+1) ≤ x₀) :
    pairSumOn ((∏ p ∈ B, p).divisors)
        (fun a b => 2 ≤ a.primeFactors.card ∧ a.primeFactors.card = b.primeFactors.card ∧
          IsConsecutive ((∏ p ∈ B, p).divisors) a b ∧
          ∃ j, j < a.primeFactors.card ∧
            esymmShift x₀ a.primeFactors j ≠ esymmShift x₀ b.primeFactors j)
      ≤ 2*(4:ℝ)^K/x₀ := by
  classical
  have h2H1 : 1 ≤ (2*H)^(K+1) := Nat.one_le_pow _ _ (by omega)
  have hx₀8 : 8 ≤ x₀ := by omega
  have hx0R : (0:ℝ) < (x₀:ℝ) := by exact_mod_cast (by omega : 0 < x₀)
  refine os_pairSumOn_le_of_forall fun S hS => ?_
  have hterm : ∀ p ∈ S, invGap p.1 p.2 ≤ 2/(x₀:ℝ) := by
    intro p hp
    obtain ⟨ha, hb, hlt, h2, hceq, hcons, hj⟩ := hS p hp
    have hKa : p.1.primeFactors.card ≤ K := by
      rw [← hcard]
      exact Finset.card_le_card (os_primeFactors_subset hprime ha)
    have hga := F_nonconst_gap (x₀ := x₀) (H := H) (K := K)
      (fun q hq => hwin q (os_primeFactors_subset hprime ha hq))
      (fun q hq => hwin q (os_primeFactors_subset hprime hb hq))
      hceq hKa hH hbig hj
    rw [← os_cast_eq_prod hprime ha, ← os_cast_eq_prod hprime hb] at hga
    have habR : (p.1:ℝ) < (p.2:ℝ) := by exact_mod_cast hlt
    rw [abs_sub_comm, abs_of_nonneg (by linarith)] at hga
    have hhalf : (0:ℝ) < (x₀:ℝ)/2 := by linarith
    calc invGap p.1 p.2 ≤ ((x₀:ℝ)/2)⁻¹ := inv_anti₀ hhalf hga
      _ = 2/(x₀:ℝ) := by rw [inv_div]
  have hsub : S ⊆ (∏ p ∈ B, p).divisors ×ˢ (∏ p ∈ B, p).divisors := by
    intro p hp
    exact Finset.mem_product.mpr ⟨(hS p hp).1, (hS p hp).2.1⟩
  have hScard : (S.card : ℝ) ≤ (2:ℝ)^K * (2:ℝ)^K := by
    have h1 : S.card ≤ ((∏ p ∈ B, p).divisors ×ˢ (∏ p ∈ B, p).divisors).card :=
      Finset.card_le_card hsub
    have h2 : ((∏ p ∈ B, p).divisors ×ˢ (∏ p ∈ B, p).divisors).card = 2^K * 2^K := by
      rw [Finset.card_product, card_divisors_prodPrimes hprime, hcard]
    rw [h2] at h1
    exact_mod_cast h1
  calc ∑ p ∈ S, invGap p.1 p.2 ≤ ∑ _p ∈ S, 2/(x₀:ℝ) := Finset.sum_le_sum hterm
    _ = (S.card : ℝ) * (2/(x₀:ℝ)) := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ((2:ℝ)^K * (2:ℝ)^K) * (2/(x₀:ℝ)) := by
        refine mul_le_mul_of_nonneg_right hScard (by positivity)
    _ = 2*(4:ℝ)^K/x₀ := by
        have h4 : (2:ℝ)^K * (2:ℝ)^K = (4:ℝ)^K := by
          rw [← mul_pow]
          norm_num
        rw [h4]
        ring

/-! ### Class 2: consecutive pairs with equal `ω ≥ 2` -/

theorem oneScale_sameCard_le {B : Finset ℕ} {x₀ H N K : ℕ}
    (hprime : ∀ p ∈ B, p.Prime) (hcard : B.card = K) (hK : 2 ≤ K) (hN : 1 ≤ N) (hH : 1 ≤ H)
    (hwin : ∀ p ∈ B, x₀ < p ∧ p ≤ x₀ + H)
    (hsep : ∀ p ∈ B, ∀ q ∈ B, p < q → N < q - p)
    (hbig : 8 * (2*H)^(K+1) ≤ x₀)
    (hlogK : 2 * (1 + Real.log K) ≤ N) :
    pairSumOn ((∏ p ∈ B, p).divisors)
        (fun a b => 2 ≤ a.primeFactors.card ∧ a.primeFactors.card = b.primeFactors.card ∧
                    IsConsecutive ((∏ p ∈ B, p).divisors) a b)
      ≤ 2*K*(1 + Real.log K)/N^2 + 2*(4:ℝ)^K/x₀ := by
  classical
  have hmono : pairSumOn ((∏ p ∈ B, p).divisors)
      (fun a b => 2 ≤ a.primeFactors.card ∧ a.primeFactors.card = b.primeFactors.card ∧
        IsConsecutive ((∏ p ∈ B, p).divisors) a b)
      ≤ pairSumOn ((∏ p ∈ B, p).divisors)
        (fun a b =>
          (2 ≤ a.primeFactors.card ∧ a.primeFactors.card = b.primeFactors.card ∧
            IsConsecutive ((∏ p ∈ B, p).divisors) a b ∧
            ∀ j, j < a.primeFactors.card →
              esymmShift x₀ a.primeFactors j = esymmShift x₀ b.primeFactors j) ∨
          (2 ≤ a.primeFactors.card ∧ a.primeFactors.card = b.primeFactors.card ∧
            IsConsecutive ((∏ p ∈ B, p).divisors) a b ∧
            ∃ j, j < a.primeFactors.card ∧
              esymmShift x₀ a.primeFactors j ≠ esymmShift x₀ b.primeFactors j)) := by
    refine pairSumOn_mono_pred fun a b _ _ _ hC => ?_
    obtain ⟨h2, hceq, hcons⟩ := hC
    by_cases hall : ∀ j, j < a.primeFactors.card →
        esymmShift x₀ a.primeFactors j = esymmShift x₀ b.primeFactors j
    · exact Or.inl ⟨h2, hceq, hcons, hall⟩
    · push_neg at hall
      obtain ⟨j, hj, hne⟩ := hall
      exact Or.inr ⟨h2, hceq, hcons, j, hj, hne⟩
  refine le_trans hmono (le_trans (pairSumOn_or_le _ _ _) ?_)
  exact add_le_add (os_sameCard_ii_le hprime hcard hN hwin hsep hlogK)
    (os_sameCard_i_le hprime hcard hH hwin hbig)

/-! ### The trichotomy glue: the full one-scale gap-sum bound -/

theorem oneScale_gapSum_le {B : Finset ℕ} {x₀ H N K : ℕ}
    (hprime : ∀ p ∈ B, p.Prime) (hcard : B.card = K) (hK : 2 ≤ K) (hN : 1 ≤ N) (hH : 1 ≤ H)
    (hwin : ∀ p ∈ B, x₀ < p ∧ p ≤ x₀ + H)
    (hsep : ∀ p ∈ B, ∀ q ∈ B, p < q → N < q - p)
    (hbig : 8 * (2*H)^(K+1) ≤ x₀) (hKH : 2*K*H ≤ x₀) (hx₀ : 4 ≤ x₀)
    (hlogK : 2 * (1 + Real.log K) ≤ N) :
    gapSum ((∏ p ∈ B, p).divisors)
      ≤ (K:ℝ)/N + (2*K*(1 + Real.log K)/N^2 + 2*(4:ℝ)^K/x₀) + (2:ℝ)^(K+3)*K/x₀ := by
  classical
  have hcover : ∀ a b, IsConsecutive ((∏ p ∈ B, p).divisors) a b →
      ((a ∈ B ∧ b ∈ B ∧ IsConsecutive ((∏ p ∈ B, p).divisors) a b) ∨
       ((2 ≤ a.primeFactors.card ∧ a.primeFactors.card = b.primeFactors.card ∧
         IsConsecutive ((∏ p ∈ B, p).divisors) a b) ∨
        a.primeFactors.card ≠ b.primeFactors.card)) := by
    intro a b hcons
    have ha := hcons.1
    have hb := hcons.2.1
    have hab := hcons.2.2.1
    by_cases hceq : a.primeFactors.card = b.primeFactors.card
    · rcases Nat.lt_or_ge a.primeFactors.card 2 with hlt2 | hge2
      · have hcase : a.primeFactors.card = 0 ∨ a.primeFactors.card = 1 := by omega
        rcases hcase with h0 | h1
        · exfalso
          have ha1 : a = 1 := os_eq_one_of_card_zero hprime ha h0
          have hb1 : b = 1 := os_eq_one_of_card_zero hprime hb (by omega)
          omega
        · exact Or.inl ⟨os_mem_B_of_card_one hprime ha h1,
            os_mem_B_of_card_one hprime hb (by omega), hcons⟩
      · exact Or.inr (Or.inl ⟨hge2, hceq, hcons⟩)
    · exact Or.inr (Or.inr hceq)
  have h1 : gapSum ((∏ p ∈ B, p).divisors)
      ≤ (K:ℝ)/N + ((2*K*(1 + Real.log K)/N^2 + 2*(4:ℝ)^K/x₀) + (2:ℝ)^(K+3)*K/x₀) := by
    refine le_trans (gapSum_le_pairSumOn hcover) ?_
    refine le_trans (pairSumOn_or_le _ _ _) ?_
    refine add_le_add (oneScale_primePart_le hprime hcard hsep hN) ?_
    refine le_trans (pairSumOn_or_le _ _ _) ?_
    exact add_le_add
      (oneScale_sameCard_le hprime hcard hK hN hH hwin hsep hbig hlogK)
      (oneScale_diffCard_le hprime hcard hwin hKH hx₀ hH (by omega))
  linarith

end Erdos884
end

/-! Flattened from Erdos884/Selection884.lean. -/
section

/-!
# Erdős 884 — Lemma C: selection of well-separated primes in a short window

Exports `Erdos884.separated_primes_selection`: for suitable `ε` and all large `t`, and any
`2 ≤ K ≤ log t / log log t`, there are `K` primes in a window `(x₀, x₀ + H]` with
`t ≤ x₀ ≤ 8t`, `H ≤ 7K log t`, pairwise gaps exceeding `N ≍ ε log t`.

Route: Chebyshev (`primesBetween_lower` at `t+1`) provides `≳ (3/2) t / log t` primes in
`(⌊t+1⌋₊, ⌊8t⌋₊]`; the pair-sieve bound (`prime_pairs_bound`) shows at most `t/(8 log t)`
of them are within `N` of a smaller one (greedy filtering, no recursion); pigeonholing the
survivors over windows of length `H` produces a window containing `K` of them.
-/

namespace Erdos884

/-! ## Numeric helper: `100 (log t)² ≤ t` for `t ≥ 2 560 000` -/

lemma sel_log_sq_le {t : ℝ} (ht : 2560000 ≤ t) : 100 * (Real.log t)^2 ≤ t := by
  have ht1 : (1:ℝ) ≤ t := by linarith
  have ht0 : (0:ℝ) < t := by linarith
  have hs0 : (0:ℝ) ≤ Real.sqrt t := Real.sqrt_nonneg t
  have hs_pos : (0:ℝ) < Real.sqrt t := Real.sqrt_pos.mpr ht0
  have hu_pos : (0:ℝ) < Real.sqrt (Real.sqrt t) := Real.sqrt_pos.mpr hs_pos
  have h1 : Real.log t = 4 * Real.log (Real.sqrt (Real.sqrt t)) := by
    rw [Real.log_sqrt hs0, Real.log_sqrt ht0.le]; ring
  have h2 : Real.log (Real.sqrt (Real.sqrt t)) ≤ Real.sqrt (Real.sqrt t) :=
    (Real.log_le_sub_one_of_pos hu_pos).trans (by linarith)
  have h3 : Real.log t ≤ 4 * Real.sqrt (Real.sqrt t) := by rw [h1]; linarith
  have hlog0 : 0 ≤ Real.log t := Real.log_nonneg ht1
  have h4 : (Real.log t)^2 ≤ 16 * Real.sqrt t := by
    calc (Real.log t)^2 ≤ (4 * Real.sqrt (Real.sqrt t))^2 := pow_le_pow_left₀ hlog0 h3 2
      _ = 16 * (Real.sqrt (Real.sqrt t))^2 := by ring
      _ = 16 * Real.sqrt t := by rw [Real.sq_sqrt hs0]
  have h5 : (1600:ℝ) ≤ Real.sqrt t := by
    rw [show (1600:ℝ) = Real.sqrt (1600^2) from (Real.sqrt_sq (by norm_num)).symm]
    exact Real.sqrt_le_sqrt (by norm_num; linarith)
  calc 100 * (Real.log t)^2 ≤ 100 * (16 * Real.sqrt t) := by linarith
    _ = 1600 * Real.sqrt t := by ring
    _ ≤ Real.sqrt t * Real.sqrt t := mul_le_mul_of_nonneg_right h5 hs0
    _ = t := Real.mul_self_sqrt ht0.le

/-! ## Window arithmetic -/

lemma sel_window {b H p w : ℕ} (hH : 0 < H) (hbp : b < p)
    (hw : (p - b - 1) / H = w) : b + w * H < p ∧ p ≤ b + w * H + H := by
  have h1 : H * ((p - b - 1) / H) + (p - b - 1) % H = p - b - 1 := Nat.div_add_mod _ _
  have h2 : (p - b - 1) % H < H := Nat.mod_lt _ hH
  rw [hw] at h1
  have h3 : w * H = H * w := Nat.mul_comm w H
  set m := (p - b - 1) % H with hm
  set z := H * w with hz
  rw [h3]
  omega

/-! ## The greedy separated subfamily -/

/-- From any finite set `P ⊆ ℕ`, one can extract a subset `kept` whose pairwise gaps all
exceed `N`, discarding at most `S.card` elements, where `S` is any set of pairs containing
all `(q, p)` with `p, q ∈ P`, `q < p`, `p - q ≤ N`. -/
lemma sel_greedy (P : Finset ℕ) (N : ℕ) (S : Finset (ℕ × ℕ))
    (hS : ∀ p ∈ P, ∀ q ∈ P, q < p → p - q ≤ N → (q, p) ∈ S) :
    ∃ kept : Finset ℕ, kept ⊆ P ∧
      (∀ p ∈ kept, ∀ q ∈ kept, p < q → N < q - p) ∧
      P.card ≤ kept.card + S.card := by
  classical
  set kept := P.filter (fun p => ∀ q ∈ P, ¬(q < p ∧ p - q ≤ N)) with hkeptdef
  refine ⟨kept, Finset.filter_subset _ _, ?_, ?_⟩
  · intro p hp q hq hpq
    rw [hkeptdef, Finset.mem_filter] at hp hq
    by_contra hle
    push_neg at hle
    exact hq.2 p hp.1 ⟨hpq, hle⟩
  · have hD : ∀ p ∈ P \ kept, ∃ q, q ∈ P ∧ q < p ∧ p - q ≤ N := by
      intro p hp
      rw [Finset.mem_sdiff, hkeptdef, Finset.mem_filter] at hp
      obtain ⟨hpP, hpk⟩ := hp
      push_neg at hpk
      obtain ⟨q, hqP, hql, hqN⟩ := hpk hpP
      exact ⟨q, hqP, hql, hqN⟩
    have key : (P \ kept).card ≤ S.card := by
      apply Finset.card_le_card_of_injOn
        (fun p => ((if h : ∃ q, q ∈ P ∧ q < p ∧ p - q ≤ N then h.choose else 0), p))
      · intro p hp
        rw [Finset.mem_coe] at hp
        obtain ⟨q, hqP, hql, hqN⟩ := hD p hp
        have hex : ∃ q, q ∈ P ∧ q < p ∧ p - q ≤ N := ⟨q, hqP, hql, hqN⟩
        simp only [dif_pos hex]
        obtain ⟨h1, h2, h3⟩ := hex.choose_spec
        exact hS p (Finset.mem_sdiff.mp hp).1 _ h1 h2 h3
      · intro a _ b _ hab
        simpa using congrArg Prod.snd hab
    have hsplit : (P \ kept).card + kept.card = P.card :=
      Finset.card_sdiff_add_card_eq_card (Finset.filter_subset _ _)
    omega

/-! ## The selection theorem -/

theorem separated_primes_selection :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 ∧ ∃ T_C : ℝ, 3 ≤ T_C ∧ ∀ t : ℝ, T_C ≤ t → ∀ K : ℕ, 2 ≤ K →
      (K : ℝ) ≤ Real.log t / Real.log (Real.log t) →
      ∃ (B : Finset ℕ) (x₀ N H : ℕ),
        (∀ p ∈ B, Nat.Prime p) ∧ B.card = K ∧
        (t ≤ (x₀:ℝ)) ∧ ((x₀:ℝ) ≤ 8*t) ∧
        (∀ p ∈ B, x₀ < p ∧ p ≤ x₀ + H) ∧
        (∀ p ∈ B, ∀ q ∈ B, p < q → N < q - p) ∧
        (ε * Real.log t ≤ (N:ℝ)) ∧ ((N:ℝ) ≤ Real.log t) ∧ 1 ≤ N ∧
        ((H:ℝ) ≤ 7 * K * Real.log t) ∧ 1 ≤ H ∧ ((x₀:ℝ) + H ≤ 9*t) := by
  classical
  obtain ⟨C_B, hCB1, T_B, hTB3, hPB⟩ := prime_pairs_bound
  obtain ⟨T_A, hTA3, hCheb⟩ := primesBetween_lower
  have hCB0 : (0:ℝ) < C_B := by linarith
  set ε₀ : ℝ := min (1/(8*C_B)) 1 with hε₀def
  have hε₀pos : 0 < ε₀ := lt_min (by positivity) one_pos
  have hε₀le1 : ε₀ ≤ 1 := min_le_right _ _
  have hε₀CB : C_B * ε₀ ≤ 1/8 := by
    have h1 : ε₀ ≤ 1/(8*C_B) := min_le_left _ _
    calc C_B * ε₀ ≤ C_B * (1/(8*C_B)) := by gcongr
      _ = 1/8 := by field_simp
  refine ⟨ε₀/2, by positivity, by linarith,
    max (max T_A T_B) (max (Real.exp (max 3 (2/ε₀))) 2560000), ?_, ?_⟩
  · exact le_trans (by norm_num) (le_trans (le_max_right _ _) (le_max_right _ _))
  intro t ht K hK2 hKle
  -- unpack the threshold
  have hTA : T_A ≤ t := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) ht
  have hTB : T_B ≤ t := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) ht
  have hexp : Real.exp (max 3 (2/ε₀)) ≤ t :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) ht
  have h256 : (2560000:ℝ) ≤ t := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) ht
  have ht0 : (0:ℝ) < t := by linarith
  have ht1 : (1:ℝ) ≤ t := by linarith
  -- Chebyshev at t+1 (before introducing local abbreviations)
  have hcheb := hCheb (t+1) (by linarith)
  -- the log scale
  set L := Real.log t with hLdef
  have hLmax : max 3 (2/ε₀) ≤ L := by
    have h1 := Real.log_le_log (Real.exp_pos _) hexp
    rwa [Real.log_exp] at h1
  have hL3 : (3:ℝ) ≤ L := le_trans (le_max_left _ _) hLmax
  have hL0 : (0:ℝ) < L := by linarith
  have hε₀L : (2:ℝ) ≤ ε₀ * L := by
    have h1 : 2/ε₀ ≤ L := le_trans (le_max_right _ _) hLmax
    calc (2:ℝ) = ε₀ * (2/ε₀) := by field_simp
      _ ≤ ε₀ * L := by gcongr
  have h100L : 100 * L^2 ≤ t := sel_log_sq_le h256
  -- K ≤ L
  have hlogL1 : (1:ℝ) ≤ Real.log L := by
    rw [Real.le_log_iff_exp_le hL0]
    have h1 := Real.exp_one_lt_d9
    linarith
  have hKL : (K:ℝ) ≤ L := by
    have h1 : L / Real.log L ≤ L := div_le_self hL0.le hlogL1
    linarith [hKle]
  have hKR : (2:ℝ) ≤ (K:ℝ) := by exact_mod_cast hK2
  have hKposR : (0:ℝ) < (K:ℝ) := by linarith
  -- the separation scale N
  set N := ⌊ε₀ * L⌋₊ with hNdef
  have hN2 : 2 ≤ N := Nat.le_floor (by exact_mod_cast hε₀L)
  have hNleR : (N:ℝ) ≤ ε₀ * L := Nat.floor_le (mul_nonneg hε₀pos.le hL0.le)
  have hNleL : (N:ℝ) ≤ L := by nlinarith only [hNleR, hε₀le1, hL0]
  have hNge : (ε₀/2) * L ≤ (N:ℝ) := by
    have h1 : ε₀ * L < (N:ℝ) + 1 := Nat.lt_floor_add_one _
    linarith only [h1, hε₀L]
  -- the window length H
  set Hn := ⌈6 * (K:ℝ) * L⌉₊ with hHdef
  have h6KL : (0:ℝ) < 6 * (K:ℝ) * L := mul_pos (mul_pos (by norm_num) hKposR) hL0
  have hH1 : 1 ≤ Hn := Nat.ceil_pos.mpr h6KL
  have hHgeR : 6 * (K:ℝ) * L ≤ (Hn:ℝ) := Nat.le_ceil _
  have hHleR : (Hn:ℝ) ≤ 7 * (K:ℝ) * L := by
    have h1 : (Hn:ℝ) < 6 * (K:ℝ) * L + 1 := Nat.ceil_lt_add_one h6KL.le
    nlinarith only [h1, hKR, hL3]
  have hHt : (Hn:ℝ) ≤ t := by
    nlinarith only [hHleR, hKL, hL0, h100L, hKposR]
  -- the pair bound at (t, N)
  have hNL2 : (N:ℝ) ≤ Real.log t ^ 2 := by
    rw [← hLdef]
    nlinarith only [hNleL, hL3, hL0]
  have hbad := hPB t hTB N hN2 hNL2
  rw [← hLdef] at hbad
  -- interval endpoints
  set b := ⌊t+1⌋₊ with hbdef
  set U := ⌊8*t⌋₊ with hUdef
  set V := ⌊8*(t+1)⌋₊ with hVdef
  have hbt : t ≤ (b:ℝ) := by
    have h1 := Nat.lt_floor_add_one (t+1)
    rw [← hbdef] at h1
    linarith only [h1]
  have hU8t : (U:ℝ) ≤ 8*t := Nat.floor_le (by linarith)
  have hU8t' : 8*t < (U:ℝ) + 1 := by
    have h1 := Nat.lt_floor_add_one (8*t)
    rw [← hUdef] at h1
    exact h1
  have hbU : b ≤ U := Nat.floor_le_floor (by linarith)
  have hUV : U ≤ V := Nat.floor_le_floor (by linarith)
  have hV8 : (V:ℝ) ≤ 8*t + 8 := by
    have h1 : (V:ℝ) ≤ 8*(t+1) := Nat.floor_le (by linarith)
    linarith only [h1]
  have hVU8 : V ≤ U + 8 := by
    by_contra hcon
    push_neg at hcon
    have h1 : ((U + 9 : ℕ):ℝ) ≤ (V:ℝ) := by exact_mod_cast hcon
    push_cast at h1
    linarith only [h1, hV8, hU8t']
  -- the prime reservoirs
  set P := (Finset.Ioc b U).filter Nat.Prime with hPdef
  set P₀ := (Finset.Ioc b V).filter Nat.Prime with hP₀def
  -- Chebyshev lower bound for P₀, then P
  have hlog1 : (0:ℝ) < Real.log (t+1) := Real.log_pos (by linarith)
  have hlogt1 : Real.log (t+1) ≤ (4/3) * L := by
    have h1 : Real.log (t+1) ≤ Real.log (2*t) := Real.log_le_log (by linarith) (by linarith)
    have h2 : Real.log (2*t) = Real.log 2 + L := by
      rw [hLdef]; exact Real.log_mul (by norm_num) (by linarith)
    have h3 := Real.log_two_lt_d9
    linarith only [h1, h2, h3, hL3]
  have hchain : (3/2) * t / L ≤ 2*(t+1)/Real.log (t+1) := by
    rw [div_le_div_iff₀ hL0 hlog1]
    have hprod : t * Real.log (t+1) ≤ t * ((4/3)*L) :=
      mul_le_mul_of_nonneg_left hlogt1 ht0.le
    nlinarith only [hprod, hL0, ht0]
  have hP₀R : (3/2) * t / L ≤ (P₀.card : ℝ) := le_trans hchain hcheb
  have hsplitP : P₀.card ≤ P.card + 8 := by
    have hunion : Finset.Ioc b V = Finset.Ioc b U ∪ Finset.Ioc U V :=
      (Finset.Ioc_union_Ioc_eq_Ioc hbU hUV).symm
    have h1 : P₀ ⊆ P ∪ (Finset.Ioc U V).filter Nat.Prime := by
      rw [hP₀def, hPdef, hunion, Finset.filter_union]
    have h2 : P₀.card ≤ (P ∪ (Finset.Ioc U V).filter Nat.Prime).card :=
      Finset.card_le_card h1
    have h3 : (P ∪ (Finset.Ioc U V).filter Nat.Prime).card
        ≤ P.card + ((Finset.Ioc U V).filter Nat.Prime).card := Finset.card_union_le _ _
    have h4 : ((Finset.Ioc U V).filter Nat.Prime).card ≤ 8 := by
      calc ((Finset.Ioc U V).filter Nat.Prime).card ≤ (Finset.Ioc U V).card :=
            Finset.card_filter_le _ _
        _ = V - U := Nat.card_Ioc U V
        _ ≤ 8 := by omega
    omega
  have hPR : (3/2)*t/L - 8 ≤ (P.card : ℝ) := by
    have h1 : (P₀.card : ℝ) ≤ (P.card : ℝ) + 8 := by exact_mod_cast hsplitP
    linarith only [h1, hP₀R]
  -- membership of close pairs of P in the sieve-counted pair set
  have h9t : U ≤ ⌊9*t⌋₊ := Nat.floor_le_floor (by linarith)
  have hSmem : ∀ p ∈ P, ∀ q ∈ P, q < p → p - q ≤ N →
      (q, p) ∈ (Finset.Icc 1 ⌊9*t⌋₊ ×ˢ Finset.Icc 1 ⌊9*t⌋₊).filter
        (fun pq => Nat.Prime pq.1 ∧ Nat.Prime pq.2 ∧ pq.1 < pq.2 ∧ pq.2 - pq.1 ≤ N) := by
    intro p hp q hq hqp hgap
    rw [hPdef, Finset.mem_filter, Finset.mem_Ioc] at hp hq
    rw [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc]
    exact ⟨⟨⟨hq.2.one_lt.le, le_trans hq.1.2 h9t⟩, ⟨hp.2.one_lt.le, le_trans hp.1.2 h9t⟩⟩,
      hq.2, hp.2, hqp, hgap⟩
  -- greedy extraction of an N-separated subfamily
  obtain ⟨kept, hkP, hsep, hcard⟩ := sel_greedy P N _ hSmem
  have hcardR := (Nat.cast_le (α := ℝ)).mpr hcard
  push_cast at hcardR
  -- the kept family is large
  have hkeptR : (11/8)*t/L - 8 ≤ (kept.card : ℝ) := by
    have h1 : C_B * (N:ℝ) ≤ L/8 := by
      nlinarith only [hNleR, hε₀CB, hL0, hCB0]
    have hL2pos : (0:ℝ) < L^2 := pow_pos hL0 2
    have hL8pos : (0:ℝ) < 8*L := by linarith only [hL0]
    have h4 : C_B * (N:ℝ) * t / L^2 ≤ t / (8*L) := by
      rw [div_le_div_iff₀ hL2pos hL8pos]
      have hint : (0:ℝ) ≤ (L/8 - C_B * (N:ℝ)) * t * L :=
        mul_nonneg (mul_nonneg (sub_nonneg.mpr h1) ht0.le) hL0.le
      nlinarith only [hint]
    have h7 : (3/2)*t/L - t/(8*L) = (11/8)*t/L := by ring
    linarith only [hcardR, hbad, hPR, h4, h7]
  -- windows of length Hn
  set W := (U - b)/Hn + 1 with hWdef
  have hmaps : ∀ p ∈ kept, (p - b - 1)/Hn ∈ Finset.range W := by
    intro p hp
    have hpP := hkP hp
    rw [hPdef, Finset.mem_filter, Finset.mem_Ioc] at hpP
    rw [Finset.mem_range, hWdef]
    have h1 : p - b - 1 ≤ U - b := by omega
    exact Nat.lt_succ_of_le (Nat.div_le_div_right h1)
  have hWK : W * K ≤ kept.card := by
    have hHnpos : (0:ℝ) < (Hn:ℝ) := by exact_mod_cast hH1
    have hWR : (W:ℝ) ≤ 7*t/(Hn:ℝ) + 1 := by
      rw [hWdef]
      push_cast
      have h1 : ((U - b : ℕ):ℝ) ≤ 7*t := by
        rw [Nat.cast_sub hbU]
        linarith only [hU8t, hbt]
      have h2 : (((U - b)/Hn : ℕ):ℝ) ≤ ((U - b : ℕ):ℝ)/(Hn:ℝ) := Nat.cast_div_le
      have h3 : ((U - b : ℕ):ℝ)/(Hn:ℝ) ≤ 7*t/(Hn:ℝ) := by gcongr
      linarith only [h2, h3]
    have h6L : (0:ℝ) < 6*L := by linarith only [hL0]
    have hdK : 7*t/(Hn:ℝ)*(K:ℝ) ≤ 7*t/(6*L) := by
      rw [div_mul_eq_mul_div, div_le_div_iff₀ hHnpos h6L]
      have hmul := mul_le_mul_of_nonneg_left hHgeR (show (0:ℝ) ≤ 7*t by linarith only [ht0])
      nlinarith only [hmul]
    have hq : 100*L ≤ t/L := by
      rw [le_div_iff₀ hL0]
      nlinarith only [h100L]
    have hnum : 7*t/(6*L) + L ≤ (11/8)*t/L - 8 := by
      have h30 : 7*t/(6*L) = (7/6)*(t/L) := by ring
      have h31 : (11/8)*t/L = (11/8)*(t/L) := by ring
      linarith only [hq, hL3, h30, h31]
    have hcastWK : (W:ℝ) * (K:ℝ) ≤ (kept.card:ℝ) := by
      calc (W:ℝ)*(K:ℝ) ≤ (7*t/(Hn:ℝ) + 1)*(K:ℝ) :=
            mul_le_mul_of_nonneg_right hWR hKposR.le
        _ = 7*t/(Hn:ℝ)*(K:ℝ) + (K:ℝ) := by ring
        _ ≤ 7*t/(6*L) + (K:ℝ) := by linarith only [hdK]
        _ ≤ 7*t/(6*L) + L := by linarith only [hKL]
        _ ≤ (11/8)*t/L - 8 := hnum
        _ ≤ (kept.card:ℝ) := hkeptR
    exact_mod_cast hcastWK
  -- pigeonhole: some window holds K of the kept primes
  have hW1 : 1 ≤ W := by
    rw [hWdef]
    exact Nat.le_add_left 1 _
  have hne : (Finset.range W).Nonempty := ⟨0, Finset.mem_range.mpr hW1⟩
  obtain ⟨w, hwW, hfib⟩ := Finset.exists_le_card_fiber_of_mul_le_card_of_maps_to
    hmaps hne (by rwa [Finset.card_range])
  obtain ⟨B, hBsub, hBcard⟩ := Finset.exists_subset_card_eq hfib
  have hBk : ∀ x ∈ B, x ∈ kept := fun x hx => (Finset.mem_filter.mp (hBsub hx)).1
  have hBw : ∀ x ∈ B, (x - b - 1)/Hn = w := fun x hx => (Finset.mem_filter.mp (hBsub hx)).2
  have hBP : ∀ x ∈ B, x ∈ P := fun x hx => hkP (hBk x hx)
  -- the window start
  have hwlt : w < W := Finset.mem_range.mp hwW
  have hx₀U : b + w * Hn ≤ U := by
    have hwle : w ≤ (U - b)/Hn := by
      rw [hWdef] at hwlt
      exact Nat.lt_succ_iff.mp hwlt
    calc b + w * Hn ≤ b + ((U - b)/Hn) * Hn :=
          Nat.add_le_add_left (Nat.mul_le_mul_right _ hwle) b
      _ ≤ b + (U - b) := Nat.add_le_add_left (Nat.div_mul_le_self _ _) b
      _ = U := Nat.add_sub_cancel' hbU
  have hx₀R : ((b + w * Hn : ℕ):ℝ) ≤ 8*t := by
    have h1 : ((b + w * Hn : ℕ):ℝ) ≤ (U:ℝ) := by exact_mod_cast hx₀U
    linarith only [h1, hU8t]
  -- assemble
  refine ⟨B, b + w * Hn, N, Hn, ?_, hBcard, ?_, hx₀R, ?_, ?_, hNge, hNleL, by omega, hHleR,
    hH1, ?_⟩
  · intro p hp
    have h1 := hBP p hp
    rw [hPdef, Finset.mem_filter] at h1
    exact h1.2
  · push_cast
    have h1 : (0:ℝ) ≤ (w:ℝ) * (Hn:ℝ) := by positivity
    linarith only [h1, hbt]
  · intro p hp
    have h1 := hBP p hp
    rw [hPdef, Finset.mem_filter, Finset.mem_Ioc] at h1
    exact sel_window (by omega) h1.1.1 (hBw p hp)
  · intro p hp q hq hpq
    exact hsep p (hBk p hp) q (hBk q hq) hpq
  · push_cast
    push_cast at hx₀R
    linarith only [hx₀R, hHt]

end Erdos884

end

/-! Flattened from Erdos884/ScaleStep884.lean. -/
section

/-!
# Erdős 884 — the incremental multiscale step (`ScaleStep884`)

For coprime `n` and `m := ∏ p ∈ B, p` (a fresh window of `K` primes, all exceeding
everything about `n`), we bound `gapSum ((n*m).divisors)` by classifying consecutive
divisor pairs `(d₁, d₂)` via their coprime components `d = gcd d n * gcd d m`:

* (C1) equal `m`-component: projects to a consecutive pair of `n.divisors`;
* (C2) equal `n`-component: projects to a consecutive pair of `m.divisors`
  (handled by `oneScale_gapSum_le`);
* (C3) both components differ: the gap is at least `δ/4` of the endpoint, where `δ`
  is the minimal log-gap of `n.divisors`.

Exports: `scaleStep_gapSum_le`, `exists_min_log_gap`, `sum_inv_divisors_mul`.
All internal helpers are prefixed `ss_`.
-/

namespace Erdos884

/-! ### Coprimality and the component decomposition of divisors of `n * m` -/

lemma ss_coprime_prod {n x₀ : ℕ} {B : Finset ℕ} (hn : n ≠ 0)
    (hprime : ∀ p ∈ B, p.Prime) (hwin : ∀ p ∈ B, x₀ < p) (hnx : n ≤ x₀) :
    n.Coprime (∏ p ∈ B, p) := by
  refine Nat.Coprime.prod_right fun p hp => ?_
  refine Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd (hprime p hp)).mpr ?_)
  intro hdvd
  have h1 : p ≤ n := Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hdvd
  have h2 := hwin p hp
  omega

lemma ss_decomp {n m : ℕ} (hcop : n.Coprime m) {d : ℕ} (hd : d ∈ (n * m).divisors) :
    d = d.gcd n * d.gcd m ∧ d.gcd n ∈ n.divisors ∧ d.gcd m ∈ m.divisors := by
  have hnm : n * m ≠ 0 := (Nat.mem_divisors.mp hd).2
  have hn : n ≠ 0 := fun h => hnm (by simp [h])
  have hm : m ≠ 0 := fun h => hnm (by simp [h])
  have hdvd : d ∣ n * m := (Nat.mem_divisors.mp hd).1
  refine ⟨?_, Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_right d n, hn⟩,
    Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_right d m, hm⟩⟩
  calc d = Nat.gcd d (n * m) := (Nat.gcd_eq_left hdvd).symm
    _ = d.gcd n * d.gcd m := Nat.Coprime.gcd_mul d hcop

lemma ss_comp_eq {n m : ℕ} (hcop : n.Coprime m) {e a : ℕ} (he : e ∣ n) (ha : a ∣ m) :
    (e * a).gcd n = e ∧ (e * a).gcd m = a := by
  constructor
  · have h1 : e ∣ Nat.gcd (e * a) n := Nat.dvd_gcd (dvd_mul_right e a) he
    have hga : Nat.Coprime (Nat.gcd (e * a) n) a :=
      Nat.Coprime.coprime_dvd_left (Nat.gcd_dvd_right _ _)
        (Nat.Coprime.coprime_dvd_right ha hcop)
    exact Nat.dvd_antisymm
      (Nat.Coprime.dvd_of_dvd_mul_right hga (Nat.gcd_dvd_left _ _)) h1
  · have h1 : a ∣ Nat.gcd (e * a) m := Nat.dvd_gcd (dvd_mul_left a e) ha
    have hge : Nat.Coprime (Nat.gcd (e * a) m) e :=
      Nat.Coprime.coprime_dvd_left (Nat.gcd_dvd_right _ _)
        (Nat.Coprime.coprime_dvd_right he hcop.symm)
    exact Nat.dvd_antisymm
      (Nat.Coprime.dvd_of_dvd_mul_left hge (Nat.gcd_dvd_left _ _)) h1

lemma ss_mul_mem {n m e a : ℕ} (he : e ∈ n.divisors) (ha : a ∈ m.divisors) :
    e * a ∈ (n * m).divisors :=
  Nat.mem_divisors.mpr
    ⟨mul_dvd_mul (Nat.mem_divisors.mp he).1 (Nat.mem_divisors.mp ha).1,
     mul_ne_zero (Nat.mem_divisors.mp he).2 (Nat.mem_divisors.mp ha).2⟩

/-- `invGap` scales when both endpoints are multiplied by the same factor. -/
lemma ss_invGap_mul (a u v : ℕ) : invGap (u * a) (v * a) = ((a:ℝ))⁻¹ * invGap u v := by
  unfold invGap
  push_cast
  rw [show (v:ℝ) * a - u * a = (a:ℝ) * ((v:ℝ) - u) by ring, mul_inv]

/-- `pairSumOn` as a sum over an explicitly filtered pair set (any decidability
instance). -/
lemma ss_pairSumOn_eq (A : Finset ℕ) (C : ℕ → ℕ → Prop)
    [DecidablePred fun q : ℕ × ℕ => q.1 < q.2 ∧ C q.1 q.2] :
    pairSumOn A C
      = ∑ q ∈ (A ×ˢ A).filter (fun q : ℕ × ℕ => q.1 < q.2 ∧ C q.1 q.2),
          invGap q.1 q.2 := by
  have memf : ∀ {q : ℕ × ℕ → Prop} {inst : DecidablePred q} {s : Finset (ℕ × ℕ)}
      {x : ℕ × ℕ}, x ∈ @Finset.filter _ q inst s ↔ x ∈ s ∧ q x := by
    intro q inst s x
    letI := inst
    exact Finset.mem_filter
  unfold pairSumOn
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext q
  rw [memf, memf]

/-! ### An elementary exponential inequality -/

lemma ss_half_le_one_sub_exp {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) :
    x/2 ≤ 1 - Real.exp (-x) := by
  have h2 : x + 1 ≤ Real.exp x := Real.add_one_le_exp x
  have h3 : Real.exp (-x) ≤ (1+x)⁻¹ := by
    rw [Real.exp_neg]
    exact inv_anti₀ (by linarith) (by linarith)
  have h4 : (1+x)⁻¹ ≤ 1 - x/2 := by
    rw [inv_le_iff_one_le_mul₀ (by linarith : (0:ℝ) < 1 + x)]
    nlinarith
  linarith

/-! ### The minimal log-gap of the divisors of `n` -/

theorem exists_min_log_gap (n : ℕ) (hn : n ≠ 0) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧
      ∀ d ∈ n.divisors, ∀ e ∈ n.divisors, d < e → δ ≤ Real.log e - Real.log d := by
  have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
  have hnR : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn1
  refine ⟨1/(2*(n:ℝ)), by positivity, ?_, ?_⟩
  · rw [div_le_one (by positivity)]
    linarith
  · intro d hd e he hlt
    have hd1 : 1 ≤ d := Nat.pos_of_mem_divisors hd
    have hdn : d ≤ n := Nat.le_of_dvd (Nat.pos_of_ne_zero hn) (Nat.mem_divisors.mp hd).1
    have hdR : (0:ℝ) < (d:ℝ) := by exact_mod_cast hd1
    have h1 : Real.log ((d:ℝ)+1) ≤ Real.log e := by
      apply Real.log_le_log (by linarith)
      have : d + 1 ≤ e := hlt
      exact_mod_cast this
    have h2 : Real.log ((d:ℝ)/((d:ℝ)+1)) ≤ (d:ℝ)/((d:ℝ)+1) - 1 :=
      Real.log_le_sub_one_of_pos (by positivity)
    have h3 : Real.log ((d:ℝ)/((d:ℝ)+1)) = Real.log d - Real.log ((d:ℝ)+1) :=
      Real.log_div (by positivity) (by positivity)
    have h4 : (d:ℝ)/((d:ℝ)+1) - 1 = -(1/((d:ℝ)+1)) := by
      field_simp
      ring
    have h5 : 1/((d:ℝ)+1) ≤ Real.log ((d:ℝ)+1) - Real.log d := by
      rw [h3, h4] at h2
      linarith
    have hdn' : (d:ℝ) + 1 ≤ 2*(n:ℝ) := by
      have hdR' : (d:ℝ) ≤ (n:ℝ) := by exact_mod_cast hdn
      linarith
    have h6 : 1/(2*(n:ℝ)) ≤ 1/((d:ℝ)+1) :=
      one_div_le_one_div_of_le (by positivity) hdn'
    calc 1/(2*(n:ℝ)) ≤ 1/((d:ℝ)+1) := h6
      _ ≤ Real.log ((d:ℝ)+1) - Real.log d := h5
      _ ≤ Real.log e - Real.log d := by linarith

/-! ### Multiplicativity of the sum of reciprocals of divisors -/

theorem sum_inv_divisors_mul {a b : ℕ} (h : a.Coprime b) (ha : a ≠ 0) (hb : b ≠ 0) :
    ∑ d ∈ (a*b).divisors, ((d:ℝ))⁻¹ =
      (∑ d ∈ a.divisors, ((d:ℝ))⁻¹) * (∑ d ∈ b.divisors, ((d:ℝ))⁻¹) := by
  calc ∑ d ∈ (a*b).divisors, ((d:ℝ))⁻¹
      = ∑ q ∈ a.divisors ×ˢ b.divisors, ((q.1:ℝ))⁻¹ * ((q.2:ℝ))⁻¹ := by
        refine Finset.sum_nbij' (i := fun d => (d.gcd a, d.gcd b))
          (j := fun q : ℕ × ℕ => q.1 * q.2) ?_ ?_ ?_ ?_ ?_
        · intro d hd
          obtain ⟨-, h1, h2⟩ := ss_decomp h hd
          exact Finset.mem_product.mpr ⟨h1, h2⟩
        · intro q hq
          have hq' := Finset.mem_product.mp hq
          exact ss_mul_mem hq'.1 hq'.2
        · intro d hd
          exact (ss_decomp h hd).1.symm
        · intro q hq
          have hq' := Finset.mem_product.mp hq
          have := ss_comp_eq h (Nat.mem_divisors.mp hq'.1).1 (Nat.mem_divisors.mp hq'.2).1
          exact Prod.ext this.1 this.2
        · intro d hd
          conv_lhs => rw [(ss_decomp h hd).1]
          push_cast
          rw [mul_inv]
    _ = ∑ i ∈ a.divisors, ∑ j ∈ b.divisors, ((i:ℝ))⁻¹ * ((j:ℝ))⁻¹ :=
        Finset.sum_product _ _ _
    _ = (∑ d ∈ a.divisors, ((d:ℝ))⁻¹) * (∑ d ∈ b.divisors, ((d:ℝ))⁻¹) := by
        rw [Finset.sum_mul_sum]

/-! ### Consecutive pairs with equal `m`-component project to consecutive pairs -/

/-- If a consecutive pair of `(n*m).divisors` has equal `m`-components, then the
`n`-components form a consecutive pair of `n.divisors`. -/
lemma ss_consec_proj {n m : ℕ} (hcop : n.Coprime m)
    {d₁ d₂ : ℕ} (hcons : IsConsecutive ((n * m).divisors) d₁ d₂)
    (haeq : d₁.gcd m = d₂.gcd m) :
    IsConsecutive n.divisors (d₁.gcd n) (d₂.gcd n) := by
  obtain ⟨hd₁, hd₂, hlt, hbet⟩ := hcons
  obtain ⟨heq₁, he₁, ha₁⟩ := ss_decomp hcop hd₁
  obtain ⟨heq₂, he₂, ha₂⟩ := ss_decomp hcop hd₂
  have hapos : 0 < d₁.gcd m := Nat.pos_of_mem_divisors ha₁
  have hlt' : d₁.gcd n < d₂.gcd n := by
    have h1 : d₁.gcd n * d₁.gcd m < d₂.gcd n * d₁.gcd m := by
      conv_rhs => rw [haeq]
      rw [← heq₁, ← heq₂]
      exact hlt
    exact Nat.lt_of_mul_lt_mul_right h1
  refine ⟨he₁, he₂, hlt', ?_⟩
  intro c hc hcc
  refine hbet (c * d₁.gcd m) (ss_mul_mem hc ha₁) ⟨?_, ?_⟩
  · calc d₁ = d₁.gcd n * d₁.gcd m := heq₁
      _ < c * d₁.gcd m := Nat.mul_lt_mul_of_pos_right hcc.1 hapos
  · calc c * d₁.gcd m < d₂.gcd n * d₁.gcd m := Nat.mul_lt_mul_of_pos_right hcc.2 hapos
      _ = d₂.gcd n * d₂.gcd m := by rw [haeq]
      _ = d₂ := heq₂.symm

/-! ### Class C1: equal `m`-component -/

/-- Consecutive pairs of `(n*m).divisors` with equal `m`-component are controlled by
`gapSum n.divisors` times the sum of inverse divisors of `m`. -/
lemma ss_C1_le {n m : ℕ} (hcop : n.Coprime m) :
    pairSumOn ((n * m).divisors)
        (fun d₁ d₂ => d₁.gcd m = d₂.gcd m ∧ IsConsecutive ((n * m).divisors) d₁ d₂)
      ≤ (∑ a ∈ m.divisors, ((a:ℝ))⁻¹) * gapSum n.divisors := by
  classical
  refine os_pairSumOn_le_of_forall fun S hS => ?_
  set CP := (n.divisors ×ˢ n.divisors).filter
      (fun q : ℕ × ℕ => q.1 < q.2 ∧ IsConsecutive n.divisors q.1 q.2) with hCP
  have hgap : gapSum n.divisors = ∑ q ∈ CP, invGap q.1 q.2 := by
    unfold gapSum
    exact ss_pairSumOn_eq n.divisors (IsConsecutive n.divisors)
  set φ : ℕ × ℕ → ℕ × (ℕ × ℕ) := fun p => (p.1.gcd m, (p.1.gcd n, p.2.gcd n)) with hφ
  have hterm : ∀ p ∈ S, invGap p.1 p.2
      = ((p.1.gcd m : ℝ))⁻¹ * invGap (p.1.gcd n) (p.2.gcd n) := by
    intro p hp
    obtain ⟨hd₁, hd₂, hlt, haeq, hcons⟩ := hS p hp
    obtain ⟨heq₁, -, -⟩ := ss_decomp hcop hd₁
    obtain ⟨heq₂, -, -⟩ := ss_decomp hcop hd₂
    conv_lhs => rw [heq₁, heq₂, ← haeq]
    exact ss_invGap_mul _ _ _
  have hinj : ∀ p ∈ S, ∀ p' ∈ S, φ p = φ p' → p = p' := by
    intro p hp p' hp' he
    obtain ⟨hd₁, hd₂, -, haeq, -⟩ := hS p hp
    obtain ⟨hd₁', hd₂', -, haeq', -⟩ := hS p' hp'
    have h1 : p.1.gcd m = p'.1.gcd m := congrArg Prod.fst he
    have h2 : p.1.gcd n = p'.1.gcd n := congrArg (fun x => x.2.1) he
    have h3 : p.2.gcd n = p'.2.gcd n := congrArg (fun x => x.2.2) he
    have e1 : p.1 = p'.1 := by
      rw [(ss_decomp hcop hd₁).1, (ss_decomp hcop hd₁').1, h1, h2]
    have e2 : p.2 = p'.2 := by
      rw [(ss_decomp hcop hd₂).1, (ss_decomp hcop hd₂').1, ← haeq, ← haeq', h1, h3]
    exact Prod.ext e1 e2
  have himg : ∀ p ∈ S, φ p ∈ m.divisors ×ˢ CP := by
    intro p hp
    obtain ⟨hd₁, hd₂, hlt, haeq, hcons⟩ := hS p hp
    have hproj := ss_consec_proj hcop hcons haeq
    refine Finset.mem_product.mpr ⟨(ss_decomp hcop hd₁).2.2, ?_⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hproj.1, hproj.2.1⟩,
      hproj.2.2.1, hproj⟩
  have hnn : ∀ y ∈ m.divisors ×ˢ CP, 0 ≤ ((y.1:ℝ))⁻¹ * invGap y.2.1 y.2.2 := by
    intro y hy
    have hy' := Finset.mem_product.mp hy
    have hq := Finset.mem_filter.mp hy'.2
    exact mul_nonneg (by positivity) (invGap_pos hq.2.1).le
  calc ∑ p ∈ S, invGap p.1 p.2
      = ∑ p ∈ S, ((p.1.gcd m : ℝ))⁻¹ * invGap (p.1.gcd n) (p.2.gcd n) :=
        Finset.sum_congr rfl hterm
    _ = ∑ y ∈ S.image φ, ((y.1:ℝ))⁻¹ * invGap y.2.1 y.2.2 :=
        (Finset.sum_image
          (f := fun y : ℕ × (ℕ × ℕ) => ((y.1:ℝ))⁻¹ * invGap y.2.1 y.2.2) hinj).symm
    _ ≤ ∑ y ∈ m.divisors ×ˢ CP, ((y.1:ℝ))⁻¹ * invGap y.2.1 y.2.2 := by
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun y hy _ => hnn y hy
        intro y hy
        obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hy
        exact himg p hp
    _ = (∑ a ∈ m.divisors, ((a:ℝ))⁻¹) * ∑ q ∈ CP, invGap q.1 q.2 := by
        rw [Finset.sum_mul_sum]
        exact Finset.sum_product _ _ _
    _ = (∑ a ∈ m.divisors, ((a:ℝ))⁻¹) * gapSum n.divisors := by rw [hgap]

/-! ### Nontrivial divisors of the prime product exceed the window base -/

lemma ss_x0_lt_of_ne_one {B : Finset ℕ} {x₀ : ℕ} (hprime : ∀ p ∈ B, p.Prime)
    (hwin : ∀ p ∈ B, x₀ < p) {a : ℕ}
    (ha : a ∈ (∏ p ∈ B, p).divisors) (ha1 : a ≠ 1) : x₀ < a := by
  have hpf : a.primeFactors ⊆ B := os_primeFactors_subset hprime ha
  have hane : a.primeFactors.Nonempty := by
    rw [Nat.nonempty_primeFactors]
    have := Nat.pos_of_mem_divisors ha
    omega
  obtain ⟨p, hp⟩ := hane
  have hpa : p ∣ a := Nat.dvd_of_mem_primeFactors hp
  have hple : p ≤ a := Nat.le_of_dvd (Nat.pos_of_mem_divisors ha) hpa
  have := hwin p (hpf hp)
  omega

/-! ### The log-ratio of two same-`ω` divisors of the prime product is small -/

lemma ss_log_ratio_le {B : Finset ℕ} {x₀ H K : ℕ} (hprime : ∀ p ∈ B, p.Prime)
    (hcard : B.card = K) (hwin : ∀ p ∈ B, x₀ < p ∧ p ≤ x₀ + H) (hx₀ : 0 < x₀)
    {u v : ℕ} (hu : u ∈ (∏ p ∈ B, p).divisors) (hv : v ∈ (∏ p ∈ B, p).divisors)
    (hk : u.primeFactors.card = v.primeFactors.card) :
    Real.log v - Real.log u ≤ (K:ℝ) * H / x₀ := by
  have hx0R : (0:ℝ) < (x₀:ℝ) := by exact_mod_cast hx₀
  have hkK : u.primeFactors.card ≤ K := by
    rw [← hcard]
    exact Finset.card_le_card (os_primeFactors_subset hprime hu)
  have hu_low : (x₀:ℝ)^u.primeFactors.card ≤ (u:ℝ) := os_le_prod hprime hwin hu
  have hv_up : (v:ℝ) ≤ ((x₀:ℝ) + H)^u.primeFactors.card := by
    have h := os_prod_le hprime hwin hv
    rwa [← hk] at h
  have hupos : (0:ℝ) < (u:ℝ) := by exact_mod_cast Nat.pos_of_mem_divisors hu
  have hvpos : (0:ℝ) < (v:ℝ) := by exact_mod_cast Nat.pos_of_mem_divisors hv
  have h1 : Real.log v ≤ (u.primeFactors.card : ℝ) * Real.log ((x₀:ℝ) + H) := by
    calc Real.log v ≤ Real.log (((x₀:ℝ) + H)^u.primeFactors.card) :=
          Real.log_le_log hvpos hv_up
      _ = (u.primeFactors.card : ℝ) * Real.log ((x₀:ℝ) + H) := Real.log_pow _ _
  have h2 : (u.primeFactors.card : ℝ) * Real.log x₀ ≤ Real.log u := by
    calc (u.primeFactors.card : ℝ) * Real.log x₀
        = Real.log ((x₀:ℝ)^u.primeFactors.card) := (Real.log_pow _ _).symm
      _ ≤ Real.log u := Real.log_le_log (by positivity) hu_low
  have h3 : Real.log ((x₀:ℝ) + H) - Real.log x₀ ≤ (H:ℝ)/x₀ := by
    have hd : Real.log (((x₀:ℝ) + H)/x₀) ≤ ((x₀:ℝ) + H)/x₀ - 1 :=
      Real.log_le_sub_one_of_pos (by positivity)
    have he : Real.log (((x₀:ℝ) + H)/x₀) = Real.log ((x₀:ℝ) + H) - Real.log x₀ :=
      Real.log_div (by positivity) (by positivity)
    have hf : ((x₀:ℝ) + H)/x₀ - 1 = (H:ℝ)/x₀ := by
      field_simp
      ring
    rw [he, hf] at hd
    exact hd
  have h7 : Real.log v - Real.log u
      ≤ (u.primeFactors.card : ℝ) * (Real.log ((x₀:ℝ) + H) - Real.log x₀) := by
    have hring : (u.primeFactors.card : ℝ) * (Real.log ((x₀:ℝ) + H) - Real.log x₀)
        = (u.primeFactors.card : ℝ) * Real.log ((x₀:ℝ) + H)
          - (u.primeFactors.card : ℝ) * Real.log x₀ := by ring
    linarith [h1, h2, hring]
  have h5 : (u.primeFactors.card : ℝ) * (Real.log ((x₀:ℝ) + H) - Real.log x₀)
      ≤ (u.primeFactors.card : ℝ) * ((H:ℝ)/x₀) :=
    mul_le_mul_of_nonneg_left h3 (Nat.cast_nonneg _)
  have h6 : (u.primeFactors.card : ℝ) * ((H:ℝ)/x₀) ≤ (K:ℝ) * ((H:ℝ)/x₀) := by
    have hc : (u.primeFactors.card : ℝ) ≤ (K:ℝ) := by exact_mod_cast hkK
    exact mul_le_mul_of_nonneg_right hc (by positivity)
  calc Real.log v - Real.log u
      ≤ (u.primeFactors.card : ℝ) * (Real.log ((x₀:ℝ) + H) - Real.log x₀) := h7
    _ ≤ (u.primeFactors.card : ℝ) * ((H:ℝ)/x₀) := h5
    _ ≤ (K:ℝ) * ((H:ℝ)/x₀) := h6
    _ = (K:ℝ) * H / x₀ := by ring

/-! ### The C3 gap bound -/

/-- A consecutive-candidate pair whose `n`- and `m`-components both differ has gap
at least `δ/4` times its upper endpoint, and the upper endpoint has a nontrivial
`m`-component. -/
lemma ss_C3_gap {n : ℕ} (hn : n ≠ 0) {B : Finset ℕ} {x₀ H K : ℕ}
    (hprime : ∀ p ∈ B, p.Prime) (hcard : B.card = K)
    (hwin : ∀ p ∈ B, x₀ < p ∧ p ≤ x₀ + H)
    (hKH : 2*K*H ≤ x₀) (hx₀ : 4 ≤ x₀)
    {δ : ℝ} (hδpos : 0 < δ) (hδ1 : δ ≤ 1)
    (hδ : ∀ d ∈ n.divisors, ∀ e ∈ n.divisors, d < e → δ ≤ Real.log e - Real.log d)
    (hlarge₁ : 4*(n:ℝ) ≤ x₀)
    (hlarge₂ : 2*(K:ℝ)*H ≤ δ * x₀)
    {d₁ d₂ : ℕ} (hd₁ : d₁ ∈ (n * ∏ p ∈ B, p).divisors)
    (hd₂ : d₂ ∈ (n * ∏ p ∈ B, p).divisors) (hlt : d₁ < d₂)
    (hne_e : d₁.gcd n ≠ d₂.gcd n)
    (hne_a : d₁.gcd (∏ p ∈ B, p) ≠ d₂.gcd (∏ p ∈ B, p)) :
    δ/4 * (d₂:ℝ) ≤ (d₂:ℝ) - (d₁:ℝ) ∧ d₂.gcd (∏ p ∈ B, p) ≠ 1 := by
  have hx₀pos : 0 < x₀ := by omega
  have hx0R : (0:ℝ) < (x₀:ℝ) := by exact_mod_cast hx₀pos
  have hx1R : (1:ℝ) ≤ (x₀:ℝ) := by exact_mod_cast (by omega : 1 ≤ x₀)
  have hnx : n ≤ x₀ := by
    have h1 : (n:ℝ) ≤ (x₀:ℝ) := by
      have h0 : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
      linarith
    exact_mod_cast h1
  have hcop : n.Coprime (∏ p ∈ B, p) :=
    ss_coprime_prod hn hprime (fun p hp => (hwin p hp).1) hnx
  obtain ⟨heq₁, he₁, ha₁⟩ := ss_decomp hcop hd₁
  obtain ⟨heq₂, he₂, ha₂⟩ := ss_decomp hcop hd₂
  have hd₁pos : 0 < d₁ := Nat.pos_of_mem_divisors hd₁
  have hd₂pos : 0 < d₂ := Nat.pos_of_mem_divisors hd₂
  have hd₁R : (0:ℝ) < (d₁:ℝ) := by exact_mod_cast hd₁pos
  have hd₂R : (0:ℝ) < (d₂:ℝ) := by exact_mod_cast hd₂pos
  have he₁R : (0:ℝ) < (d₁.gcd n : ℝ) := by exact_mod_cast Nat.pos_of_mem_divisors he₁
  have he₂R : (0:ℝ) < (d₂.gcd n : ℝ) := by exact_mod_cast Nat.pos_of_mem_divisors he₂
  have ha₁R : (0:ℝ) < (d₁.gcd (∏ p ∈ B, p) : ℝ) := by
    exact_mod_cast Nat.pos_of_mem_divisors ha₁
  have ha₂R : (0:ℝ) < (d₂.gcd (∏ p ∈ B, p) : ℝ) := by
    exact_mod_cast Nat.pos_of_mem_divisors ha₂
  -- the upper endpoint has a nontrivial `m`-component
  have ha₂1 : d₂.gcd (∏ p ∈ B, p) ≠ 1 := by
    intro h1
    have ha₁1 : d₁.gcd (∏ p ∈ B, p) ≠ 1 := fun h => hne_a (h.trans h1.symm)
    have hx₀a₁ : x₀ < d₁.gcd (∏ p ∈ B, p) :=
      ss_x0_lt_of_ne_one hprime (fun p hp => (hwin p hp).1) ha₁ ha₁1
    have hd₂n : d₂ ≤ n := by
      have hd₂e : d₂ = d₂.gcd n := by
        conv_lhs => rw [heq₂]
        rw [h1, mul_one]
      calc d₂ = d₂.gcd n := hd₂e
        _ ≤ n := Nat.le_of_dvd (Nat.pos_of_ne_zero hn) (Nat.mem_divisors.mp he₂).1
    have ha₁d : d₁.gcd (∏ p ∈ B, p) ≤ d₁ :=
      Nat.le_of_dvd hd₁pos (Nat.gcd_dvd_left d₁ _)
    omega
  refine ⟨?_, ha₂1⟩
  have hlogd₁ : Real.log (d₁:ℝ)
      = Real.log (d₁.gcd n : ℝ) + Real.log (d₁.gcd (∏ p ∈ B, p) : ℝ) := by
    conv_lhs => rw [heq₁]
    push_cast
    exact Real.log_mul he₁R.ne' ha₁R.ne'
  have hlogd₂ : Real.log (d₂:ℝ)
      = Real.log (d₂.gcd n : ℝ) + Real.log (d₂.gcd (∏ p ∈ B, p) : ℝ) := by
    conv_lhs => rw [heq₂]
    push_cast
    exact Real.log_mul he₂R.ne' ha₂R.ne'
  by_cases hkeq : (d₁.gcd (∏ p ∈ B, p)).primeFactors.card
      = (d₂.gcd (∏ p ∈ B, p)).primeFactors.card
  · -- Case A: same ω — use the log-resolution δ of `n.divisors`
    have hlog_a : Real.log (d₂.gcd (∏ p ∈ B, p) : ℝ)
        - Real.log (d₁.gcd (∏ p ∈ B, p) : ℝ) ≤ (K:ℝ)*H/x₀ :=
      ss_log_ratio_le hprime hcard hwin hx₀pos ha₁ ha₂ hkeq
    have hlog_a' : Real.log (d₁.gcd (∏ p ∈ B, p) : ℝ)
        - Real.log (d₂.gcd (∏ p ∈ B, p) : ℝ) ≤ (K:ℝ)*H/x₀ :=
      ss_log_ratio_le hprime hcard hwin hx₀pos ha₂ ha₁ hkeq.symm
    have hKH2 : (K:ℝ)*H/x₀ ≤ δ/2 := by
      rw [div_le_div_iff₀ hx0R (by norm_num : (0:ℝ) < 2)]
      linarith
    have hlog_lt : Real.log (d₁:ℝ) < Real.log (d₂:ℝ) :=
      Real.log_lt_log hd₁R (by exact_mod_cast hlt)
    have hgap : δ/2 ≤ Real.log (d₂:ℝ) - Real.log (d₁:ℝ) := by
      rcases lt_or_gt_of_ne hne_e with h | h
      · have hδe := hδ _ he₁ _ he₂ h
        rw [hlogd₁, hlogd₂]
        linarith
      · exfalso
        have hδe := hδ _ he₂ _ he₁ h
        rw [hlogd₁, hlogd₂] at hlog_lt
        linarith
    have hd₁d₂ : (d₁:ℝ) ≤ (d₂:ℝ) * Real.exp (-(δ/2)) := by
      have h1 : Real.log (d₁:ℝ) ≤ Real.log (d₂:ℝ) - δ/2 := by linarith
      calc (d₁:ℝ) = Real.exp (Real.log (d₁:ℝ)) := (Real.exp_log hd₁R).symm
        _ ≤ Real.exp (Real.log (d₂:ℝ) - δ/2) := Real.exp_le_exp.mpr h1
        _ = Real.exp (Real.log (d₂:ℝ)) * Real.exp (-(δ/2)) := by
            rw [← Real.exp_add]
            ring_nf
        _ = (d₂:ℝ) * Real.exp (-(δ/2)) := by rw [Real.exp_log hd₂R]
    have hexp : δ/2/2 ≤ 1 - Real.exp (-(δ/2)) :=
      ss_half_le_one_sub_exp (by linarith) (by linarith)
    have key : (0:ℝ) ≤ (d₂:ℝ) * (1 - Real.exp (-(δ/2)) - δ/4) :=
      mul_nonneg hd₂R.le (by linarith)
    nlinarith [key, hd₁d₂]
  · -- Case B: different ω — the ratio is at least 2
    have hk₁K : (d₁.gcd (∏ p ∈ B, p)).primeFactors.card ≤ K := by
      rw [← hcard]
      exact Finset.card_le_card (os_primeFactors_subset hprime ha₁)
    have hk₂K : (d₂.gcd (∏ p ∈ B, p)).primeFactors.card ≤ K := by
      rw [← hcard]
      exact Finset.card_le_card (os_primeFactors_subset hprime ha₂)
    have he₁n : (d₁.gcd n : ℝ) ≤ (n:ℝ) := by
      exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero hn) (Nat.mem_divisors.mp he₁).1
    have he₂n : (d₂.gcd n : ℝ) ≤ (n:ℝ) := by
      exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero hn) (Nat.mem_divisors.mp he₂).1
    have hd₁cast : (d₁:ℝ) = (d₁.gcd n : ℝ) * (d₁.gcd (∏ p ∈ B, p) : ℝ) := by
      conv_lhs => rw [heq₁]
      push_cast
      ring
    have hd₂cast : (d₂:ℝ) = (d₂.gcd n : ℝ) * (d₂.gcd (∏ p ∈ B, p) : ℝ) := by
      conv_lhs => rw [heq₂]
      push_cast
      ring
    have h2d : 2*(d₁:ℝ) ≤ (d₂:ℝ) := by
      rcases Nat.lt_or_ge (d₁.gcd (∏ p ∈ B, p)).primeFactors.card
          (d₂.gcd (∏ p ∈ B, p)).primeFactors.card with hklt | hkge
      · -- ω(a₁) < ω(a₂)
        have ha₁up : (d₁.gcd (∏ p ∈ B, p) : ℝ)
            ≤ 2*(x₀:ℝ)^(d₁.gcd (∏ p ∈ B, p)).primeFactors.card :=
          le_trans (os_prod_le hprime hwin ha₁) (os_window_pow_le hx₀pos hKH hk₁K)
        have ha₂low : (x₀:ℝ)^((d₁.gcd (∏ p ∈ B, p)).primeFactors.card + 1)
            ≤ (d₂.gcd (∏ p ∈ B, p) : ℝ) := by
          refine le_trans ?_ (os_le_prod hprime hwin ha₂)
          exact pow_le_pow_right₀ (by linarith) hklt
        have ha₂d : (d₂.gcd (∏ p ∈ B, p) : ℝ) ≤ (d₂:ℝ) := by
          exact_mod_cast Nat.le_of_dvd hd₂pos (Nat.gcd_dvd_left d₂ _)
        have hpk : (0:ℝ) ≤ (x₀:ℝ)^(d₁.gcd (∏ p ∈ B, p)).primeFactors.card := by
          positivity
        calc 2*(d₁:ℝ)
            = 2*((d₁.gcd n : ℝ) * (d₁.gcd (∏ p ∈ B, p) : ℝ)) := by rw [hd₁cast]
          _ ≤ 2*((n:ℝ) * (2*(x₀:ℝ)^(d₁.gcd (∏ p ∈ B, p)).primeFactors.card)) := by
              gcongr
          _ = 4*(n:ℝ) * (x₀:ℝ)^(d₁.gcd (∏ p ∈ B, p)).primeFactors.card := by ring
          _ ≤ (x₀:ℝ) * (x₀:ℝ)^(d₁.gcd (∏ p ∈ B, p)).primeFactors.card :=
              mul_le_mul_of_nonneg_right hlarge₁ hpk
          _ = (x₀:ℝ)^((d₁.gcd (∏ p ∈ B, p)).primeFactors.card + 1) := by
              rw [pow_succ]
              ring
          _ ≤ (d₂.gcd (∏ p ∈ B, p) : ℝ) := ha₂low
          _ ≤ (d₂:ℝ) := ha₂d
      · -- ω(a₂) < ω(a₁): impossible since d₁ < d₂
        exfalso
        have hklt : (d₂.gcd (∏ p ∈ B, p)).primeFactors.card
            < (d₁.gcd (∏ p ∈ B, p)).primeFactors.card :=
          lt_of_le_of_ne hkge (fun h => hkeq h.symm)
        have ha₂up : (d₂.gcd (∏ p ∈ B, p) : ℝ)
            ≤ 2*(x₀:ℝ)^(d₂.gcd (∏ p ∈ B, p)).primeFactors.card :=
          le_trans (os_prod_le hprime hwin ha₂) (os_window_pow_le hx₀pos hKH hk₂K)
        have ha₁low : (x₀:ℝ)^((d₂.gcd (∏ p ∈ B, p)).primeFactors.card + 1)
            ≤ (d₁.gcd (∏ p ∈ B, p) : ℝ) := by
          refine le_trans ?_ (os_le_prod hprime hwin ha₁)
          exact pow_le_pow_right₀ (by linarith) hklt
        have ha₁d : (d₁.gcd (∏ p ∈ B, p) : ℝ) ≤ (d₁:ℝ) := by
          exact_mod_cast Nat.le_of_dvd hd₁pos (Nat.gcd_dvd_left d₁ _)
        have hpk : (0:ℝ) < (x₀:ℝ)^(d₂.gcd (∏ p ∈ B, p)).primeFactors.card := by
          positivity
        have hn1 : (1:ℝ) ≤ (n:ℝ) := by
          exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
        have hcontra : (d₂:ℝ) < (d₂:ℝ) := by
          calc (d₂:ℝ) = (d₂.gcd n : ℝ) * (d₂.gcd (∏ p ∈ B, p) : ℝ) := hd₂cast
            _ ≤ (n:ℝ) * (2*(x₀:ℝ)^(d₂.gcd (∏ p ∈ B, p)).primeFactors.card) := by
                gcongr
            _ = 2*(n:ℝ) * (x₀:ℝ)^(d₂.gcd (∏ p ∈ B, p)).primeFactors.card := by ring
            _ < 4*(n:ℝ) * (x₀:ℝ)^(d₂.gcd (∏ p ∈ B, p)).primeFactors.card := by
                have : (0:ℝ) < (n:ℝ) * (x₀:ℝ)^(d₂.gcd (∏ p ∈ B, p)).primeFactors.card := by
                  positivity
                nlinarith
            _ ≤ (x₀:ℝ) * (x₀:ℝ)^(d₂.gcd (∏ p ∈ B, p)).primeFactors.card :=
                mul_le_mul_of_nonneg_right hlarge₁ hpk.le
            _ = (x₀:ℝ)^((d₂.gcd (∏ p ∈ B, p)).primeFactors.card + 1) := by
                rw [pow_succ]
                ring
            _ ≤ (d₁.gcd (∏ p ∈ B, p) : ℝ) := ha₁low
            _ ≤ (d₁:ℝ) := ha₁d
            _ < (d₂:ℝ) := by exact_mod_cast hlt
        exact lt_irrefl _ hcontra
    have key : (0:ℝ) ≤ (d₂:ℝ) * (1/2 - δ/4) := mul_nonneg hd₂R.le (by linarith)
    nlinarith [key, h2d]

/-! ### Sum of inverse divisors with nontrivial `m`-component -/

lemma ss_sum_inv_comp_le {n m : ℕ} (hcop : n.Coprime m) :
    ∑ d ∈ (n*m).divisors.filter (fun d => d.gcd m ≠ 1), ((d:ℝ))⁻¹
      ≤ (∑ e ∈ n.divisors, ((e:ℝ))⁻¹) * (∑ a ∈ m.divisors.erase 1, ((a:ℝ))⁻¹) := by
  classical
  have hmem : ∀ d ∈ (n*m).divisors.filter (fun d => d.gcd m ≠ 1),
      d ∈ (n*m).divisors ∧ d.gcd m ≠ 1 := fun d hd => Finset.mem_filter.mp hd
  have hterm : ∀ d ∈ (n*m).divisors.filter (fun d => d.gcd m ≠ 1),
      ((d:ℝ))⁻¹ = ((d.gcd n : ℝ))⁻¹ * ((d.gcd m : ℝ))⁻¹ := by
    intro d hd
    conv_lhs => rw [(ss_decomp hcop (hmem d hd).1).1]
    push_cast
    rw [mul_inv]
  have hinj : ∀ d ∈ (n*m).divisors.filter (fun d => d.gcd m ≠ 1),
      ∀ d' ∈ (n*m).divisors.filter (fun d => d.gcd m ≠ 1),
      (fun d : ℕ => (d.gcd n, d.gcd m)) d = (fun d : ℕ => (d.gcd n, d.gcd m)) d'
        → d = d' := by
    intro d hd d' hd' he
    have h1 : d.gcd n = d'.gcd n := congrArg Prod.fst he
    have h2 : d.gcd m = d'.gcd m := congrArg Prod.snd he
    rw [(ss_decomp hcop (hmem d hd).1).1, (ss_decomp hcop (hmem d' hd').1).1, h1, h2]
  have himg : ∀ d ∈ (n*m).divisors.filter (fun d => d.gcd m ≠ 1),
      (d.gcd n, d.gcd m) ∈ n.divisors ×ˢ (m.divisors.erase 1) := by
    intro d hd
    obtain ⟨hdm, hne⟩ := hmem d hd
    obtain ⟨-, h1, h2⟩ := ss_decomp hcop hdm
    exact Finset.mem_product.mpr ⟨h1, Finset.mem_erase.mpr ⟨hne, h2⟩⟩
  calc ∑ d ∈ (n*m).divisors.filter (fun d => d.gcd m ≠ 1), ((d:ℝ))⁻¹
      = ∑ d ∈ (n*m).divisors.filter (fun d => d.gcd m ≠ 1),
          ((d.gcd n : ℝ))⁻¹ * ((d.gcd m : ℝ))⁻¹ := Finset.sum_congr rfl hterm
    _ = ∑ y ∈ ((n*m).divisors.filter (fun d => d.gcd m ≠ 1)).image
          (fun d : ℕ => (d.gcd n, d.gcd m)), ((y.1:ℝ))⁻¹ * ((y.2:ℝ))⁻¹ :=
        (Finset.sum_image
          (f := fun y : ℕ × ℕ => ((y.1:ℝ))⁻¹ * ((y.2:ℝ))⁻¹) hinj).symm
    _ ≤ ∑ y ∈ n.divisors ×ˢ (m.divisors.erase 1), ((y.1:ℝ))⁻¹ * ((y.2:ℝ))⁻¹ := by
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun y _ _ => by positivity
        intro y hy
        obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hy
        exact himg d hd
    _ = (∑ e ∈ n.divisors, ((e:ℝ))⁻¹) * (∑ a ∈ m.divisors.erase 1, ((a:ℝ))⁻¹) := by
        rw [Finset.sum_mul_sum]
        exact Finset.sum_product _ _ _

/-! ### Class C3: both components differ -/

lemma ss_C3_le {n : ℕ} (hn : n ≠ 0) {B : Finset ℕ} {x₀ H K : ℕ}
    (hprime : ∀ p ∈ B, p.Prime) (hcard : B.card = K)
    (hwin : ∀ p ∈ B, x₀ < p ∧ p ≤ x₀ + H)
    (hKH : 2*K*H ≤ x₀) (hx₀ : 4 ≤ x₀) (hH : 1 ≤ H)
    {δ : ℝ} (hδpos : 0 < δ) (hδ1 : δ ≤ 1)
    (hδ : ∀ d ∈ n.divisors, ∀ e ∈ n.divisors, d < e → δ ≤ Real.log e - Real.log d)
    (hσ : ∑ e ∈ n.divisors, ((e:ℝ))⁻¹ ≤ 2)
    (hlarge₁ : 4*(n:ℝ) ≤ x₀)
    (hlarge₂ : 2*(K:ℝ)*H ≤ δ * x₀) :
    pairSumOn ((n * ∏ p ∈ B, p).divisors)
        (fun d₁ d₂ => d₁.gcd n ≠ d₂.gcd n ∧
          d₁.gcd (∏ p ∈ B, p) ≠ d₂.gcd (∏ p ∈ B, p) ∧
          IsConsecutive ((n * ∏ p ∈ B, p).divisors) d₁ d₂)
      ≤ 16*K/(δ*(x₀:ℝ)) := by
  classical
  have hx₀pos : 0 < x₀ := by omega
  have hx0R : (0:ℝ) < (x₀:ℝ) := by exact_mod_cast hx₀pos
  have hnx : n ≤ x₀ := by
    have h1 : (n:ℝ) ≤ (x₀:ℝ) := by
      have h0 : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
      linarith
    exact_mod_cast h1
  have hcop : n.Coprime (∏ p ∈ B, p) :=
    ss_coprime_prod hn hprime (fun p hp => (hwin p hp).1) hnx
  have hgnn : ∀ d : ℕ,
      (0:ℝ) ≤ (if d.gcd (∏ p ∈ B, p) ≠ 1 then 4/(δ*(d:ℝ)) else 0) := by
    intro d
    split
    · positivity
    · exact le_rfl
  -- Step 1: the pair sum is at most the weighted divisor sum
  have hmain : pairSumOn ((n * ∏ p ∈ B, p).divisors)
      (fun d₁ d₂ => d₁.gcd n ≠ d₂.gcd n ∧
        d₁.gcd (∏ p ∈ B, p) ≠ d₂.gcd (∏ p ∈ B, p) ∧
        IsConsecutive ((n * ∏ p ∈ B, p).divisors) d₁ d₂)
      ≤ ∑ d ∈ (n * ∏ p ∈ B, p).divisors,
          (if d.gcd (∏ p ∈ B, p) ≠ 1 then 4/(δ*(d:ℝ)) else 0) := by
    refine os_pairSumOn_le_of_forall fun S hS => ?_
    have hterm : ∀ p ∈ S, invGap p.1 p.2
        ≤ (if p.2.gcd (∏ p ∈ B, p) ≠ 1 then 4/(δ*(p.2:ℝ)) else 0) := by
      intro p hp
      obtain ⟨hd₁, hd₂, hlt, hnee, hnea, hcons⟩ := hS p hp
      obtain ⟨hgap, hne1⟩ := ss_C3_gap hn hprime hcard hwin hKH hx₀ hδpos hδ1 hδ
        hlarge₁ hlarge₂ hd₁ hd₂ hlt hnee hnea
      have hd₂R : (0:ℝ) < (p.2:ℝ) := by
        exact_mod_cast Nat.pos_of_mem_divisors hd₂
      have hpos : (0:ℝ) < δ/4 * (p.2:ℝ) := by positivity
      have h1 : invGap p.1 p.2 ≤ (δ/4 * (p.2:ℝ))⁻¹ := by
        unfold invGap
        exact inv_anti₀ hpos hgap
      have h2 : (δ/4 * (p.2:ℝ))⁻¹ = 4/(δ*(p.2:ℝ)) := by
        rw [show δ/4 * (p.2:ℝ) = δ*(p.2:ℝ)/4 by ring, inv_div]
      rw [if_pos hne1]
      rw [← h2]
      exact h1
    have hinj : ∀ p ∈ S, ∀ p' ∈ S,
        (fun q : ℕ × ℕ => q.2) p = (fun q : ℕ × ℕ => q.2) p' → p = p' := by
      intro p hp p' hp' he
      obtain ⟨-, -, -, -, -, hcons⟩ := hS p hp
      obtain ⟨-, -, -, -, -, hcons'⟩ := hS p' hp'
      have he' : p.2 = p'.2 := he
      have h1 : p.1 = p'.1 := os_consec_pred_unique hcons (he' ▸ hcons')
      exact Prod.ext h1 he'
    calc ∑ p ∈ S, invGap p.1 p.2
        ≤ ∑ p ∈ S, (if p.2.gcd (∏ p ∈ B, p) ≠ 1 then 4/(δ*(p.2:ℝ)) else 0) :=
          Finset.sum_le_sum hterm
      _ = ∑ d ∈ S.image (fun q : ℕ × ℕ => q.2),
            (if d.gcd (∏ p ∈ B, p) ≠ 1 then 4/(δ*(d:ℝ)) else 0) :=
          (Finset.sum_image
            (f := fun d : ℕ => if d.gcd (∏ p ∈ B, p) ≠ 1
              then 4/(δ*(d:ℝ)) else 0) hinj).symm
      _ ≤ ∑ d ∈ (n * ∏ p ∈ B, p).divisors,
            (if d.gcd (∏ p ∈ B, p) ≠ 1 then 4/(δ*(d:ℝ)) else 0) := by
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun d _ _ => hgnn d
          intro d hd
          obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hd
          exact (hS p hp).2.1
  -- Step 2: the weighted divisor sum
  have hsuma : ∑ a ∈ (∏ p ∈ B, p).divisors.erase 1, ((a:ℝ))⁻¹ ≤ 2*(K:ℝ)/x₀ := by
    have h := sum_inv_divisors_erase_one_le hprime (fun p hp => (hwin p hp).1.le)
      (by rw [hcard]; nlinarith : 2 * B.card ≤ x₀) hx₀pos
    rw [hcard] at h
    exact h
  have hsumnn : (0:ℝ) ≤ ∑ a ∈ (∏ p ∈ B, p).divisors.erase 1, ((a:ℝ))⁻¹ :=
    Finset.sum_nonneg fun a _ => by positivity
  have hstep2 : ∑ d ∈ (n * ∏ p ∈ B, p).divisors,
      (if d.gcd (∏ p ∈ B, p) ≠ 1 then 4/(δ*(d:ℝ)) else 0)
      ≤ 16*K/(δ*(x₀:ℝ)) := by
    calc ∑ d ∈ (n * ∏ p ∈ B, p).divisors,
          (if d.gcd (∏ p ∈ B, p) ≠ 1 then 4/(δ*(d:ℝ)) else 0)
        = ∑ d ∈ (n * ∏ p ∈ B, p).divisors.filter
            (fun d => d.gcd (∏ p ∈ B, p) ≠ 1), 4/(δ*(d:ℝ)) :=
          (Finset.sum_filter _ _).symm
      _ = (4/δ) * ∑ d ∈ (n * ∏ p ∈ B, p).divisors.filter
            (fun d => d.gcd (∏ p ∈ B, p) ≠ 1), ((d:ℝ))⁻¹ := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun d _ => ?_
          rw [div_eq_mul_inv, mul_inv, div_eq_mul_inv]
          ring
      _ ≤ (4/δ) * ((∑ e ∈ n.divisors, ((e:ℝ))⁻¹)
            * (∑ a ∈ (∏ p ∈ B, p).divisors.erase 1, ((a:ℝ))⁻¹)) := by
          refine mul_le_mul_of_nonneg_left (ss_sum_inv_comp_le hcop) (by positivity)
      _ ≤ (4/δ) * (2 * (2*(K:ℝ)/x₀)) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact mul_le_mul hσ hsuma hsumnn (by norm_num)
      _ = 16*K/(δ*(x₀:ℝ)) := by
          field_simp
          ring
  exact le_trans hmain hstep2

/-! ### The scale step -/

/-- **The incremental multiscale step.**  For `n ≠ 0` with inverse-divisor sum at most
`2` and minimal divisor log-gap `δ`, and a fresh window `B` of `K` primes in
`(x₀, x₀+H]` with pairwise gaps `> N` (with `x₀` large as in `hlarge₁`/`hlarge₂`),
the gap sum of `n * ∏ p ∈ B, p` is controlled by that of `n` plus the one-scale
bounds plus a `16K/(δx₀)` cross-term. -/
theorem scaleStep_gapSum_le {n : ℕ} (hn : n ≠ 0) {B : Finset ℕ} {x₀ H N K : ℕ}
    (hprime : ∀ p ∈ B, p.Prime) (hcard : B.card = K) (hK : 2 ≤ K) (hN : 1 ≤ N)
    (hH : 1 ≤ H) (hx₀ : 4 ≤ x₀)
    (hwin : ∀ p ∈ B, x₀ < p ∧ p ≤ x₀ + H)
    (hsep : ∀ p ∈ B, ∀ q ∈ B, p < q → N < q - p)
    (hbig : 8 * (2*H)^(K+1) ≤ x₀) (hKH : 2*K*H ≤ x₀)
    (hlogK : 2 * (1 + Real.log K) ≤ N)
    {δ : ℝ} (hδpos : 0 < δ) (hδ1 : δ ≤ 1)
    (hδ : ∀ d ∈ n.divisors, ∀ e ∈ n.divisors, d < e → δ ≤ Real.log e - Real.log d)
    (hσ : ∑ e ∈ n.divisors, ((e:ℝ))⁻¹ ≤ 2)
    (hlarge₁ : 4*(n:ℝ) ≤ x₀)
    (hlarge₂ : 2*(K:ℝ)*H ≤ δ * x₀) :
    gapSum ((n * ∏ p ∈ B, p).divisors)
      ≤ gapSum (n.divisors) * (1 + 2*K/(x₀:ℝ))
        + 2 * ((K:ℝ)/N + 2*K*(1 + Real.log K)/N^2 + 2*(4:ℝ)^K/x₀ + (2:ℝ)^(K+3)*K/x₀)
        + 16*K/(δ*(x₀:ℝ)) := by
  classical
  have hx₀pos : 0 < x₀ := by omega
  have hx0R : (0:ℝ) < (x₀:ℝ) := by exact_mod_cast hx₀pos
  have hnx : n ≤ x₀ := by
    have h1 : (n:ℝ) ≤ (x₀:ℝ) := by
      have h0 : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
      linarith
    exact_mod_cast h1
  have hcop : n.Coprime (∏ p ∈ B, p) :=
    ss_coprime_prod hn hprime (fun p hp => (hwin p hp).1) hnx
  -- cover the consecutive pairs by three classes
  have hcover : ∀ a b, IsConsecutive ((n * ∏ p ∈ B, p).divisors) a b →
      ((a.gcd (∏ p ∈ B, p) = b.gcd (∏ p ∈ B, p) ∧
          IsConsecutive ((n * ∏ p ∈ B, p).divisors) a b) ∨
        ((a.gcd n = b.gcd n ∧ IsConsecutive ((n * ∏ p ∈ B, p).divisors) a b) ∨
         (a.gcd n ≠ b.gcd n ∧ a.gcd (∏ p ∈ B, p) ≠ b.gcd (∏ p ∈ B, p) ∧
          IsConsecutive ((n * ∏ p ∈ B, p).divisors) a b))) := by
    intro a b hcons
    by_cases h1 : a.gcd (∏ p ∈ B, p) = b.gcd (∏ p ∈ B, p)
    · exact Or.inl ⟨h1, hcons⟩
    · by_cases h2 : a.gcd n = b.gcd n
      · exact Or.inr (Or.inl ⟨h2, hcons⟩)
      · exact Or.inr (Or.inr ⟨h2, h1, hcons⟩)
  -- C1: equal `m`-component
  have hsum_m : ∑ a ∈ (∏ p ∈ B, p).divisors, ((a:ℝ))⁻¹ ≤ 1 + 2*(K:ℝ)/x₀ := by
    have h := sum_inv_divisors_le hprime (fun p hp => (hwin p hp).1.le)
      (by rw [hcard]; nlinarith : 2 * B.card ≤ x₀) hx₀pos
    rw [hcard] at h
    exact h
  have hC1 : pairSumOn ((n * ∏ p ∈ B, p).divisors)
      (fun d₁ d₂ => d₁.gcd (∏ p ∈ B, p) = d₂.gcd (∏ p ∈ B, p) ∧
        IsConsecutive ((n * ∏ p ∈ B, p).divisors) d₁ d₂)
      ≤ (1 + 2*(K:ℝ)/x₀) * gapSum n.divisors := by
    refine le_trans (ss_C1_le hcop) ?_
    exact mul_le_mul_of_nonneg_right hsum_m (gapSum_nonneg _)
  -- C2: equal `n`-component, via the one-scale bound
  have hC2 : pairSumOn ((n * ∏ p ∈ B, p).divisors)
      (fun d₁ d₂ => d₁.gcd n = d₂.gcd n ∧
        IsConsecutive ((n * ∏ p ∈ B, p).divisors) d₁ d₂)
      ≤ 2 * ((K:ℝ)/N + (2*K*(1 + Real.log K)/N^2 + 2*(4:ℝ)^K/x₀)
          + (2:ℝ)^(K+3)*K/x₀) := by
    have hswap : pairSumOn (((∏ p ∈ B, p) * n).divisors)
        (fun d₁ d₂ => d₁.gcd n = d₂.gcd n ∧
          IsConsecutive (((∏ p ∈ B, p) * n).divisors) d₁ d₂)
        ≤ (∑ e ∈ n.divisors, ((e:ℝ))⁻¹) * gapSum ((∏ p ∈ B, p).divisors) :=
      ss_C1_le hcop.symm
    rw [mul_comm n (∏ p ∈ B, p)]
    refine le_trans hswap ?_
    have hone := oneScale_gapSum_le hprime hcard hK hN hH hwin hsep hbig hKH hx₀ hlogK
    calc (∑ e ∈ n.divisors, ((e:ℝ))⁻¹) * gapSum ((∏ p ∈ B, p).divisors)
        ≤ 2 * gapSum ((∏ p ∈ B, p).divisors) :=
          mul_le_mul_of_nonneg_right hσ (gapSum_nonneg _)
      _ ≤ 2 * ((K:ℝ)/N + (2*K*(1 + Real.log K)/N^2 + 2*(4:ℝ)^K/x₀)
            + (2:ℝ)^(K+3)*K/x₀) :=
          mul_le_mul_of_nonneg_left hone (by norm_num)
  -- C3: both components differ
  have hC3 := ss_C3_le hn hprime hcard hwin hKH hx₀ hH hδpos hδ1 hδ hσ hlarge₁ hlarge₂
  -- assemble
  have h1 : gapSum ((n * ∏ p ∈ B, p).divisors)
      ≤ (1 + 2*(K:ℝ)/x₀) * gapSum n.divisors
        + (2 * ((K:ℝ)/N + (2*K*(1 + Real.log K)/N^2 + 2*(4:ℝ)^K/x₀)
            + (2:ℝ)^(K+3)*K/x₀)
          + 16*K/(δ*(x₀:ℝ))) := by
    refine le_trans (gapSum_le_pairSumOn hcover) ?_
    refine le_trans (pairSumOn_or_le _ _ _) ?_
    refine add_le_add hC1 ?_
    refine le_trans (pairSumOn_or_le _ _ _) ?_
    exact add_le_add hC2 hC3
  have heq : (1 + 2*(K:ℝ)/x₀) * gapSum n.divisors
      + (2 * ((K:ℝ)/N + (2*K*(1 + Real.log K)/N^2 + 2*(4:ℝ)^K/x₀)
          + (2:ℝ)^(K+3)*K/x₀)
        + 16*K/(δ*(x₀:ℝ)))
      = gapSum (n.divisors) * (1 + 2*K/(x₀:ℝ))
        + 2 * ((K:ℝ)/N + 2*K*(1 + Real.log K)/N^2 + 2*(4:ℝ)^K/x₀
          + (2:ℝ)^(K+3)*K/x₀)
        + 16*K/(δ*(x₀:ℝ)) := by ring
  linarith [h1, heq]

end Erdos884
end

/-! Flattened from Erdos884/MultiScale884.lean. -/
section

/-!
# Erdős Problem 884 — the multiscale construction

We iterate the single-scale construction (`OneScale884`) via the incremental step
(`ScaleStep884`), with scales produced by `Selection884`, to build integers `n` whose
pair sum `pairSum n.divisors` exceeds `C * (1 + gapSum n.divisors)` for any fixed `C`.

Export: `exists_ratio_large`.
-/

open Finset

namespace Erdos884

/-! ### Elementary real-analysis helpers -/

/-- `(x/k)^k ≤ exp x` for `x ≥ 0`. -/
lemma ms_div_pow_le_exp (k : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    (x / k) ^ k ≤ Real.exp x := by
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk
    simpa using Real.one_le_exp hx
  · have hk0 : (k : ℝ) ≠ 0 := by positivity
    have h1 : x / k ≤ Real.exp (x / k) := by
      have := Real.add_one_le_exp (x / k)
      linarith
    have h2 : (x / k) ^ k ≤ (Real.exp (x / k)) ^ k :=
      pow_le_pow_left₀ (by positivity) h1 k
    calc (x / k) ^ k ≤ (Real.exp (x / k)) ^ k := h2
      _ = Real.exp ((k : ℝ) * (x / k)) := (Real.exp_nat_mul _ _).symm
      _ = Real.exp x := by rw [mul_div_cancel₀ _ hk0]

/-- `log y ≤ y/a + a` for `1 ≤ a`, `0 < y`. -/
lemma ms_log_le_div_add {a y : ℝ} (ha : 1 ≤ a) (hy : 0 < y) :
    Real.log y ≤ y / a + a := by
  have ha0 : (0:ℝ) < a := by linarith
  have h1 : Real.log y = Real.log (y / a) + Real.log a := by
    rw [← Real.log_mul (by positivity) (by positivity), div_mul_cancel₀ _ ha0.ne']
  have h2 : Real.log (y / a) ≤ y / a - 1 := Real.log_le_sub_one_of_pos (by positivity)
  have h3 : Real.log a ≤ a - 1 := Real.log_le_sub_one_of_pos ha0
  linarith

/-! ### pairSum monotonicity and superadditivity consequences -/

/-- Monotonicity of `pairSum` under set inclusion. -/
lemma ms_pairSum_mono {B A : Finset ℕ} (h : B ⊆ A) : pairSum B ≤ pairSum A := by
  have := sum_pairSum_le_pairSum (ι := ℕ) (I := {0}) (B := fun _ => B) (A := A)
    (fun _ _ => h) (fun i hi j hj hij => by
      simp only [Finset.mem_singleton] at hi hj; omega)
  simpa using this

/-- Any member of `B` bounds the product of `B` from below. -/
lemma ms_le_prodB {B : Finset ℕ} (hB : ∀ p ∈ B, p.Prime) {p : ℕ} (hp : p ∈ B) :
    p ≤ ∏ q ∈ B, q :=
  Finset.single_le_prod' (fun q hq => (hB q hq).one_lt.le.trans' (by norm_num)) hp

/-- Superadditivity across a new scale: if all primes of `B` exceed `n`, then
`pairSum n.divisors + pairSum B ≤ pairSum ((n * ∏ B).divisors)`. -/
lemma ms_pairSum_add_le {n : ℕ} (hn : n ≠ 0) {B : Finset ℕ}
    (hB : ∀ p ∈ B, p.Prime) (hgt : ∀ p ∈ B, n < p) :
    pairSum n.divisors + pairSum B ≤ pairSum ((n * ∏ p ∈ B, p).divisors) := by
  classical
  have hm : (∏ p ∈ B, p) ≠ 0 := os_prodB_ne_zero hB
  have hnm : n * (∏ p ∈ B, p) ≠ 0 := mul_ne_zero hn hm
  have hsub1 : n.divisors ⊆ (n * ∏ p ∈ B, p).divisors := by
    intro d hd
    rw [Nat.mem_divisors] at hd ⊢
    exact ⟨hd.1.mul_right _, hnm⟩
  have hsub2 : B ⊆ (n * ∏ p ∈ B, p).divisors := by
    intro p hp
    rw [Nat.mem_divisors]
    exact ⟨(Finset.dvd_prod_of_mem _ hp).mul_left n, hnm⟩
  have hdisj : Disjoint n.divisors B := by
    rw [Finset.disjoint_left]
    intro d hd hdB
    have h1 : d ≤ n := Nat.divisor_le hd
    have h2 := hgt d hdB
    omega
  have := sum_pairSum_le_pairSum (ι := ℕ) (I := {0, 1})
    (B := fun i => if i = 0 then n.divisors else B) (A := (n * ∏ p ∈ B, p).divisors)
    (fun i _ => by split <;> [exact hsub1; exact hsub2])
    (fun i hi j hj hij => by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj
      rcases hi with rfl | rfl <;> rcases hj with rfl | rfl
      · exact absurd rfl hij
      · simpa using hdisj
      · simpa using hdisj.symm
      · exact absurd rfl hij)
  simpa using this

/-! ### Quotient monotonicity workhorse -/

lemma ms_div_le_div {a b c d : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hd : 0 < d) (hdc : d ≤ c) :
    a / c ≤ b / d := by
  have hc : 0 < c := lt_of_lt_of_le hd hdc
  rw [div_le_div_iff₀ hc hd]
  nlinarith

/-! ### Parameter estimates for one scale -/

/-- The window-size condition `8·(2H)^(K+1) ≤ exp L` from `K ≤ L/(12Λ)`, `H ≤ 7KL`. -/
lemma ms_hbig_aux {Λ L : ℝ} {K H : ℕ} (hΛ : 30 ≤ Λ) (hL : Real.exp Λ = L)
    (hH1 : 1 ≤ (H:ℝ)) (hK1 : 1 ≤ (K:ℝ)) (hK12 : (K:ℝ)*(12*Λ) ≤ L)
    (hHb : (H:ℝ) ≤ 7*K*L) :
    (8:ℝ)*(2*H)^(K+1) ≤ Real.exp L := by
  have hΛ0 : (0:ℝ) < Λ := by linarith
  have hL1 : Λ + 1 ≤ L := by rw [← hL]; exact Real.add_one_le_exp Λ
  have hL31 : 31 ≤ L := by linarith
  have hL0 : (0:ℝ) < L := by linarith
  have hK0 : (0:ℝ) < K := by linarith
  have h2H0 : (0:ℝ) < 2*(H:ℝ) := by linarith
  have hlogL : Real.log L = Λ := by rw [← hL, Real.log_exp]
  have hlogK : Real.log (K:ℝ) ≤ Λ := by
    have hKL : (K:ℝ) ≤ L := by nlinarith
    have h1 : Real.log (K:ℝ) ≤ Real.log L := Real.log_le_log hK0 hKL
    rwa [hlogL] at h1
  have hlog2H : Real.log (2*(H:ℝ)) ≤ 3*Λ := by
    have h14 : 2*(H:ℝ) ≤ 14*((K:ℝ)*L) := by nlinarith
    have h1 : Real.log (2*(H:ℝ)) ≤ Real.log (14*((K:ℝ)*L)) := Real.log_le_log h2H0 h14
    have h2 : Real.log (14*((K:ℝ)*L)) = Real.log 14 + (Real.log K + Real.log L) := by
      rw [Real.log_mul (by norm_num) (by positivity), Real.log_mul (by positivity) (by positivity)]
    have h3 : Real.log (14:ℝ) ≤ 13 := by
      have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 14 by norm_num); linarith
    rw [h2, hlogL] at h1
    linarith
  have hpow0 : (0:ℝ) < (2*(H:ℝ))^(K+1) := by positivity
  have hmain : Real.log ((8:ℝ)*(2*H)^(K+1)) ≤ L := by
    have h1 : Real.log ((8:ℝ)*(2*(H:ℝ))^(K+1)) = Real.log 8 + ((K:ℝ)+1)*Real.log (2*(H:ℝ)) := by
      rw [Real.log_mul (by norm_num) hpow0.ne', Real.log_pow]
      push_cast; ring
    have hlog8 : Real.log (8:ℝ) ≤ 7 := by
      have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 8 by norm_num); linarith
    have hlog2H0 : 0 ≤ Real.log (2*(H:ℝ)) := Real.log_nonneg (by linarith)
    have h2 : ((K:ℝ)+1)*Real.log (2*(H:ℝ)) ≤ (2*(K:ℝ))*(3*Λ) :=
      mul_le_mul (by linarith) hlog2H (by linarith) (by linarith)
    have h3 : (2*(K:ℝ))*(3*Λ) ≤ L/2 := by nlinarith
    rw [h1]
    linarith
  calc (8:ℝ)*(2*H)^(K+1)
      = Real.exp (Real.log ((8:ℝ)*(2*(H:ℝ))^(K+1))) := (Real.exp_log (by positivity)).symm
    _ ≤ Real.exp L := Real.exp_le_exp.mpr hmain

/-- The `2KH ≤ γ·exp L` estimate. -/
lemma ms_KH_aux {Λ L γ : ℝ} {K H : ℕ} (hγ : 0 < γ) (hΛγ : 3584/γ ≤ Λ)
    (hΛ : 30 ≤ Λ) (hL : Real.exp Λ = L) (hKL : (K:ℝ) ≤ L)
    (hHb : (H:ℝ) ≤ 7*K*L) :
    2*(K:ℝ)*H ≤ γ * Real.exp L := by
  have hK0 : (0:ℝ) ≤ (K:ℝ) := Nat.cast_nonneg K
  have hΛ0 : (0:ℝ) < Λ := by linarith
  have hL1 : Λ + 1 ≤ L := by rw [← hL]; exact Real.add_one_le_exp Λ
  have hL0 : (0:ℝ) < L := by linarith
  have h1 : 2*(K:ℝ)*H ≤ 14*L^3 := by
    nlinarith [mul_le_mul_of_nonneg_left hHb (show (0:ℝ) ≤ 2*(K:ℝ) by positivity),
      mul_le_mul_of_nonneg_right (mul_self_le_mul_self hK0 hKL) hL0.le]
  have hγΛ : 3584 ≤ γ*Λ := by
    have h := mul_le_mul_of_nonneg_left hΛγ hγ.le
    have heq : γ*(3584/γ) = 3584 := by field_simp
    linarith
  have hγL : 3584 ≤ γ*L := by nlinarith
  have hp4 : L^4/256 ≤ Real.exp L := by
    calc L^4/256 = (L/4)^4 := by ring
      _ ≤ Real.exp L := ms_div_pow_le_exp 4 hL0.le
  have h4 : 14*L^3 ≤ γ*(L^4/256) := by
    nlinarith [mul_le_mul_of_nonneg_right hγL (show (0:ℝ) ≤ L^3 by positivity)]
  have h3 : γ*(L^4/256) ≤ γ*Real.exp L := mul_le_mul_of_nonneg_left hp4 hγ.le
  linarith

/-- The exponential-junk error terms are at most `η` once `Λ ≥ 6(E+20)/η`. -/
lemma ms_err_aux {Λ L E η : ℝ} {K x₀ : ℕ} (hE : 0 ≤ E) (hη : 0 < η)
    (hΛ : 30 ≤ Λ) (hΛE : 6*(E+20)/η ≤ Λ) (hL : Real.exp Λ = L)
    (hK6 : 2*(K:ℝ) ≤ L/6) (hKL : (K:ℝ) ≤ L) (hx₀ : Real.exp L ≤ (x₀:ℝ)) :
    E*(K:ℝ)/x₀ + 2*(2*(4:ℝ)^K/x₀ + (2:ℝ)^(K+3)*K/x₀) ≤ η := by
  have hΛ0 : (0:ℝ) < Λ := by linarith
  have hL1 : Λ + 1 ≤ L := by rw [← hL]; exact Real.add_one_le_exp Λ
  have hL0 : (0:ℝ) < L := by linarith
  have ht0 : (0:ℝ) < Real.exp L := Real.exp_pos L
  have hx0 : (0:ℝ) < (x₀:ℝ) := lt_of_lt_of_le ht0 hx₀
  have hK0 : (0:ℝ) ≤ (K:ℝ) := Nat.cast_nonneg K
  have hexp2 : (4:ℝ) ≤ Real.exp 2 := by
    have h1 : (2:ℝ) ≤ Real.exp 1 := by
      have := Real.add_one_le_exp (1:ℝ); linarith
    have h2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
      rw [← Real.exp_add]; norm_num
    nlinarith
  have h4K : (4:ℝ)^K ≤ Real.exp (2*(K:ℝ)) := by
    calc (4:ℝ)^K ≤ (Real.exp 2)^K := pow_le_pow_left₀ (by norm_num) hexp2 K
      _ = Real.exp ((K:ℕ)*(2:ℝ)) := (Real.exp_nat_mul 2 K).symm
      _ = Real.exp (2*(K:ℝ)) := by rw [mul_comm]
  have h2K : (2:ℝ)^K ≤ Real.exp (2*(K:ℝ)) := by
    calc (2:ℝ)^K ≤ (4:ℝ)^K := pow_le_pow_left₀ (by norm_num) (by norm_num) K
      _ ≤ Real.exp (2*(K:ℝ)) := h4K
  have he2K1 : (1:ℝ) ≤ Real.exp (2*(K:ℝ)) := Real.one_le_exp (by positivity)
  have hL1' : (1:ℝ) ≤ L := by linarith
  -- numerator bound
  have hU : E*(K:ℝ) + 4*(4:ℝ)^K + 2*((2:ℝ)^(K+3)*K)
      ≤ (E+20)*L*Real.exp (2*(K:ℝ)) := by
    have hEK : E*(K:ℝ) ≤ E*L*Real.exp (2*(K:ℝ)) := by
      have ha : E*(K:ℝ) ≤ E*L := mul_le_mul_of_nonneg_left hKL hE
      have hb : E*L*1 ≤ E*L*Real.exp (2*(K:ℝ)) :=
        mul_le_mul_of_nonneg_left he2K1 (mul_nonneg hE (by linarith))
      linarith
    have h44 : 4*(4:ℝ)^K ≤ 4*L*Real.exp (2*(K:ℝ)) := by
      have hc : (1:ℝ)*Real.exp (2*(K:ℝ)) ≤ L*Real.exp (2*(K:ℝ)) :=
        mul_le_mul_of_nonneg_right hL1' (Real.exp_pos _).le
      linarith [h4K]
    have hp : (2:ℝ)^(K+3) = 8*(2:ℝ)^K := by ring
    have h2K3 : 2*((2:ℝ)^(K+3)*K) ≤ 16*L*Real.exp (2*(K:ℝ)) := by
      rw [hp]
      nlinarith [mul_le_mul_of_nonneg_right h2K hK0,
        mul_le_mul_of_nonneg_left hKL (Real.exp_pos (2*(K:ℝ))).le]
    linarith
  have hmono : Real.exp (2*(K:ℝ)) ≤ Real.exp (L/6) := Real.exp_le_exp.mpr hK6
  have hV : E*(K:ℝ) + 4*(4:ℝ)^K + 2*((2:ℝ)^(K+3)*K)
      ≤ (E+20)*L*Real.exp (L/6) := by
    have h := mul_le_mul_of_nonneg_left hmono (mul_nonneg (by linarith : (0:ℝ) ≤ E+20) hL0.le)
    linarith
  have hU0 : (0:ℝ) ≤ E*(K:ℝ) + 4*(4:ℝ)^K + 2*((2:ℝ)^(K+3)*K) := by
    have := mul_nonneg hE hK0; positivity
  -- key quotient chain
  have hquot : (E+20)*L*Real.exp (L/6) / Real.exp L = (E+20)*L/Real.exp (5*L/6) := by
    have hsplit : Real.exp L = Real.exp (L/6) * Real.exp (5*L/6) := by
      rw [← Real.exp_add]; ring_nf
    rw [hsplit]
    field_simp
  have h56 : 25*L^2/144 ≤ Real.exp (5*L/6) := by
    calc 25*L^2/144 = ((5*L/6)/2)^2 := by ring
      _ ≤ Real.exp (5*L/6) := ms_div_pow_le_exp 2 (by positivity)
  have hd : (E+20)*L/Real.exp (5*L/6) ≤ (E+20)*L/(25*L^2/144) :=
    ms_div_le_div (by nlinarith) (le_refl _) (by positivity) h56
  have heq : (E+20)*L/(25*L^2/144) = 144*(E+20)/(25*L) := by
    field_simp
  have hstep : 144*(E+20)/(25*L) ≤ 6*(E+20)/L := by
    rw [div_le_div_iff₀ (by positivity) hL0]
    nlinarith
  have hfinal : 6*(E+20)/L ≤ η := by
    rw [div_le_iff₀ hL0]
    have h1 : η*(6*(E+20)/η) = 6*(E+20) := by field_simp
    nlinarith [mul_le_mul_of_nonneg_left hΛE hη.le, mul_le_mul_of_nonneg_left hL1 hη.le]
  -- assemble
  have hLHS : E*(K:ℝ)/x₀ + 2*(2*(4:ℝ)^K/x₀ + (2:ℝ)^(K+3)*K/x₀)
      = (E*(K:ℝ) + 4*(4:ℝ)^K + 2*((2:ℝ)^(K+3)*K))/x₀ := by ring
  rw [hLHS]
  calc (E*(K:ℝ) + 4*(4:ℝ)^K + 2*((2:ℝ)^(K+3)*K))/(x₀:ℝ)
      ≤ ((E+20)*L*Real.exp (L/6))/Real.exp L := ms_div_le_div hU0 hV ht0 hx₀
    _ = (E+20)*L/Real.exp (5*L/6) := hquot
    _ ≤ (E+20)*L/(25*L^2/144) := hd
    _ = 144*(E+20)/(25*L) := heq
    _ ≤ 6*(E+20)/L := hstep
    _ ≤ η := hfinal

/-- Lower bound `Λ/2 ≤ log(K/2)` for the floor-chosen `K`. -/
lemma ms_logK2_ge {Λ L : ℝ} {K M : ℕ} (hM1 : 1 ≤ M) (hΛM : 3*(M:ℝ)+30 ≤ Λ)
    (hL : Real.exp Λ = L) (hKlow : L/(2*(M:ℝ)*Λ) ≤ (K:ℝ)) :
    Λ/2 ≤ Real.log ((K:ℝ)/2) := by
  have hMR : (1:ℝ) ≤ (M:ℝ) := by exact_mod_cast hM1
  have hM0 : (0:ℝ) < (M:ℝ) := by linarith
  have hΛ0 : (0:ℝ) < Λ := by linarith
  have hL0 : (0:ℝ) < L := by rw [← hL]; exact Real.exp_pos Λ
  have hq0 : (0:ℝ) < L/(4*(M:ℝ)*Λ) := by positivity
  have hK2 : L/(4*(M:ℝ)*Λ) ≤ (K:ℝ)/2 := by
    have heq : L/(4*(M:ℝ)*Λ) = (L/(2*(M:ℝ)*Λ))/2 := by ring
    rw [heq]
    linarith
  have h1 : Real.log (L/(4*(M:ℝ)*Λ)) ≤ Real.log ((K:ℝ)/2) := Real.log_le_log hq0 hK2
  have h2 : Real.log (L/(4*(M:ℝ)*Λ)) = Real.log L - Real.log (4*(M:ℝ)*Λ) :=
    Real.log_div hL0.ne' (by positivity)
  have h3 : Real.log L = Λ := by rw [← hL, Real.log_exp]
  have h4 : Real.log (4*(M:ℝ)*Λ) ≤ Λ/2 := by
    have ha : Real.log (4*(M:ℝ)*Λ) = Real.log 4 + Real.log (M:ℝ) + Real.log Λ := by
      rw [Real.log_mul (by positivity) (by positivity),
        Real.log_mul (by norm_num) (by positivity)]
    have hb : Real.log (4:ℝ) ≤ 3 := by
      have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 4 by norm_num); linarith
    have hc : Real.log (M:ℝ) ≤ (M:ℝ) := by
      have := Real.log_le_sub_one_of_pos hM0; linarith
    have hd : Real.log Λ ≤ Λ/8 + 8 := ms_log_le_div_add (by norm_num) hΛ0
    rw [ha]
    linarith
  linarith [h2 ▸ h1]

/-- The per-scale target `1/(112 M)` is below `K·log(K/2)/(28 L)`. -/
lemma ms_tau_ge {Λ L : ℝ} {K M : ℕ} (hΛ0 : 0 < Λ) (hL0 : 0 < L) (hM0 : 0 < M)
    (hKlow : L/(2*(M:ℝ)*Λ) ≤ (K:ℝ)) (hlg : Λ/2 ≤ Real.log ((K:ℝ)/2)) :
    1/(112*(M:ℝ)) ≤ (K:ℝ)*Real.log ((K:ℝ)/2)/(28*L) := by
  have hM0R : (0:ℝ) < (M:ℝ) := by exact_mod_cast hM0
  have h1 : L/(2*(M:ℝ)*Λ)*(Λ/2) ≤ (K:ℝ)*Real.log ((K:ℝ)/2) :=
    mul_le_mul hKlow hlg (by positivity) (Nat.cast_nonneg K)
  have heq : L/(2*(M:ℝ)*Λ)*(Λ/2) = L/(4*(M:ℝ)) := by field_simp; ring
  have h2 : L/(4*(M:ℝ))/(28*L) = 1/(112*(M:ℝ)) := by field_simp; ring
  rw [← h2]
  exact ms_div_le_div (by positivity) (heq ▸ h1) (by positivity) (le_refl _)

/-- Energy lower bound in the window form used by the recursion. -/
lemma ms_pairSum_ge {B : Finset ℕ} {x₀ H K : ℕ} {L : ℝ}
    (hcard : B.card = K) (hK4 : 4 ≤ K) (hH1 : 1 ≤ H)
    (hwin : ∀ p ∈ B, x₀ < p ∧ p ≤ x₀ + H)
    (hHb : (H:ℝ) ≤ 7*K*L) (hL0 : 0 < L)
    (hlg0 : 0 ≤ Real.log ((K:ℝ)/2)) :
    (K:ℝ)*Real.log ((K:ℝ)/2)/(28*L) ≤ pairSum B := by
  have hH0 : (1:ℝ) ≤ (H:ℝ) := by exact_mod_cast hH1
  have hK0 : (0:ℝ) < (K:ℝ) := by
    have : 0 < K := by omega
    exact_mod_cast this
  have hdiam : ∀ a ∈ B, ∀ b ∈ B, (b:ℝ) - (a:ℝ) ≤ (H:ℝ) := by
    intro a ha b hb
    have h1 : x₀ + 1 ≤ a := (hwin a ha).1
    have h2 : b ≤ x₀ + H := (hwin b hb).2
    have h1' : ((x₀:ℝ) + 1) ≤ (a:ℝ) := by exact_mod_cast h1
    have h2' : (b:ℝ) ≤ (x₀:ℝ) + (H:ℝ) := by exact_mod_cast h2
    linarith
  have hE := pairSum_ge_energy (A := B) (H := (H:ℝ))
    (by omega : 4 ≤ B.card) hH0 hdiam
  rw [hcard] at hE
  have h4H : (0:ℝ) < 4*(H:ℝ) := by linarith
  have hnum : (0:ℝ) ≤ (K:ℝ)^2*Real.log ((K:ℝ)/2) := mul_nonneg (by positivity) hlg0
  have hchain : (K:ℝ)*Real.log ((K:ℝ)/2)/(28*L)
      ≤ (K:ℝ)^2*Real.log ((K:ℝ)/2)/(4*(H:ℝ)) := by
    have heq : (K:ℝ)*Real.log ((K:ℝ)/2)/(28*L) = (K:ℝ)^2*Real.log ((K:ℝ)/2)/(28*(K:ℝ)*L) := by
      field_simp
    rw [heq]
    exact ms_div_le_div hnum (le_refl _) h4H (by nlinarith)
  calc (K:ℝ)*Real.log ((K:ℝ)/2)/(28*L)
      ≤ (K:ℝ)^2*Real.log ((K:ℝ)/2)/(4*(H:ℝ)) := hchain
    _ ≤ pairSum B := hE

/-- The two main gap-cost terms are at most `P/(8C)` for any `P ≥ K·log(K/2)/(28L)`. -/
lemma ms_main_aux {Λ L ε C P : ℝ} {K N : ℕ}
    (hC : 0 < C) (hε : 0 < ε) (hΛ : 30 ≤ Λ) (hL0 : 0 < L)
    (hK0 : 0 < (K:ℝ)) (hN0 : 0 < (N:ℝ))
    (hlogKΛ : Real.log K ≤ Λ)
    (hlg : Λ/2 ≤ Real.log ((K:ℝ)/2))
    (hεΛ : 1792*C ≤ ε*Λ)
    (hε2L : 7168*C ≤ ε^2*L)
    (hNlow : ε*L ≤ (N:ℝ))
    (hP : (K:ℝ)*Real.log ((K:ℝ)/2)/(28*L) ≤ P) :
    2*((K:ℝ)/N + 2*K*(1 + Real.log K)/N^2) ≤ P/(8*C) := by
  have hlg0 : (0:ℝ) < Real.log ((K:ℝ)/2) := by linarith
  have hεL0 : (0:ℝ) < ε*L := by positivity
  have hKlg0 : (0:ℝ) ≤ (K:ℝ)*Real.log ((K:ℝ)/2) := by positivity
  have ht1 : 2*(K:ℝ)/N ≤ (K:ℝ)*Real.log ((K:ℝ)/2)/(28*L)/(16*C) := by
    rw [div_div, div_le_div_iff₀ hN0 (by positivity)]
    have h1 : (K:ℝ)*(Λ/2)*(ε*L) ≤ (K:ℝ)*Real.log ((K:ℝ)/2)*N :=
      mul_le_mul (mul_le_mul_of_nonneg_left hlg hK0.le) hNlow hεL0.le hKlg0
    have h2 : (K:ℝ)*L*(1792*C) ≤ (K:ℝ)*L*(ε*Λ) :=
      mul_le_mul_of_nonneg_left hεΛ (by positivity)
    nlinarith [h1, h2]
  have ht2 : 2*(2*(K:ℝ)*(1 + Real.log K)/N^2) ≤ (K:ℝ)*Real.log ((K:ℝ)/2)/(28*L)/(16*C) := by
    have hlhs : 2*(2*(K:ℝ)*(1 + Real.log K)/N^2) = (4*(K:ℝ)*(1 + Real.log K))/(N:ℝ)^2 := by
      ring
    rw [hlhs, div_div, div_le_div_iff₀ (by positivity : (0:ℝ) < ((N:ℝ))^2) (by positivity)]
    have hN2 : (ε*L)^2 ≤ ((N:ℝ))^2 := pow_le_pow_left₀ hεL0.le hNlow 2
    have h1 : (K:ℝ)*(Λ/2)*((ε*L)^2) ≤ (K:ℝ)*Real.log ((K:ℝ)/2)*((N:ℝ))^2 :=
      mul_le_mul (mul_le_mul_of_nonneg_left hlg hK0.le) hN2 (by positivity) hKlg0
    have h2 : 1 + Real.log K ≤ 2*Λ := by linarith
    have h3 := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right h2 (show (0:ℝ) ≤ 28*L*(16*C) by positivity))
      (show (0:ℝ) ≤ 2*(2*(K:ℝ)) by positivity)
    have h4 : 7168*C*L ≤ ε^2*L*L := mul_le_mul_of_nonneg_right hε2L hL0.le
    have h5 := mul_le_mul_of_nonneg_left h4 (show (0:ℝ) ≤ (K:ℝ)*(Λ/2) by positivity)
    nlinarith [h1, h3, h5]
  have hPC : (K:ℝ)*Real.log ((K:ℝ)/2)/(28*L)/(16*C) + (K:ℝ)*Real.log ((K:ℝ)/2)/(28*L)/(16*C)
      = ((K:ℝ)*Real.log ((K:ℝ)/2)/(28*L))/(8*C) := by
    field_simp
    ring
  have hfin : ((K:ℝ)*Real.log ((K:ℝ)/2)/(28*L))/(8*C) ≤ P/(8*C) :=
    ms_div_le_div (by positivity) hP (by positivity) (le_refl _)
  have hsum : 2*((K:ℝ)/N + 2*(K:ℝ)*(1 + Real.log K)/N^2)
      = 2*(K:ℝ)/N + 2*(2*(K:ℝ)*(1 + Real.log K)/N^2) := by ring
  rw [hsum]
  linarith [ht1, ht2, hPC, hfin]

/-! ### The scale-setup lemma -/

/-- The conclusion of `separated_primes_selection` for fixed `ε, T_C`. -/
def ms_SelProp (ε T_C : ℝ) : Prop :=
  ∀ t : ℝ, T_C ≤ t → ∀ K : ℕ, 2 ≤ K →
    (K : ℝ) ≤ Real.log t / Real.log (Real.log t) →
    ∃ (B : Finset ℕ) (x₀ N H : ℕ),
      (∀ p ∈ B, Nat.Prime p) ∧ B.card = K ∧
      (t ≤ (x₀:ℝ)) ∧ ((x₀:ℝ) ≤ 8*t) ∧
      (∀ p ∈ B, x₀ < p ∧ p ≤ x₀ + H) ∧
      (∀ p ∈ B, ∀ q ∈ B, p < q → N < q - p) ∧
      (ε * Real.log t ≤ (N:ℝ)) ∧ ((N:ℝ) ≤ Real.log t) ∧ 1 ≤ N ∧
      ((H:ℝ) ≤ 7 * K * Real.log t) ∧ 1 ≤ H ∧ ((x₀:ℝ) + H ≤ 9*t)

set_option maxHeartbeats 1600000 in
/-- One scale, fully prepared: primes `B` in a window above `Θ`, with all side conditions
for `oneScale`/`scaleStep`, a pair-sum contribution of at least `1/(112M)`, main gap-cost
controlled by `pairSum B/(8C)`, and all junk terms below `η`. -/
lemma ms_scale_setup {ε T_C : ℝ} (C : ℝ) (hC : 0 < C) (hε : 0 < ε)
    (hsel : ms_SelProp ε T_C) (M : ℕ) (hM : 12 ≤ M)
    (Θ E η γ : ℝ) (hE : 0 ≤ E) (hη : 0 < η) (hγ : 0 < γ) (hγ1 : γ ≤ 1) :
    ∃ (B : Finset ℕ) (x₀ N H K : ℕ),
      (∀ p ∈ B, Nat.Prime p) ∧ B.card = K ∧ 4 ≤ K ∧
      (∀ p ∈ B, x₀ < p ∧ p ≤ x₀ + H) ∧
      (∀ p ∈ B, ∀ q ∈ B, p < q → N < q - p) ∧
      1 ≤ N ∧ 1 ≤ H ∧ 4 ≤ x₀ ∧ Θ ≤ (x₀:ℝ) ∧
      8 * (2*H)^(K+1) ≤ x₀ ∧ 2*K*H ≤ x₀ ∧
      2 * (1 + Real.log K) ≤ (N:ℝ) ∧
      2*(K:ℝ)*H ≤ γ * x₀ ∧
      2*(K:ℝ)/x₀ ≤ η ∧
      1/(112*(M:ℝ)) ≤ pairSum B ∧
      2*((K:ℝ)/N + 2*K*(1 + Real.log K)/N^2) ≤ pairSum B / (8*C) ∧
      E*(K:ℝ)/x₀ + 2*(2*(4:ℝ)^K/x₀ + (2:ℝ)^(K+3)*K/x₀) ≤ η := by
  -- an opaque threshold Λ dominating every requirement
  obtain ⟨Λ, h30, hc20M, hc3M, hc16ε, hc1792, hc7168, hcγ, hcE, hcΘ, hcT, hcη⟩ :
      ∃ Λ : ℝ, 30 ≤ Λ ∧ 20*(M:ℝ) ≤ Λ ∧ 3*(M:ℝ)+30 ≤ Λ ∧ 16/ε ≤ Λ ∧ 1792*C/ε ≤ Λ ∧
        7168*C/ε^2 ≤ Λ ∧ 3584/γ ≤ Λ ∧ 6*(E+20)/η ≤ Λ ∧ Θ ≤ Λ ∧ T_C ≤ Λ ∧ 8/η ≤ Λ := by
    refine ⟨max 30 (max (20*(M:ℝ)) (max (3*(M:ℝ)+30) (max (16/ε) (max (1792*C/ε)
      (max (7168*C/ε^2) (max (3584/γ) (max (6*(E+20)/η) (max Θ (max T_C (8/η)))))))))),
      le_max_left _ _, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact le_max_of_le_right (le_max_left _ _)
    · exact le_max_of_le_right (le_max_of_le_right (le_max_left _ _))
    · exact le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_left _ _)))
    · exact le_max_of_le_right (le_max_of_le_right (le_max_of_le_right
        (le_max_of_le_right (le_max_left _ _))))
    · exact le_max_of_le_right (le_max_of_le_right (le_max_of_le_right
        (le_max_of_le_right (le_max_of_le_right (le_max_left _ _)))))
    · exact le_max_of_le_right (le_max_of_le_right (le_max_of_le_right
        (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_left _ _))))))
    · exact le_max_of_le_right (le_max_of_le_right (le_max_of_le_right
        (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right
          (le_max_of_le_right (le_max_left _ _)))))))
    · exact le_max_of_le_right (le_max_of_le_right (le_max_of_le_right
        (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right
          (le_max_of_le_right (le_max_of_le_right (le_max_left _ _))))))))
    · exact le_max_of_le_right (le_max_of_le_right (le_max_of_le_right
        (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right
          (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_left _ _)))))))))
    · exact le_max_of_le_right (le_max_of_le_right (le_max_of_le_right
        (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right
          (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_right _ _)))))))))
  have hMR : (12:ℝ) ≤ (M:ℝ) := by exact_mod_cast hM
  have hM1R : (1:ℝ) ≤ (M:ℝ) := by linarith
  have hΛ0 : (0:ℝ) < Λ := by linarith
  -- an opaque L with exp Λ = L
  obtain ⟨L, hexpΛ⟩ : ∃ L : ℝ, Real.exp Λ = L := ⟨_, rfl⟩
  have hL1 : Λ + 1 ≤ L := by rw [← hexpΛ]; exact Real.add_one_le_exp Λ
  have hL0 : (0:ℝ) < L := by rw [← hexpΛ]; exact Real.exp_pos Λ
  have hL31 : 31 ≤ L := by linarith
  have hLΛ : Λ ≤ L := by linarith
  have hLsq : Λ^2/4 ≤ L := by
    calc Λ^2/4 = (Λ/2)^2 := by ring
      _ ≤ Real.exp Λ := ms_div_pow_le_exp 2 hΛ0.le
      _ = L := hexpΛ
  have ht1 : L + 1 ≤ Real.exp L := Real.add_one_le_exp L
  have ht0 : (0:ℝ) < Real.exp L := Real.exp_pos L
  have hlogL : Real.log L = Λ := by rw [← hexpΛ, Real.log_exp]
  have hx5 : 5 ≤ L/((M:ℝ)*Λ) := by
    have h1 : 5 ≤ (Λ^2/4)/((M:ℝ)*Λ) := by
      rw [le_div_iff₀ (by positivity)]
      nlinarith [mul_le_mul_of_nonneg_right hc20M hΛ0.le]
    have h2 : (Λ^2/4)/((M:ℝ)*Λ) ≤ L/((M:ℝ)*Λ) :=
      ms_div_le_div (by positivity) hLsq (by positivity) (le_refl _)
    linarith
  -- an opaque K with the floor properties
  obtain ⟨K, hK4, hKx, hxK⟩ :
      ∃ K : ℕ, 4 ≤ K ∧ (K:ℝ) ≤ L/((M:ℝ)*Λ) ∧ L/((M:ℝ)*Λ) < (K:ℝ)+1 := by
    refine ⟨⌊L/((M:ℝ)*Λ)⌋₊, ?_, Nat.floor_le (by positivity), Nat.lt_floor_add_one _⟩
    exact Nat.le_floor (by push_cast; linarith)
  have hK2 : 2 ≤ K := by omega
  have hK1N : 1 ≤ K := by omega
  have hK0 : (0:ℝ) < (K:ℝ) := by
    have h4 : (4:ℝ) ≤ (K:ℝ) := by exact_mod_cast hK4
    linarith
  have hK1R : (1:ℝ) ≤ (K:ℝ) := by linarith
  have hKlow : L/(2*(M:ℝ)*Λ) ≤ (K:ℝ) := by
    have heq : L/(2*(M:ℝ)*Λ) = (L/((M:ℝ)*Λ))/2 := by ring
    rw [heq]
    linarith
  have hKMΛ : (K:ℝ)*((M:ℝ)*Λ) ≤ L := (le_div_iff₀ (by positivity)).mp hKx
  have hK12 : (K:ℝ)*(12*Λ) ≤ L := by
    nlinarith [mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hMR hΛ0.le) hK0.le]
  have hKL : (K:ℝ) ≤ L := by
    nlinarith [mul_le_mul_of_nonneg_left (show (1:ℝ) ≤ 12*Λ by linarith) hK0.le]
  have hK6 : 2*(K:ℝ) ≤ L/6 := by
    nlinarith [mul_le_mul_of_nonneg_left (show (12:ℝ) ≤ 12*Λ by linarith) hK0.le]
  have hlogKΛ : Real.log (K:ℝ) ≤ Λ := by
    have h1 : Real.log (K:ℝ) ≤ Real.log L := Real.log_le_log hK0 hKL
    rwa [hlogL] at h1
  have hlg : Λ/2 ≤ Real.log ((K:ℝ)/2) :=
    ms_logK2_ge (by omega) (by linarith) hexpΛ hKlow
  have hlg0 : (0:ℝ) ≤ Real.log ((K:ℝ)/2) := by linarith
  have hεΛ16 : 16 ≤ ε*Λ := by
    have heq : ε*(16/ε) = 16 := by field_simp
    nlinarith [mul_le_mul_of_nonneg_left hc16ε hε.le]
  have hεΛC : 1792*C ≤ ε*Λ := by
    have heq : ε*(1792*C/ε) = 1792*C := by field_simp
    nlinarith [mul_le_mul_of_nonneg_left hc1792 hε.le]
  have hε2L : 7168*C ≤ ε^2*L := by
    have heq : ε^2*(7168*C/ε^2) = 7168*C := by field_simp
    have h1 : ε^2*Λ ≤ ε^2*L := mul_le_mul_of_nonneg_left hLΛ (by positivity)
    nlinarith [mul_le_mul_of_nonneg_left hc7168 (show (0:ℝ) ≤ ε^2 by positivity)]
  have hTt : T_C ≤ Real.exp L := by linarith
  have hKcap : (K:ℝ) ≤ Real.log (Real.exp L) / Real.log (Real.log (Real.exp L)) := by
    rw [Real.log_exp, hlogL, le_div_iff₀ hΛ0]
    nlinarith [mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hM1R hΛ0.le) hK0.le]
  obtain ⟨B, x₀, N, H, hBp, hBcard, hx₀t, hx₀8t, hwin, hsep, hNlow, hNup, hN1, hHb, hH1, hx₀H⟩ :=
    hsel (Real.exp L) hTt K hK2 hKcap
  rw [Real.log_exp] at hNlow hNup hHb
  have hx₀0 : (0:ℝ) < (x₀:ℝ) := lt_of_lt_of_le ht0 hx₀t
  have hN0 : (0:ℝ) < (N:ℝ) := by
    have h1 : (1:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN1
    linarith
  have hH1R : (1:ℝ) ≤ (H:ℝ) := by exact_mod_cast hH1
  have hPS : (K:ℝ)*Real.log ((K:ℝ)/2)/(28*L) ≤ pairSum B :=
    ms_pairSum_ge hBcard hK4 hH1 hwin hHb hL0 hlg0
  have hbigR := ms_hbig_aux h30 hexpΛ hH1R hK1R hK12 hHb
  have hKHR := ms_KH_aux hγ hcγ h30 hexpΛ hKL hHb
  refine ⟨B, x₀, N, H, K, hBp, hBcard, hK4, hwin, hsep, hN1, hH1,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- 4 ≤ x₀
    have h4 : (4:ℝ) ≤ (x₀:ℝ) := by linarith
    exact_mod_cast h4
  · -- Θ ≤ x₀
    linarith
  · -- hbig
    have hcast : ((8*(2*H)^(K+1) : ℕ):ℝ) ≤ (x₀:ℝ) := by push_cast; linarith
    exact_mod_cast hcast
  · -- hKH
    have h1 : γ*Real.exp L ≤ Real.exp L := by
      nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ 1-γ) ht0.le]
    have hcast : ((2*K*H : ℕ):ℝ) ≤ (x₀:ℝ) := by push_cast; linarith
    exact_mod_cast hcast
  · -- hlogK
    have h1 : ε*(Λ^2/4) ≤ ε*L := mul_le_mul_of_nonneg_left hLsq hε.le
    have h2 : 4*Λ ≤ ε*(Λ^2/4) := by
      nlinarith [mul_le_mul_of_nonneg_right hεΛ16 hΛ0.le]
    linarith [hlogKΛ]
  · -- 2KH ≤ γ x₀
    have h1 : γ*Real.exp L ≤ γ*(x₀:ℝ) := mul_le_mul_of_nonneg_left hx₀t hγ.le
    linarith
  · -- 2K/x₀ ≤ η
    have h1 : 2*(K:ℝ)/x₀ ≤ 2*L/Real.exp L :=
      ms_div_le_div (by positivity) (by linarith) ht0 hx₀t
    have hsqt : L^2/4 ≤ Real.exp L := by
      calc L^2/4 = (L/2)^2 := by ring
        _ ≤ Real.exp L := ms_div_pow_le_exp 2 hL0.le
    have h2 : 2*L/Real.exp L ≤ 2*L/(L^2/4) :=
      ms_div_le_div (by positivity) (le_refl _) (by positivity) hsqt
    have h3 : 2*L/(L^2/4) = 8/L := by
      field_simp
      ring
    have h4 : 8/L ≤ η := by
      rw [div_le_iff₀ hL0]
      have heq : η*(8/η) = 8 := by field_simp
      nlinarith [mul_le_mul_of_nonneg_left hcη hη.le, mul_le_mul_of_nonneg_left hLΛ hη.le]
    linarith [h3 ▸ h2]
  · -- pairSum lower bound
    exact le_trans (ms_tau_ge hΛ0 hL0 (by omega) hKlow hlg) hPS
  · -- main terms
    exact ms_main_aux hC hε h30 hL0 hK0 hN0 hlogKΛ hlg hεΛC hε2L hNlow hPS
  · -- error terms
    exact ms_err_aux hE hη h30 hcE hexpΛ hK6 hKL hx₀t

/-! ### The multiscale recursion -/

/-- The growing sequence of states: at stage `r` we have `n` with harmonic-type
pair-sum mass `A` and gap sum controlled by `A/(8C) + 3`. -/
lemma ms_grow {ε T_C : ℝ} (C : ℝ) (hC : 0 < C) (hε : 0 < ε)
    (hsel : ms_SelProp ε T_C) (n₀ : ℕ) :
    ∀ r : ℕ, 1 ≤ r → ∃ (n : ℕ) (A : ℝ), n ≠ 0 ∧ n₀ ≤ n ∧
      (∑ d ∈ n.divisors, ((d:ℝ))⁻¹ ≤ 2 - (1/2:ℝ)^r) ∧
      (∑ i ∈ Finset.Icc 1 r, 1/((i:ℝ)+12))/112 ≤ A ∧
      A ≤ pairSum n.divisors ∧
      gapSum n.divisors ≤ A/(8*C) + 3 - (1/2:ℝ)^r := by
  intro r hr
  induction r with
  | zero => omega
  | succ r ih =>
    rcases Nat.eq_zero_or_pos r with rfl | hr1
    · -- base case: a single scale
      obtain ⟨B, x₀, N, H, K, hBp, hBcard, hK4, hwin, hsep, hN1, hH1, hx₀4, hΘ,
          hbig, hKH, hlogK, hγb, hη2K, hPlow, hmain, herr⟩ :=
        ms_scale_setup C hC hε hsel 13 (by norm_num) (n₀:ℝ) 0 (1/8) 1
          (le_refl 0) (by norm_num) one_pos (le_refl 1)
      have hm0 : (∏ p ∈ B, p) ≠ 0 := os_prodB_ne_zero hBp
      have hBne : B.Nonempty := Finset.card_pos.mp (by omega)
      obtain ⟨p₀, hp₀⟩ := hBne
      have hn₀m : n₀ ≤ ∏ p ∈ B, p := by
        have h1 : n₀ ≤ x₀ := by exact_mod_cast hΘ
        have h3 : x₀ < p₀ := (hwin p₀ hp₀).1
        have h4 : p₀ ≤ ∏ p ∈ B, p := ms_le_prodB hBp hp₀
        omega
      have h2K : 2*B.card ≤ x₀ := by
        rw [hBcard]
        calc 2*K = 2*K*1 := (mul_one _).symm
          _ ≤ 2*K*H := Nat.mul_le_mul_left _ hH1
          _ ≤ x₀ := hKH
      have hσm : ∑ d ∈ (∏ p ∈ B, p).divisors, ((d:ℝ))⁻¹ ≤ 1 + 2*(K:ℝ)/x₀ := by
        have h := sum_inv_divisors_le hBp (fun p hp => (hwin p hp).1.le) h2K (by omega)
        rwa [hBcard] at h
      have hK2 : 2 ≤ K := by omega
      have hOS := oneScale_gapSum_le hBp hBcard hK2 hN1 hH1 hwin hsep hbig hKH hx₀4 hlogK
      have hBsub : B ⊆ (∏ p ∈ B, p).divisors := fun p hp =>
        Nat.mem_divisors.mpr ⟨Finset.dvd_prod_of_mem _ hp, hm0⟩
      have hPnn : 0 ≤ pairSum B := pairSum_nonneg B
      simp only [zero_add, pow_one]
      refine ⟨∏ p ∈ B, p, pairSum B, hm0, hn₀m, ?_, ?_, ms_pairSum_mono hBsub, ?_⟩
      · -- σ invariant
        linarith
      · -- A lower bound
        have h13 : ((1:ℕ):ℝ) + 12 = 13 := by norm_num
        rw [Finset.Icc_self, Finset.sum_singleton, h13]
        norm_num at hPlow
        linarith
      · -- gap sum invariant
        have hhalf : pairSum B/(16*C) = (pairSum B/(8*C))/2 := by ring
        have hPC : 0 ≤ pairSum B/(8*C) := by positivity
        norm_num at herr
        linarith [hOS, hmain, herr, hPC]
    · -- inductive step
      obtain ⟨n, A, hn0, hnn₀, hσ, hAlow, hAup, hG⟩ := ih hr1
      obtain ⟨δ, hδ0, hδ1, hδ⟩ := exists_min_log_gap n hn0
      have hGnn : 0 ≤ gapSum n.divisors := gapSum_nonneg _
      have hE0 : 0 ≤ 2*gapSum n.divisors + 16/δ :=
        add_nonneg (by linarith) (div_nonneg (by norm_num) hδ0.le)
      obtain ⟨B, x₀, N, H, K, hBp, hBcard, hK4, hwin, hsep, hN1, hH1, hx₀4, hΘ,
          hbig, hKH, hlogK, hγb, hη2K, hPlow, hmain, herr⟩ :=
        ms_scale_setup C hC hε hsel (r+13) (by omega) (4*(n:ℝ))
          (2*gapSum n.divisors + 16/δ) ((1/2:ℝ)^(r+2)) δ hE0 (by positivity) hδ0 hδ1
      have hm0 : (∏ p ∈ B, p) ≠ 0 := os_prodB_ne_zero hBp
      have hnm0 : n * ∏ p ∈ B, p ≠ 0 := mul_ne_zero hn0 hm0
      have hnx₀ : n ≤ x₀ := by
        have h1 : (n:ℝ) ≤ (x₀:ℝ) := by
          have h2 : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
          linarith
        exact_mod_cast h1
      have hngt : ∀ p ∈ B, n < p := fun p hp => lt_of_le_of_lt hnx₀ (hwin p hp).1
      have hcop : n.Coprime (∏ p ∈ B, p) :=
        ss_coprime_prod hn0 hBp (fun p hp => (hwin p hp).1) hnx₀
      have hp0 : (0:ℝ) < (1/2:ℝ)^r := by positivity
      have hpow1 : ((1/2:ℝ))^(r+1) = ((1/2:ℝ))^r/2 := by rw [pow_succ]; ring
      have hpow2 : ((1/2:ℝ))^(r+2) = ((1/2:ℝ))^r/4 := by rw [pow_succ, pow_succ]; ring
      have hp1 : ((1/2:ℝ))^r ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
      have hσ2 : ∑ e ∈ n.divisors, ((e:ℝ))⁻¹ ≤ 2 := by linarith
      have hK2 : 2 ≤ K := by omega
      have hSS := scaleStep_gapSum_le hn0 hBp hBcard hK2 hN1 hH1 hx₀4 hwin hsep
        hbig hKH hlogK hδ0 hδ1 hδ hσ2 hΘ hγb
      -- σ invariant for the new state
      have h2K : 2*B.card ≤ x₀ := by
        rw [hBcard]
        calc 2*K = 2*K*1 := (mul_one _).symm
          _ ≤ 2*K*H := Nat.mul_le_mul_left _ hH1
          _ ≤ x₀ := hKH
      have hσm : ∑ d ∈ (∏ p ∈ B, p).divisors, ((d:ℝ))⁻¹ ≤ 1 + 2*(K:ℝ)/x₀ := by
        have h := sum_inv_divisors_le hBp (fun p hp => (hwin p hp).1.le) h2K (by omega)
        rwa [hBcard] at h
      have hσm_nn : 0 ≤ ∑ d ∈ (∏ p ∈ B, p).divisors, ((d:ℝ))⁻¹ :=
        Finset.sum_nonneg fun d _ => by positivity
      have hσ' : ∑ d ∈ (n * ∏ p ∈ B, p).divisors, ((d:ℝ))⁻¹ ≤ 2 - (1/2:ℝ)^(r+1) := by
        rw [sum_inv_divisors_mul hcop hn0 hm0]
        have hσm' : ∑ d ∈ (∏ p ∈ B, p).divisors, ((d:ℝ))⁻¹ ≤ 1 + ((1/2:ℝ))^r/4 := by
          linarith
        have hprod := mul_le_mul hσ hσm' hσm_nn (by linarith)
        have hfin : (2 - (1/2:ℝ)^r)*(1 + (1/2:ℝ)^r/4) ≤ 2 - (1/2:ℝ)^r/2 := by
          nlinarith [sq_nonneg ((1/2:ℝ)^r)]
        rw [hpow1]
        linarith
      have hadd := ms_pairSum_add_le hn0 hBp hngt
      have hPnn : 0 ≤ pairSum B := pairSum_nonneg B
      refine ⟨n * ∏ p ∈ B, p, A + pairSum B, hnm0, ?_, hσ', ?_, ?_, ?_⟩
      · -- n₀ ≤ n·m
        exact le_trans hnn₀ (Nat.le_mul_of_pos_right n (Nat.pos_of_ne_zero hm0))
      · -- A lower bound
        rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ r+1), add_div]
        have hkey : 1/(((r+1:ℕ):ℝ)+12)/112 ≤ pairSum B := by
          have heq : 1/(((r+1:ℕ):ℝ)+12)/112 = 1/(112*(((r+13:ℕ)):ℝ)) := by
            push_cast
            rw [div_div]
            ring_nf
          rw [heq]
          exact hPlow
        linarith [hAlow, hkey]
      · -- A upper bound
        linarith [hAup, hadd]
      · -- gap sum invariant
        have hx₀R : (0:ℝ) < (x₀:ℝ) := by
          have h1 : 0 < x₀ := by omega
          exact_mod_cast h1
        have hbr : 16*(K:ℝ)/(δ*(x₀:ℝ)) = 16/δ*(K:ℝ)/(x₀:ℝ) := by
          rw [div_eq_mul_inv, mul_inv]
          ring
        rw [hbr] at hSS
        have hexp : gapSum n.divisors * (1 + 2*(K:ℝ)/(x₀:ℝ))
            = gapSum n.divisors + 2*gapSum n.divisors*((K:ℝ)/(x₀:ℝ)) := by ring
        rw [hexp] at hSS
        have hEexp : (2*gapSum n.divisors + 16/δ)*(K:ℝ)/(x₀:ℝ)
            = 2*gapSum n.divisors*((K:ℝ)/(x₀:ℝ)) + 16/δ*(K:ℝ)/(x₀:ℝ) := by ring
        rw [hEexp] at herr
        have hkey : gapSum ((n * ∏ p ∈ B, p).divisors)
            ≤ gapSum n.divisors + (1/2:ℝ)^(r+2) + pairSum B/(8*C) := by
          linarith [hSS, herr, hmain]
        have hsplit : (A + pairSum B)/(8*C) = A/(8*C) + pairSum B/(8*C) := by ring
        linarith [hkey, hG, hp0, hpow1, hpow2, hsplit]

/-! ### The export: divisor pair sums beat gap sums by any constant factor -/

/-- **Multiscale construction.**  For every `C > 0` and every threshold `n₀` there is an
`n ≥ n₀` with `C * (1 + S(n)) < T(n)`, where `S` is the sum of reciprocals of consecutive
divisor gaps and `T` the sum of reciprocals of all divisor differences. -/
theorem exists_ratio_large :
    ∀ C : ℝ, 0 < C → ∀ n₀ : ℕ, ∃ n : ℕ, n₀ ≤ n ∧ n ≠ 0 ∧
      C * (1 + gapSum n.divisors) < pairSum n.divisors := by
  intro C hC n₀
  obtain ⟨ε, hε, hε1, T_C, hTC, hsel⟩ := separated_primes_selection
  -- choose a stage r whose harmonic mass exceeds 560·C
  obtain ⟨r, hr1, hSr⟩ :
      ∃ r : ℕ, 1 ≤ r ∧ 560*C ≤ ∑ i ∈ Finset.Icc 1 r, 1/((i:ℝ)+12) := by
    obtain ⟨R, hRgt⟩ := exists_nat_gt (Real.exp (7280*C))
    refine ⟨R + 1, by omega, ?_⟩
    have hexpR : Real.exp (7280*C) ≤ ((R+1:ℕ):ℝ) + 1 := by push_cast; linarith
    have h2 : 7280*C ≤ Real.log (((R+1:ℕ):ℝ)+1) := by
      have h3 := Real.log_le_log (Real.exp_pos _) hexpR
      rwa [Real.log_exp] at h3
    have h4 := log_le_sum_inv (R+1)
    have h5 : ∑ i ∈ Finset.Icc 1 (R+1), ((i:ℝ))⁻¹
        ≤ 13 * ∑ i ∈ Finset.Icc 1 (R+1), 1/((i:ℝ)+12) := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro i hi
      have hi1 : 1 ≤ i := (Finset.mem_Icc.mp hi).1
      have hiR : (1:ℝ) ≤ (i:ℝ) := by exact_mod_cast hi1
      rw [mul_one_div, inv_eq_one_div, div_le_div_iff₀ (by linarith) (by linarith)]
      linarith
    linarith
  obtain ⟨n, A, hn0, hnn₀, hσ, hAlow, hAup, hG⟩ := ms_grow C hC hε hsel n₀ r hr1
  refine ⟨n, hnn₀, hn0, ?_⟩
  have hA5C : 5*C ≤ A := by linarith
  have hp0 : (0:ℝ) < (1/2:ℝ)^r := by positivity
  have hCne : C ≠ 0 := hC.ne'
  have h1 : C*(1 + gapSum n.divisors) ≤ C*(4 + A/(8*C)) := by
    apply mul_le_mul_of_nonneg_left _ hC.le
    linarith
  have hCA : C * (A/(8*C)) = A/8 := by
    field_simp
  have h2 : C*(4 + A/(8*C)) = 4*C + C*(A/(8*C)) := by ring
  have h3 : 4*C + A/8 < A := by linarith
  linarith [h1, h2, hCA, h3, hAup]

end Erdos884
end

/-! Flattened from Erdos884/Main884.lean. -/
section

/-!
# Erdős Problem 884 — the disproof (final statement)

Combining the multiscale construction (`exists_ratio_large`) with the bridge to the
official formal-conjectures statement (`Bridge884`), we conclude:

  it is NOT the case that
    ∑_{d < e, d,e ∣ n} 1/(e - d)  =O  1 + ∑_{consecutive divisors d < e of n} 1/(e - d)

as functions of `n → ∞`, i.e. Erdős problem #884 has a negative answer (Daniel Larsen).

In the ≪ notation of formal-conjectures, this refutes
  `sumDivisorInvPairwiseDifference ≪ 1 + sumDivisorInvConsecutiveDifference`.
-/

namespace Erdos884

theorem erdos_884_disproof :
    ¬ (sumDivisorInvPairwiseDifference =O[Filter.atTop] (1 + sumDivisorInvConsecutiveDifference)) := by
  intro h
  obtain ⟨c, hc⟩ := Asymptotics.isBigO_iff.mp h
  obtain ⟨n₀, hn₀⟩ := Filter.eventually_atTop.mp hc
  obtain ⟨n, hn_ge, hn_ne, hlt⟩ :=
    exists_ratio_large (max c 1) (lt_of_lt_of_le one_pos (le_max_right c 1)) n₀
  have hb := hn₀ n hn_ge
  have hgap : (0 : ℝ) ≤ gapSum n.divisors := gapSum_nonneg _
  have hT : ‖sumDivisorInvPairwiseDifference n‖ = pairSum n.divisors := by
    rw [Real.norm_of_nonneg (sumDivisorInvPairwise_nonneg n hn_ne),
        sumDivisorInvPairwiseDifference_eq hn_ne]
  have hS : ‖(1 + sumDivisorInvConsecutiveDifference) n‖ = 1 + gapSum n.divisors := by
    have happ : (1 + sumDivisorInvConsecutiveDifference) n
        = 1 + sumDivisorInvConsecutiveDifference n := by
      simp [Pi.add_apply, Pi.one_apply]
    rw [happ, sumDivisorInvConsecutiveDifference_eq hn_ne,
        Real.norm_of_nonneg (by linarith)]
  rw [hT, hS] at hb
  have hchain : pairSum n.divisors ≤ max c 1 * (1 + gapSum n.divisors) :=
    hb.trans (mul_le_mul_of_nonneg_right (le_max_left c 1) (by linarith))
  exact absurd hchain (not_le.mpr hlt)

/--
The disproof in the exact shape of the google-deepmind/formal-conjectures statement
`Erdos884.erdos_884 : answer(False) ↔ Erdos884Prop`.

There `answer(False)` reduces to `False`, and `Erdos884Prop` is
`sumDivisorInvPairwiseDifference ≪ 1 + sumDivisorInvConsecutiveDifference`, where `≪` is
their notation for `Asymptotics.IsBigO Filter.atTop`. Unfolding both, that statement is
exactly the `↔` below, discharged by `erdos_884_disproof`. This is the formal proof
referenced by the `@[formal_proof using lean4 at …]` attribute on `erdos_884`.
-/
theorem erdos_884_iff_false :
    False ↔ sumDivisorInvPairwiseDifference =O[Filter.atTop]
      (1 + sumDivisorInvConsecutiveDifference) :=
  iff_of_false not_false erdos_884_disproof

end Erdos884
end

namespace Submissions.Erdos884Disproof.Full

theorem proof :
    ¬ (Erdos884.sumDivisorInvPairwiseDifference =O[Filter.atTop]
      (1 + Erdos884.sumDivisorInvConsecutiveDifference)) :=
  Erdos884.erdos_884_disproof

#print axioms proof

end Submissions.Erdos884Disproof.Full
