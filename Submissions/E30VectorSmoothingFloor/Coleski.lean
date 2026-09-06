import Mathlib


open Real intervalIntegral

namespace Erdos30CDF

theorem integral_sqrt_mul_one_sub :
    (∫ u : ℝ in 0..1, Real.sqrt (u * (1-u))) = Real.pi / 8 := by
  have hpoint (u : ℝ) :
      Real.sqrt (1 - (2*u-1)^2) = 2 * Real.sqrt (u*(1-u)) := by
    have heq : 1 - (2*u-1)^2 = 4 * (u*(1-u)) := by ring
    rw [heq, Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 4)]
    norm_num
  have hchange := intervalIntegral.integral_comp_mul_add
    (fun x : ℝ => Real.sqrt (1-x^2)) (a := (0:ℝ)) (b := 1)
    (c := (2:ℝ)) (by norm_num) (-1)
  norm_num at hchange
  simp only [show ∀ x : ℝ, 2*x + -1 = 2*x-1 by intro x; ring,
    hpoint, integral_const_mul] at hchange
  rw [integral_sqrt_one_sub_sq] at hchange
  linarith


/-- The CDF substitution step for continuously differentiable CDFs.
Histogram CDFs require a separate piecewise/absolute-continuity transfer. -/
theorem integral_density_sqrt_cdf
    (F f : ℝ → ℝ)
    (hderiv : ∀ t ∈ Set.uIcc (0:ℝ) 1, HasDerivAt F (f t) t)
    (hf : ContinuousOn f (Set.uIcc (0:ℝ) 1))
    (hzero : F 0 = 0) (hone : F 1 = 1) :
    (∫ t : ℝ in 0..1, f t * Real.sqrt (F t * (1-F t))) = Real.pi / 8 := by
  have h := intervalIntegral.integral_comp_mul_deriv hderiv hf
    (show Continuous (fun u : ℝ => Real.sqrt (u*(1-u))) by fun_prop)
  simp only [Function.comp_apply, hzero, hone] at h
  rw [integral_sqrt_mul_one_sub] at h
  simpa only [mul_comm] using h


/-- Exact affine-bin substitution, including zero or negative bin increments. -/
theorem affine_bin_substitution (g : ℝ → ℝ) (hg : Continuous g) (a b : ℝ) :
    (∫ t : ℝ in 0..1, (b-a) * g (a+(b-a)*t)) = ∫ u in a..b, g u := by
  have h := intervalIntegral.integral_comp_mul_deriv
    (a := (0:ℝ)) (b := (1:ℝ))
    (f := fun t : ℝ => a+(b-a)*t) (f' := fun _ => b-a)
    (fun t _ => by simpa using (((hasDerivAt_id t).const_mul (b-a)).const_add a))
    (by fun_prop) hg
  simpa only [Function.comp_apply, mul_zero, add_zero, mul_one,
    add_sub_cancel, mul_comm] using h

/-- The exact histogram-CDF chain rule, obtained by telescoping oriented integrals.
No monotonicity or nonzero bin-mass assumption is required. -/
theorem histogram_cdf_substitution (c : ℕ → ℝ) (n : ℕ)
    (hzero : c 0 = 0) (hone : c n = 1) :
    (∑ i ∈ Finset.range n, ∫ t : ℝ in 0..1,
      (c (i+1)-c i) * Real.sqrt
        ((c i+(c (i+1)-c i)*t) * (1-(c i+(c (i+1)-c i)*t)))) = Real.pi / 8 := by
  have hg : Continuous (fun u : ℝ => Real.sqrt (u*(1-u))) := by fun_prop
  simp_rw [affine_bin_substitution _ hg]
  rw [intervalIntegral.sum_integral_adjacent_intervals
    (fun i hi => hg.intervalIntegrable (c i) (c (i+1)))]
  rw [hzero, hone, integral_sqrt_mul_one_sub]


theorem interval_integral_sq_le (g : ℝ → ℝ) (hg : Continuous g) :
    (∫ t : ℝ in 0..1, g t)^2 ≤ ∫ t : ℝ in 0..1, (g t)^2 := by
  let I : ℝ := ∫ t : ℝ in 0..1, g t
  have hnonneg : 0 ≤ ∫ t : ℝ in 0..1, (g t-I)^2 :=
    intervalIntegral.integral_nonneg_of_forall (by norm_num) (fun t => sq_nonneg _)
  have heq : (fun t : ℝ => (g t-I)^2) = (fun t => (g t)^2 - (2*I)*g t + I^2) := by
    funext t; ring
  have hsq : IntervalIntegrable (fun t : ℝ => (g t)^2) MeasureTheory.volume 0 1 :=
    (show Continuous (fun t : ℝ => (g t)^2) by fun_prop).intervalIntegrable _ _
  have hmul : IntervalIntegrable (fun t : ℝ => (2*I)*g t) MeasureTheory.volume 0 1 :=
    (show Continuous (fun t : ℝ => (2*I)*g t) by fun_prop).intervalIntegrable _ _
  have hconst : IntervalIntegrable (fun _ : ℝ => I^2) MeasureTheory.volume 0 1 :=
    continuous_const.intervalIntegrable _ _
  rw [heq, intervalIntegral.integral_add (hsq.sub hmul) hconst,
    intervalIntegral.integral_sub hsq hmul,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const] at hnonneg
  dsimp [I] at hnonneg
  norm_num at hnonneg
  nlinarith


theorem bin_sqrt_integral_sq_le (a b : ℝ) (ha : 0 ≤ a ∧ a ≤ 1)
    (hb : 0 ≤ b ∧ b ≤ 1) :
    (∫ t : ℝ in 0..1, Real.sqrt ((a+(b-a)*t)*(1-(a+(b-a)*t))))^2 ≤
      ∫ t : ℝ in 0..1, (a+(b-a)*t)*(1-(a+(b-a)*t)) := by
  have h := interval_integral_sq_le
    (fun t : ℝ => Real.sqrt ((a+(b-a)*t)*(1-(a+(b-a)*t)))) (by fun_prop)
  convert h using 1
  apply intervalIntegral.integral_congr
  intro t ht
  rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] at ht
  have hlo : 0 ≤ a+(b-a)*t := by
    nlinarith [mul_nonneg (sub_nonneg.mpr ht.2) ha.1, mul_nonneg ht.1 hb.1]
  have hhi : 0 ≤ 1-(a+(b-a)*t) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr ht.2) (sub_nonneg.mpr ha.2),
      mul_nonneg ht.1 (sub_nonneg.mpr hb.2)]
  exact (Real.sq_sqrt (mul_nonneg hlo hhi)).symm


/-- Scalar histogram Gini-energy inequality in cumulative-bin coordinates. -/
theorem histogram_gini_energy (c : ℕ → ℝ) (n : ℕ)
    (hzero : c 0 = 0) (hone : c n = 1)
    (hbins : ∀ i ≤ n, 0 ≤ c i ∧ c i ≤ 1) :
    Real.pi^2 ≤ 64 * (∑ i ∈ Finset.range n, (c (i+1)-c i)^2) *
      (∑ i ∈ Finset.range n, ∫ t : ℝ in 0..1,
        (c i+(c (i+1)-c i)*t)*(1-(c i+(c (i+1)-c i)*t))) := by
  let p : ℕ → ℝ := fun i => c (i+1)-c i
  let I : ℕ → ℝ := fun i => ∫ t : ℝ in 0..1,
    Real.sqrt ((c i+p i*t)*(1-(c i+p i*t)))
  let J : ℕ → ℝ := fun i => ∫ t : ℝ in 0..1,
    (c i+p i*t)*(1-(c i+p i*t))
  have hchain : (∑ i ∈ Finset.range n, p i * I i) = Real.pi/8 := by
    simpa only [p, I, intervalIntegral.integral_const_mul] using
      histogram_cdf_substitution c n hzero hone
  have hbin : ∀ i ∈ Finset.range n, (I i)^2 ≤ J i := by
    intro i hi
    have hin : i < n := Finset.mem_range.mp hi
    exact bin_sqrt_integral_sq_le (c i) (c (i+1))
      (hbins i (Nat.le_of_lt hin)) (hbins (i+1) hin)
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.range n) p I
  have hsum := Finset.sum_le_sum hbin
  have hpos : 0 ≤ ∑ i ∈ Finset.range n, (p i)^2 :=
    Finset.sum_nonneg (fun i hi => sq_nonneg _)
  have hbound := mul_le_mul_of_nonneg_left hsum hpos
  rw [hchain] at hcs
  change Real.pi^2 ≤ 64 * (∑ i ∈ Finset.range n, (p i)^2) *
    (∑ i ∈ Finset.range n, J i)
  nlinarith


theorem histogram_scaled_gini_energy (c : ℕ → ℝ) (n : ℕ) (m : ℝ)
    (hm : 0 < m) (hzero : c 0 = 0) (hone : c n = 1)
    (hbins : ∀ i ≤ n, 0 ≤ c i ∧ c i ≤ 1) :
    Real.pi^2/32 ≤
      (m * ∑ i ∈ Finset.range n, (c (i+1)-c i)^2) *
      ((2/m) * ∑ i ∈ Finset.range n, ∫ t : ℝ in 0..1,
        (c i+(c (i+1)-c i)*t)*(1-(c i+(c (i+1)-c i)*t))) := by
  have h := histogram_gini_energy c n hzero hone hbins
  have heq (x y : ℝ) : (m*x)*((2/m)*y) = 2*x*y := by
    field_simp [ne_of_gt hm]
  rw [heq]
  nlinarith


/-- The scalar Gini bound directly for a nonnegative normalized histogram kernel. -/
theorem kernel_histogram_gini_energy (p : ℕ → ℝ) (n : ℕ)
    (hp : ∀ i < n, 0 ≤ p i)
    (hpsum : (∑ i ∈ Finset.range n, p i) = 1) :
    Real.pi^2 ≤ 64 * (∑ i ∈ Finset.range n, (p i)^2) *
      (∑ i ∈ Finset.range n, ∫ t : ℝ in 0..1,
        ((∑ j ∈ Finset.range i, p j)+p i*t) *
        (1-((∑ j ∈ Finset.range i, p j)+p i*t))) := by
  let c : ℕ → ℝ := fun i => ∑ j ∈ Finset.range i, p j
  have hzero : c 0 = 0 := by simp [c]
  have hone : c n = 1 := hpsum
  have hbins : ∀ i ≤ n, 0 ≤ c i ∧ c i ≤ 1 := by
    intro i hi
    constructor
    · exact Finset.sum_nonneg (fun j hj => hp j (lt_of_lt_of_le (Finset.mem_range.mp hj) hi))
    · calc
        c i ≤ c n := Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.range_mono hi) (fun j hj _ => hp j (Finset.mem_range.mp hj))
        _ = 1 := hone
  have hdiff (i : ℕ) : c (i+1)-c i = p i := by
    simp [c, Finset.sum_range_succ]
  have h := histogram_gini_energy c n hzero hone hbins
  simpa only [hdiff, c] using h


end Erdos30CDF

namespace E30Floor
open scoped BigOperators

/-- The boundary covering condition, after summation, bounds its energy
by a discrete survival-function moment. No sign condition on w is needed. -/
theorem boundary_completion {R J : Type*} [Fintype R] [Fintype J]
    (mix : R → ℝ) (w h : R → J → ℝ)
    (hmix : ∀ r, 0 ≤ mix r) (hnorm : ∑ r, mix r = 1)
    (hcover : 0 ≤ ∑ r, mix r * ∑ j, (1 - h r j) * (w r j - 1)) :
    (Fintype.card J : ℝ) ≤
      (∑ r, mix r * ∑ j, (w r j)^2) + (∑ r, mix r * ∑ j, (h r j)^2) := by
  have hs : 0 ≤ ∑ r, mix r * ∑ j, (w r j - 1 + h r j)^2 := by
    exact Finset.sum_nonneg fun r _ => mul_nonneg (hmix r)
      (Finset.sum_nonneg fun j _ => sq_nonneg _)
  have hid : (∑ r, mix r * ∑ j, (w r j)^2) +
      (∑ r, mix r * ∑ j, (h r j)^2) - (Fintype.card J : ℝ) =
      (∑ r, mix r * ∑ j, (w r j - 1 + h r j)^2) +
        2 * (∑ r, mix r * ∑ j, (1 - h r j) * (w r j - 1)) := by
    have point : ∀ r j, (w r j - 1 + h r j)^2 +
        2 * ((1 - h r j) * (w r j - 1)) = (w r j)^2 + (h r j)^2 - 1 := by
      intros; ring
    calc
      _ = ∑ r, mix r * ∑ j, ((w r j)^2 + (h r j)^2 - 1) := by
        simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_const,
          Finset.card_univ, nsmul_eq_mul, mul_one, mul_sub, mul_add]
        rw [← Finset.sum_mul, hnorm]
        ring
      _ = ∑ r, mix r * ∑ j, ((w r j - 1 + h r j)^2 +
          2 * ((1 - h r j) * (w r j - 1))) := by
        apply Finset.sum_congr rfl
        intro r hr
        congr 1
        apply Finset.sum_congr rfl
        intro j hj
        exact (point r j).symm
      _ = _ := by
        simp only [Finset.sum_add_distrib, ← Finset.mul_sum, mul_add]
        ring_nf
        simp only [Finset.sum_mul]
  linarith

/-- A common product floor survives arbitrary nonnegative mixing. -/
theorem weighted_product_floor {R : Type*} [Fintype R]
    (mix e d : R → ℝ) (c : ℝ)
    (hmix : ∀ r, 0 ≤ mix r) (hnorm : ∑ r, mix r = 1)
    (he : ∀ r, 0 ≤ e r) (hd : ∀ r, 0 ≤ d r)
    (hc : 0 ≤ c) (hpoint : ∀ r, c^2 ≤ e r * d r) :
    c^2 ≤ (∑ r, mix r * e r) * (∑ r, mix r * d r) := by
  have hlo : c ≤ ∑ r, mix r * Real.sqrt (e r * d r) := by
    calc
      c = ∑ r, mix r * c := by rw [← Finset.sum_mul, hnorm, one_mul]
      _ ≤ _ := Finset.sum_le_sum fun r _ =>
        mul_le_mul_of_nonneg_left (Real.le_sqrt_of_sq_le (hpoint r)) (hmix r)
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset R)
    (fun r => Real.sqrt (mix r) * Real.sqrt (e r))
    (fun r => Real.sqrt (mix r) * Real.sqrt (d r))
  have hp (r : R) :
      (Real.sqrt (mix r) * Real.sqrt (e r)) *
        (Real.sqrt (mix r) * Real.sqrt (d r)) =
          mix r * Real.sqrt (e r * d r) := by
    rw [mul_mul_mul_comm, Real.mul_self_sqrt (hmix r), Real.sqrt_mul (he r)]
  simp_rw [hp, mul_pow, Real.sq_sqrt (hmix _), Real.sq_sqrt (he _),
    Real.sq_sqrt (hd _)] at hcs
  nlinarith

/-- Final finite mixing step, ready for the scalar CDF bound and boundary bound. -/
theorem floor_assembly {R : Type*} [Fintype R]
    (mix e d : R → ℝ) (m b : ℝ)
    (hmix : ∀ r, 0 ≤ mix r) (hnorm : ∑ r, mix r = 1)
    (he : ∀ r, 0 ≤ e r) (hd : ∀ r, 0 ≤ d r) (hm : 0 ≤ m)
    (hscalar : ∀ r, Real.pi^2 ≤ (32*m*e r) * d r)
    (hboundary : (∑ r, mix r * d r) ≤ b) :
    Real.pi^2 ≤ 32 * (m * ∑ r, mix r * e r) * b := by
  have h := weighted_product_floor mix (fun r => 32*m*e r) d Real.pi
    hmix hnorm (fun r => mul_nonneg (mul_nonneg (by norm_num) hm) (he r)) hd Real.pi_pos.le hscalar
  have hrewrite : (∑ r, mix r * (32*m*e r)) =
      32*m*(∑ r, mix r * e r) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r hr
    ring
  rw [hrewrite] at h
  have hnonneg : 0 ≤ 32*m*(∑ r, mix r * e r) := by
    apply mul_nonneg (by positivity)
    exact Finset.sum_nonneg fun r _ => mul_nonneg (hmix r) (he r)
  have hup := mul_le_mul_of_nonneg_left hboundary hnonneg
  nlinarith

end E30Floor

namespace E30Floor
open scoped BigOperators

theorem bin_moment (c p : ℝ) :
    (∫ t : ℝ in 0..1, (c+p*t)*(1-(c+p*t))) =
      (c+p/2)*(1-(c+p/2)) - p^2/12 := by
  let P : ℝ → ℝ := fun t => c*(1-c)*t + p*(1-2*c)*t^2/2 - p^2*t^3/3
  have hd (t : ℝ) : HasDerivAt P ((c+p*t)*(1-(c+p*t))) t := by
    convert ((((hasDerivAt_id t).const_mul (c*(1-c))).add
      (((hasDerivAt_pow 2 t).const_mul (p*(1-2*c))).div_const 2)).sub
      (((hasDerivAt_pow 3 t).const_mul (p^2)).div_const 3)) using 1 <;> first | rfl | (dsimp [P]; ring)
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := (0:ℝ)) (b := 1) (fun t ht => hd t)
    (show IntervalIntegrable (fun t : ℝ => (c+p*t)*(1-(c+p*t))) MeasureTheory.volume 0 1 from
      (by fun_prop : Continuous (fun t : ℝ => (c+p*t)*(1-(c+p*t)))).intervalIntegrable 0 1)
  rw [h]
  dsimp [P]
  ring


theorem bin_moment_sum_le (c p : ℕ → ℝ) (m : ℕ)
    (hmean : (∑ i ∈ Finset.range m, (1-c i-p i/2)) = (m : ℝ)/2) :
    (∑ i ∈ Finset.range m, ∫ t : ℝ in 0..1,
      (c i+p i*t)*(1-(c i+p i*t))) ≤
      (m : ℝ)/2 - ∑ i ∈ Finset.range m, (1-c i-p i/2)^2 := by
  calc
    _ ≤ ∑ i ∈ Finset.range m, ((1-c i-p i/2) - (1-c i-p i/2)^2) := by
      apply Finset.sum_le_sum
      intro i hi
      rw [bin_moment]
      nlinarith [sq_nonneg (p i)]
    _ = _ := by rw [Finset.sum_sub_distrib, hmean]

end E30Floor

namespace E30Boundary
open scoped BigOperators

lemma shifted_sum (n i : ℕ) (v : ℕ → ℝ) (hv : ∀ j, n ≤ j → v j = 0) :
    (∑ q ∈ Finset.range n, v (q+i)) =
      ∑ j ∈ Finset.range n, if i ≤ j then v j else 0 := by
  classical
  calc
    (∑ q ∈ Finset.range n, v (q+i)) =
        ∑ q ∈ (Finset.range n).filter (fun q => q+i < n), v (q+i) := by
      symm
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro q hq hnot
      apply hv
      simp only [Finset.mem_filter, hq, true_and, not_lt] at hnot
      exact hnot
    _ = ∑ j ∈ (Finset.range n).filter (fun j => i≤j), v j := by
      apply Finset.sum_bij (fun q _ => q+i)
      · intro q hq
        simp only [Finset.mem_filter, Finset.mem_range] at hq ⊢
        omega
      · intro a ha b hb hab
        omega
      · intro j hj
        simp only [Finset.mem_filter, Finset.mem_range] at hj
        refine ⟨j-i, ?_, ?_⟩
        · simp only [Finset.mem_filter, Finset.mem_range]
          omega
        · omega
      · intro q hq
        rfl
    _ = _ := Finset.sum_filter _ _

lemma convolution_sum (n m : ℕ) (p v : ℕ → ℝ)
    (hv : ∀ j, n ≤ j → v j = 0) :
    (∑ q ∈ Finset.range n, ∑ i ∈ Finset.range m, p i * v (q+i)) =
    ∑ j ∈ Finset.range n, (∑ i ∈ Finset.range m, if i≤j then p i else 0) * v j := by
  classical
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, shifted_sum n _ v hv]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  split_ifs  <;> simp

lemma diagonal_sum (n i : ℕ) (v : ℕ → ℝ)
    (hv : ∀ j, n ≤ j → v j = 0) :
    (∑ j ∈ Finset.range n, if i=j then v j else 0) = v i := by
  classical
  by_cases hi : i < n
  · simp [hi]
  · simp [hi, hv i (by omega)]

noncomputable def cdfCoeff (m : ℕ) (p : ℕ → ℝ) (j : ℕ) : ℝ :=
  ∑ i ∈ Finset.range m, if i < j then p i else if i=j then p i/2 else 0

lemma cdf_identity (n m : ℕ) (p v : ℕ → ℝ)
    (hv : ∀ j, n ≤ j → v j = 0) :
    (∑ q ∈ Finset.range n, ∑ i ∈ Finset.range m, p i * v (q+i)) -
      (∑ i ∈ Finset.range m, p i*v i)/2 =
    ∑ j ∈ Finset.range n, cdfCoeff m p j * v j := by
  classical
  have hd : (∑ j ∈ Finset.range n,
      ∑ i ∈ Finset.range m, if i=j then p i*v j else 0) =
        ∑ i ∈ Finset.range m, p i*v i := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    have he : (∑ j ∈ Finset.range n, if i=j then p i*v j else 0) =
        p i * ∑ j ∈ Finset.range n, if i=j then v j else 0 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      split_ifs  <;> simp
    rw [he, diagonal_sum n i v hv]
  rw [convolution_sum n m p v hv, ← hd, Finset.sum_div, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  rw [cdfCoeff, Finset.sum_mul, Finset.sum_mul, Finset.sum_div,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases hij : i < j
  · simp [hij, Nat.le_of_lt hij, Nat.ne_of_lt hij]
  · by_cases heq : i=j
    · subst i
      simp
      ring
    · simp [hij, heq, show ¬ i≤j by omega]

lemma mixed_cdf_nonneg {R n m : ℕ} (hn : 0 < n)
    (mix : Fin R → ℝ) (p v : Fin R → ℕ → ℝ)
    (hv : ∀ r j, n ≤ j → v r j = 0)
    (hcover : ∀ q < n, 0 ≤ ∑ r, mix r *
      ∑ i ∈ Finset.range m, p r i * v r (q+i)) :
    0 ≤ ∑ r, mix r * ∑ j ∈ Finset.range n, cdfCoeff m (p r) j * v r j := by
  classical
  let C : ℕ → ℝ := fun q => ∑ r, mix r *
      ∑ i ∈ Finset.range m, p r i * v r (q+i)
  have hC : ∀ q < n, 0 ≤ C q := hcover
  have hsum : C 0 ≤ ∑ q ∈ Finset.range n, C q := by
    apply Finset.single_le_sum
    · intro q hq
      exact hC q (Finset.mem_range.mp hq)
    · exact Finset.mem_range.mpr hn
  have hid : (∑ r, mix r * ∑ j ∈ Finset.range n, cdfCoeff m (p r) j * v r j) =
      (∑ q ∈ Finset.range n, C q) - C 0/2 := by
    simp_rw [← cdf_identity n m _ _ (hv _), mul_sub, ← mul_div_assoc]
    rw [Finset.sum_sub_distrib, ← Finset.sum_div]
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    simp [C, Finset.mul_sum]
  rw [hid]
  have hzero := hC 0 hn
  linarith

lemma normalized_cover_deviation {R m : ℕ}
    (mix : Fin R → ℝ) (p w : Fin R → ℕ → ℝ)
    (hmix : ∑ r, mix r = 1)
    (hp : ∀ r, ∑ i ∈ Finset.range m, p r i = 1)
    (q : ℕ)
    (hc : 1 ≤ ∑ r, mix r * ∑ i ∈ Finset.range m, p r i*w r (q+i)) :
    0 ≤ ∑ r, mix r * ∑ i ∈ Finset.range m, p r i*(w r (q+i)-1) := by
  have he : (∑ r, mix r * ∑ i ∈ Finset.range m, p r i*(w r (q+i)-1)) =
      (∑ r, mix r * ∑ i ∈ Finset.range m, p r i*w r (q+i)) - 1 := by
    simp_rw [mul_sub, mul_one, Finset.sum_sub_distrib, hp, mul_sub, mul_one]
    rw [Finset.sum_sub_distrib, hmix]
  rw [he]
  linarith

/-- Discrete normalized covers imply the exact weighted midpoint-CDF condition.
No positivity or symmetry of the kernels is needed for this finite implication. -/
theorem normalized_covers_imply_cdf {R n m : ℕ} (hn : 0 < n)
    (mix : Fin R → ℝ) (p w : Fin R → ℕ → ℝ)
    (hmix : ∑ r, mix r = 1)
    (hp : ∀ r, ∑ i ∈ Finset.range m, p r i = 1)
    (hw : ∀ r j, n≤j → w r j = 1)
    (hc : ∀ q < n, 1 ≤ ∑ r, mix r *
      ∑ i ∈ Finset.range m, p r i*w r (q+i)) :
    0 ≤ ∑ r, mix r * ∑ j ∈ Finset.range n,
      cdfCoeff m (p r) j * (w r j-1) := by
  apply mixed_cdf_nonneg hn mix p (fun r j => w r j-1)
  · intro r j hj
    rw [hw r j hj]
    ring
  · intro q hq
    exact normalized_cover_deviation mix p w hmix hp q (hc q hq)

lemma cdfCoeff_of_lt (m j : ℕ) (p : ℕ → ℝ) (hj : j <  m) :
    cdfCoeff m p j = (∑ i ∈ Finset.range j, p i) + p j/2 := by
  classical
  have ht : ∀ i, (if i < j then p i else if i=j then p i/2 else 0) =
      (if i < j then p i else 0) + (if i=j then p i/2 else 0) := by
    intro i
    by_cases hi : i < j
    · simp [hi, Nat.ne_of_lt hi]
    · simp [hi]
  have hf : (Finset.range m).filter (fun i => i < j) = Finset.range j := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  unfold cdfCoeff
  simp_rw [ht]
  rw [Finset.sum_add_distrib, ← Finset.sum_filter, hf]
  simp [hj]

lemma cdfCoeff_of_ge (m j : ℕ) (p : ℕ → ℝ) (hj : m≤j)
    (hp : ∑ i ∈ Finset.range m, p i = 1) : cdfCoeff m p j = 1 := by
  unfold cdfCoeff
  rw [← hp]
  apply Finset.sum_congr rfl
  intro i hi
  simp [Nat.lt_of_lt_of_le (Finset.mem_range.mp hi) hj]

noncomputable def tailMidpoint (m : ℕ) (p : ℕ → ℝ) (j : ℕ) : ℝ :=
  if j <  m then 1-(∑ i ∈ Finset.range j, p i)-p j/2 else 0

lemma cdfCoeff_eq_one_sub_tail (m j : ℕ) (p : ℕ → ℝ)
    (hp : ∑ i ∈ Finset.range m, p i = 1) :
    cdfCoeff m p j = 1-tailMidpoint m p j := by
  by_cases hj : j <  m
  · rw [cdfCoeff_of_lt m j p hj]
    simp only [tailMidpoint, if_pos hj]
    ring
  · rw [cdfCoeff_of_ge m j p (by omega) hp]
    simp [tailMidpoint, hj]

noncomputable def kernelAt {m : ℕ} (p : Fin m → ℝ) (j : ℕ) : ℝ :=
  if hj : j  <  m then p ⟨j,hj⟩ else 0

noncomputable def extendedWeight {R n : ℕ} (w : Fin R → Fin n → ℝ)
    (r : Fin R) (j : ℕ) : ℝ :=
  if hj : j  <  n then w r ⟨j,hj⟩ else 1

/-- The finite covering condition implies the weighted CDF boundary condition,
with exactly the original finite arrays and constant-one extension of w. -/
theorem finite_covers_imply_boundary {R n m : ℕ} (hn : 0 < n)
    (mix : Fin R → ℝ) (p : Fin R → Fin m → ℝ) (w : Fin R → Fin n → ℝ)
    (hmix : ∑ r, mix r = 1) (hp : ∀ r, ∑ i, p r i = 1)
    (hc : ∀ q : Fin (n+1), 1 ≤ ∑ r, mix r *
      ∑ i, p r i * extendedWeight w r (q.val+i.val)) :
    0 ≤ ∑ r, mix r * ∑ j : Fin n,
      (1-tailMidpoint m (kernelAt (p r)) j.val) * (w r j-1) := by
  have hpn : ∀ r, ∑ i ∈ Finset.range m, kernelAt (p r) i = 1 := by
    intro r
    rw [← Fin.sum_univ_eq_sum_range]
    simpa [kernelAt] using hp r
  have hwn : ∀ r j, n≤j → extendedWeight w r j = 1 := by
    intro r j hj
    simp [extendedWeight, show ¬j < n by omega]
  have hcn : ∀ q < n, 1 ≤ ∑ r, mix r * ∑ i ∈ Finset.range m,
      kernelAt (p r) i * extendedWeight w r (q+i) := by
    intro q hq
    simp_rw [← Fin.sum_univ_eq_sum_range]
    simpa [kernelAt] using hc ⟨q, by omega⟩
  have h := normalized_covers_imply_cdf hn mix (fun r => kernelAt (p r))
    (extendedWeight w) hmix hpn hwn hcn
  simp_rw [cdfCoeff_eq_one_sub_tail m _ _ (hpn _)] at h
  simp_rw [← Fin.sum_univ_eq_sum_range] at h
  simpa [extendedWeight] using h


noncomputable def finCDF {m : ℕ} (p : Fin m → ℝ) (j : Fin m) : ℝ :=
  ∑ i, if i < j then p i else if i=j then p i/2 else 0

lemma cdfCoeff_eq_finCDF {m : ℕ} (p : Fin m → ℝ) (j : Fin m) :
    cdfCoeff m (kernelAt p) j.val = finCDF p j := by
  unfold cdfCoeff finCDF
  rw [← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro i hi
  simp [kernelAt, Fin.ext_iff]

lemma finCDF_rev {m : ℕ} (p : Fin m → ℝ)
    (hsym : ∀ i, p i = p i.rev) (j : Fin m) :
    finCDF p j.rev = ∑ i : Fin m, if j < i then p i else if i=j then p i/2 else 0 := by
  unfold finCDF
  rw [← Equiv.sum_comp Fin.revPerm]
  change (∑ i : Fin m, if i.rev < j.rev then p i.rev
    else if i.rev=j.rev then p i.rev/2 else 0) = _
  simp_rw [Fin.rev_lt_rev, Fin.rev_injective.eq_iff, ← hsym]

lemma finCDF_add_rev {m : ℕ} (p : Fin m → ℝ)
    (hp : ∑ i, p i = 1) (hsym : ∀ i, p i = p i.rev) (j : Fin m) :
    finCDF p j + finCDF p j.rev = 1 := by
  rw [finCDF_rev p hsym j, finCDF, ← Finset.sum_add_distrib, ← hp]
  apply Finset.sum_congr rfl
  intro i hi
  rcases lt_trichotomy i j with hij | hij | hij
  · simp [hij, ne_of_lt hij, not_lt_of_ge (le_of_lt hij)]
  · subst i
    simp
  · simp [hij, ne_of_gt hij, not_lt_of_ge (le_of_lt hij)]

lemma sum_finCDF {m : ℕ} (p : Fin m → ℝ)
    (hp : ∑ i, p i = 1) (hsym : ∀ i, p i = p i.rev) :
    (∑ j, finCDF p j) = (m : ℝ)/2 := by
  have hrev : (∑ j : Fin m, finCDF p j.rev) = ∑ j, finCDF p j :=
    Equiv.sum_comp Fin.revPerm (finCDF p)
  have hadd : (∑ j, finCDF p j) + (∑ j : Fin m, finCDF p j.rev) = (m : ℝ) := by
    rw [← Finset.sum_add_distrib]
    simp_rw [finCDF_add_rev p hp hsym]
    simp
  rw [hrev] at hadd
  linarith

lemma sum_tailMidpoint {m : ℕ} (p : Fin m → ℝ)
    (hp : ∑ i, p i = 1) (hsym : ∀ i, p i = p i.rev) :
    (∑ j : Fin m, tailMidpoint m (kernelAt p) j.val) = (m : ℝ)/2 := by
  have hpn : ∑ i ∈ Finset.range m, kernelAt p i = 1 := by
    rw [← Fin.sum_univ_eq_sum_range]
    simpa [kernelAt] using hp
  have he : ∀ j : Fin m, tailMidpoint m (kernelAt p) j.val = 1-finCDF p j := by
    intro j
    have hh := cdfCoeff_eq_one_sub_tail m j.val (kernelAt p) hpn
    rw [cdfCoeff_eq_finCDF] at hh
    linarith
  simp_rw [he]
  rw [Finset.sum_sub_distrib, sum_finCDF p hp hsym]
  simp
  ring


lemma sum_tailMidpoint_extended {m n : ℕ} (hmn : m≤n) (p : Fin m → ℝ)
    (hp : ∑ i, p i = 1) (hsym : ∀ i, p i = p i.rev) :
    (∑ j : Fin n, tailMidpoint m (kernelAt p) j.val) = (m : ℝ)/2 := by
  have hs : (∑ j ∈ Finset.range m, tailMidpoint m (kernelAt p) j) =
      ∑ j ∈ Finset.range n, tailMidpoint m (kernelAt p) j := by
    apply Finset.sum_subset (Finset.range_mono hmn)
    intro j hj hjm
    simp only [Finset.mem_range, not_lt] at hjm
    simp [tailMidpoint, show ¬ j  <  m by omega]
  rw [Fin.sum_univ_eq_sum_range, ← hs, ← Fin.sum_univ_eq_sum_range]
  exact sum_tailMidpoint p hp hsym


end E30Boundary
namespace Submissions.E30VectorSmoothingFloor.Coleski
open scoped BigOperators
open E30Boundary
noncomputable section

lemma tail_square_sum {m n : ℕ} (hmn : m ≤ n) (p : Fin m → ℝ) :
    (∑ j : Fin n, (tailMidpoint m (kernelAt p) j.val)^2) =
    ∑ j ∈ Finset.range m, (1-(∑ i ∈ Finset.range j, kernelAt p i)-kernelAt p j/2)^2 := by
  rw [Fin.sum_univ_eq_sum_range (fun j => (tailMidpoint m (kernelAt p) j)^2) n]
  have hs : (∑ j ∈ Finset.range m, (tailMidpoint m (kernelAt p) j)^2) =
      ∑ j ∈ Finset.range n, (tailMidpoint m (kernelAt p) j)^2 := by
    apply Finset.sum_subset (Finset.range_mono hmn)
    intro j hj hjm
    simp only [Finset.mem_range, not_lt] at hjm
    simp [tailMidpoint, show ¬j < m by omega]
  rw [← hs]
  apply Finset.sum_congr rfl
  intro j hj
  simp [tailMidpoint, Finset.mem_range.mp hj]

open scoped BigOperators

def extendedWeight {R m L : ℕ} (w : Fin R → Fin (L * m) → ℝ)
    (r : Fin R) (j : ℕ) : ℝ :=
  if hj : j < L * m then w r ⟨j, hj⟩ else 1

def energyA {R m : ℕ} (mix : Fin R → ℝ) (p : Fin R → Fin m → ℝ) : ℝ :=
  (m : ℝ) * ∑ r, mix r * ∑ i, (p r i)^2

noncomputable def energyB {R m L : ℕ} (mix : Fin R → ℝ)
    (w : Fin R → Fin (L * m) → ℝ) : ℝ :=
  1 + 2 * ((∑ r, mix r * ∑ j, (w r j)^2) / (m : ℝ) - (L : ℝ))

/-- A uniform obstruction for the nonnegative, symmetric, diagonal
vector-smoothing framework, with no bound on its finite dimensions. -/
abbrev statement : Prop :=
  ∀ (R m L : ℕ), 0 < R → 0 < m → 0 < L →
    ∀ (mix : Fin R → ℝ) (p : Fin R → Fin m → ℝ)
      (w : Fin R → Fin (L * m) → ℝ),
      (∀ r, 0 ≤ mix r) → (∑ r, mix r) = 1 →
      (∀ r i, 0 ≤ p r i) → (∀ r, (∑ i, p r i) = 1) →
      (∀ r i, p r i = p r i.rev) →
      (∀ q : Fin (L * m + 1),
        1 ≤ ∑ r, mix r * ∑ i, p r i * extendedWeight w r (q.val + i.val)) →
      Real.pi ^ 2 ≤ 32 * energyA mix p * energyB mix w

theorem proof : statement := by
  intro R m L hR hm hL mix p w hmix hnorm hp hpsum hsym hcover
  have hmR : (0:ℝ) < m := by exact_mod_cast hm
  have hLm : m ≤ L*m := by nlinarith
  let pn : Fin R → ℕ → ℝ := fun r => kernelAt (p r)
  let e : Fin R → ℝ := fun r => ∑ i, (p r i)^2
  let J : Fin R → ℝ := fun r => ∑ i ∈ Finset.range m, ∫ t : ℝ in 0..1,
    ((∑ j ∈ Finset.range i, pn r j)+pn r i*t)*
      (1-((∑ j ∈ Finset.range i, pn r j)+pn r i*t))
  let d : Fin R → ℝ := fun r => (2/(m:ℝ))*J r
  let h : Fin R → Fin (L*m) → ℝ := fun r j => tailMidpoint m (pn r) j.val
  have he : ∀ r, 0 ≤ e r := fun r => Finset.sum_nonneg (fun i hi => sq_nonneg _)
  have hpn : ∀ r, (∑ i ∈ Finset.range m, pn r i) = 1 := by
    intro r
    rw [← Fin.sum_univ_eq_sum_range]
    simpa [pn, kernelAt] using hpsum r
  have hpnonneg : ∀ r i, i < m → 0 ≤ pn r i := by
    intro r i hi
    simpa [pn, kernelAt, hi] using hp r ⟨i,hi⟩
  have hraw : ∀ r, Real.pi^2 ≤ 64*e r*J r := by
    intro r
    have hh := Erdos30CDF.kernel_histogram_gini_energy (pn r) m (hpnonneg r) (hpn r)
    have heq : (∑ i ∈ Finset.range m, (pn r i)^2) = e r := by
      rw [← Fin.sum_univ_eq_sum_range]
      simp [pn, kernelAt, e]
    change Real.pi^2 ≤ 64*(∑ i ∈ Finset.range m, (pn r i)^2)*J r at hh
    rw [heq] at hh
    exact hh
  have hJnonneg : ∀ r, 0 ≤ J r := by
    intro r
    by_contra hj
    have hprod := mul_nonpos_of_nonneg_of_nonpos (he r) (le_of_lt (lt_of_not_ge hj))
    have hpi := sq_pos_of_pos Real.pi_pos
    nlinarith [hraw r]
  have hd : ∀ r, 0 ≤ d r := fun r => mul_nonneg (by positivity) (hJnonneg r)
  have hscalar : ∀ r, Real.pi^2 ≤ (32*(m:ℝ)*e r)*d r := by
    intro r
    have heq : (32*(m:ℝ)*e r)*d r = 64*e r*J r := by
      dsimp [d]
      field_simp [ne_of_gt hmR]
      <;> ring
    rw [heq]
    exact hraw r
  have hc : 0 ≤ ∑ r, mix r * ∑ j, (1-h r j)*(w r j-1) := by
    apply finite_covers_imply_boundary (Nat.mul_pos hL hm) mix p w hnorm hpsum
    intro q
    simpa only [extendedWeight, E30Boundary.extendedWeight] using hcover q
  have hb := E30Floor.boundary_completion mix w h hmix hnorm hc
  simp only [Fintype.card_fin, Nat.cast_mul] at hb
  have hJbound : ∀ r, J r ≤ (m:ℝ)/2 - ∑ j, (h r j)^2 := by
    intro r
    have hmean0 := sum_tailMidpoint (p r) (hpsum r) (hsym r)
    rw [Fin.sum_univ_eq_sum_range] at hmean0
    have hmean : (∑ i ∈ Finset.range m,
        (1-(∑ j ∈ Finset.range i, pn r j)-pn r i/2)) = (m:ℝ)/2 := by
      rw [← hmean0]
      apply Finset.sum_congr rfl
      intro i hi
      simp [pn, tailMidpoint, Finset.mem_range.mp hi]
    have hh := E30Floor.bin_moment_sum_le
      (fun i => ∑ j ∈ Finset.range i, pn r j) (pn r) m hmean
    change J r ≤ (m:ℝ)/2 - _ at hh
    have ht := tail_square_sum hLm (p r)
    change (∑ j, (h r j)^2) = _ at ht
    rw [ht]
    exact hh
  have hsumJ : (∑ r, mix r * J r) ≤
      (m:ℝ)/2 - ∑ r, mix r * ∑ j, (h r j)^2 := by
    calc
      _ ≤ ∑ r, mix r * ((m:ℝ)/2 - ∑ j, (h r j)^2) :=
        Finset.sum_le_sum (fun r hr => mul_le_mul_of_nonneg_left (hJbound r) (hmix r))
      _ = _ := by
        simp_rw [mul_sub]
        rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hnorm, one_mul]
  have hboundary : (∑ r, mix r * d r) ≤ energyB mix w := by
    have hid : (∑ r, mix r*d r) = (2/(m:ℝ))*(∑ r, mix r*J r) := by
      simp only [d, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r hr
      ring
    rw [hid]
    have hmul := mul_le_mul_of_nonneg_left hsumJ (show 0≤2/(m:ℝ) by positivity)
    unfold energyB
    apply (mul_le_mul_iff_left₀ hmR).mp
    field_simp [ne_of_gt hmR]
    nlinarith
  exact E30Floor.floor_assembly mix e d (m:ℝ) (energyB mix w)
    hmix hnorm he hd (le_of_lt hmR) hscalar hboundary

#print axioms proof
end
end Submissions.E30VectorSmoothingFloor.Coleski
