import Mathlib

namespace Submissions.Erdos1039UnitySharpConstant.ImagRays

open scoped BigOperators

/-- Every disk of radius `(π/2)(1 + 1/n)/n` meets a point where `|z ^ n - 1| ≥ 1`.
Far from the origin the center itself works. Otherwise move the center along
its circle to the nearest ray on which `z ^ n` is purely imaginary. -/
theorem key (n : ℕ) (hn : 0 < n) (w : ℂ) :
    ∃ z : ℂ, dist z w < Real.pi / 2 * (1 + 1 / (n : ℝ)) / (n : ℝ) ∧ 1 ≤ ‖z ^ n - 1‖ := by
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hn0 : (n : ℝ) ≠ 0 := hnR.ne'
  have hinv : (0 : ℝ) < 1 / (n : ℝ) := div_pos one_pos hnR
  have hc0 : (0 : ℝ) < 1 + 1 / (n : ℝ) := by linarith
  have hbern : (1 : ℝ) + (n : ℝ) * (1 / (n : ℝ)) ≤ (1 + 1 / (n : ℝ)) ^ n :=
    one_add_mul_le_pow (by linarith) n
  have hcn : (2 : ℝ) ≤ (1 + 1 / (n : ℝ)) ^ n := by
    have h1 : (n : ℝ) * (1 / (n : ℝ)) = 1 := mul_div_cancel₀ 1 hn0
    linarith
  have hbound : (0 : ℝ) < Real.pi / 2 * (1 + 1 / (n : ℝ)) / (n : ℝ) :=
    div_pos (mul_pos (div_pos Real.pi_pos (by norm_num)) hc0) hnR
  by_cases hr : 2 ≤ ‖w‖ ^ n
  · refine ⟨w, ?_, ?_⟩
    · rw [dist_self]
      exact hbound
    · have h2 : ‖w ^ n‖ - ‖(1 : ℂ)‖ ≤ ‖w ^ n - 1‖ := norm_sub_norm_le _ _
      rw [norm_pow, norm_one] at h2
      linarith
  · have hr2 : ‖w‖ < 1 + 1 / (n : ℝ) := by
      by_contra hge
      have hge' : 1 + 1 / (n : ℝ) ≤ ‖w‖ := not_lt.mp hge
      have hpow : (1 + 1 / (n : ℝ)) ^ n ≤ ‖w‖ ^ n := pow_le_pow_left₀ hc0.le hge' n
      exact hr (le_trans hcn hpow)
    obtain ⟨a, ha⟩ : ∃ a : ℝ, a = Real.pi / 2 / n := ⟨_, rfl⟩
    have ha0 : 0 < a := by
      rw [ha]
      exact div_pos (div_pos Real.pi_pos (by norm_num)) hnR
    have hna : (n : ℝ) * a = Real.pi / 2 := by
      rw [ha]
      exact mul_div_cancel₀ (Real.pi / 2) hn0
    have h2a : (0 : ℝ) < 2 * a := by linarith [ha0]
    obtain ⟨k, hk⟩ : ∃ k : ℤ, k = ⌊Complex.arg w / (2 * a)⌋ := ⟨_, rfl⟩
    have hk1 : (k : ℝ) ≤ Complex.arg w / (2 * a) := by
      rw [hk]
      exact Int.floor_le _
    have hk2 : Complex.arg w / (2 * a) < (k : ℝ) + 1 := by
      rw [hk]
      exact Int.lt_floor_add_one _
    have hk1' : (k : ℝ) * (2 * a) ≤ Complex.arg w := (le_div_iff₀ h2a).mp hk1
    have hk2' : Complex.arg w < ((k : ℝ) + 1) * (2 * a) := (div_lt_iff₀ h2a).mp hk2
    obtain ⟨φ, hφ⟩ : ∃ φ : ℝ, φ = (2 * (k : ℝ) + 1) * a := ⟨_, rfl⟩
    have e1 : φ - Complex.arg w = ((k : ℝ) * (2 * a) - Complex.arg w) + a := by
      rw [hφ]
      ring
    have e2 : ((k : ℝ) + 1) * (2 * a) = (k : ℝ) * (2 * a) + 2 * a := by ring
    rw [e2] at hk2'
    have hd : |φ - Complex.arg w| ≤ a := by
      rw [abs_le]
      constructor
      · linarith
      · linarith
    obtain ⟨z, hz⟩ : ∃ z : ℂ, z = (‖w‖ : ℂ) * Complex.exp ((φ : ℂ) * Complex.I) :=
      ⟨_, rfl⟩
    have hw : (‖w‖ : ℂ) * Complex.exp ((Complex.arg w : ℂ) * Complex.I) = w :=
      Complex.norm_mul_exp_arg_mul_I w
    refine ⟨z, ?_, ?_⟩
    · have hexp : Complex.exp ((φ : ℂ) * Complex.I)
          = Complex.exp ((Complex.arg w : ℂ) * Complex.I)
            * Complex.exp (Complex.I * ((φ - Complex.arg w : ℝ) : ℂ)) := by
        rw [← Complex.exp_add]
        congr 1
        push_cast
        ring
      have hzw : z - w = w * (Complex.exp (Complex.I * ((φ - Complex.arg w : ℝ) : ℂ)) - 1) := by
        calc z - w
            = (‖w‖ : ℂ) * Complex.exp ((φ : ℂ) * Complex.I)
                - (‖w‖ : ℂ) * Complex.exp ((Complex.arg w : ℂ) * Complex.I) := by
              rw [hz, hw]
          _ = ((‖w‖ : ℂ) * Complex.exp ((Complex.arg w : ℂ) * Complex.I))
                * (Complex.exp (Complex.I * ((φ - Complex.arg w : ℝ) : ℂ)) - 1) := by
              rw [hexp]
              ring
          _ = w * (Complex.exp (Complex.I * ((φ - Complex.arg w : ℝ) : ℂ)) - 1) := by
              rw [hw]
      have hb : ‖Complex.exp (Complex.I * ((φ - Complex.arg w : ℝ) : ℂ)) - (1 : ℂ)‖
          ≤ ‖φ - Complex.arg w‖ := Real.norm_exp_I_mul_ofReal_sub_one_le
      rw [Real.norm_eq_abs] at hb
      have hb' : ‖Complex.exp (Complex.I * ((φ - Complex.arg w : ℝ) : ℂ)) - (1 : ℂ)‖ ≤ a :=
        hb.trans hd
      have hmul : ‖w‖ * ‖Complex.exp (Complex.I * ((φ - Complex.arg w : ℝ) : ℂ)) - (1 : ℂ)‖
          ≤ ‖w‖ * a := mul_le_mul_of_nonneg_left hb' (norm_nonneg w)
      have hlt : ‖w‖ * a < (1 + 1 / (n : ℝ)) * a := mul_lt_mul_of_pos_right hr2 ha0
      have h2a' : (1 + 1 / (n : ℝ)) * a = Real.pi / 2 * (1 + 1 / (n : ℝ)) / (n : ℝ) := by
        rw [ha]
        ring
      rw [dist_eq_norm, hzw, norm_mul]
      linarith
    · have harg : (n : ℂ) * ((φ : ℂ) * Complex.I) = (((n : ℝ) * φ : ℝ) : ℂ) * Complex.I := by
        push_cast
        ring
      have hzn : z ^ n = ((‖w‖ ^ n : ℝ) : ℂ) * Complex.exp ((((n : ℝ) * φ : ℝ) : ℂ) * Complex.I) := by
        rw [hz, mul_pow, ← Complex.exp_nat_mul, harg, Complex.ofReal_pow]
      have hnφ : (n : ℝ) * φ = (2 * (k : ℝ) + 1) * Real.pi / 2 := by
        rw [hφ]
        calc (n : ℝ) * ((2 * (k : ℝ) + 1) * a) = (2 * (k : ℝ) + 1) * ((n : ℝ) * a) := by ring
          _ = (2 * (k : ℝ) + 1) * (Real.pi / 2) := by rw [hna]
          _ = (2 * (k : ℝ) + 1) * Real.pi / 2 := by ring
      have hcos : Real.cos ((n : ℝ) * φ) = 0 := Real.cos_eq_zero_iff.mpr ⟨k, hnφ⟩
      have hre : (z ^ n - 1).re = -1 := by
        rw [Complex.sub_re, hzn, Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re, hcos,
          Complex.one_re]
        ring
      have habs : |(z ^ n - 1).re| ≤ ‖z ^ n - 1‖ := Complex.abs_re_le_norm _
      rw [hre, abs_neg, abs_one] at habs
      exact habs

/-- The roots-of-unity polynomial in every positive degree has no disk of
radius `(π/2)(1 + 1/n)/n` inside its strict unit lemniscate. -/
theorem proof :
    ∀ n : ℕ, 0 < n → ∃ roots : Fin n → ℂ,
      (∀ i, ‖roots i‖ ≤ 1) ∧
      ∀ center : ℂ, ∃ z : ℂ,
        dist z center < Real.pi / 2 * (1 + 1 / n) / n ∧ 1 ≤ ‖∏ i, (z - roots i)‖ := by
  intro n hn
  have hprim : IsPrimitiveRoot (Complex.exp (2 * Real.pi * Complex.I / n)) n :=
    Complex.isPrimitiveRoot_exp n hn.ne'
  have hcard : Fintype.card (Polynomial.nthRootsFinset n (1 : ℂ)) = n := by
    rw [Fintype.card_coe]
    exact hprim.card_nthRootsFinset
  obtain ⟨e⟩ : Nonempty ((Polynomial.nthRootsFinset n (1 : ℂ)) ≃ Fin n) :=
    ⟨Fintype.equivFinOfCardEq hcard⟩
  refine ⟨fun i => ((e.symm i : Polynomial.nthRootsFinset n (1 : ℂ)) : ℂ), fun i => ?_,
    fun center => ?_⟩
  · have hmem : ((e.symm i : Polynomial.nthRootsFinset n (1 : ℂ)) : ℂ)
        ∈ Polynomial.nthRootsFinset n (1 : ℂ) := (e.symm i).2
    rw [Polynomial.mem_nthRootsFinset hn] at hmem
    exact (Complex.norm_eq_one_of_pow_eq_one hmem hn.ne').le
  · obtain ⟨z, hz1, hz2⟩ := key n hn center
    refine ⟨z, hz1, ?_⟩
    have h1 : ∏ i : Fin n, (z - ((e.symm i : Polynomial.nthRootsFinset n (1 : ℂ)) : ℂ))
        = ∏ x : Polynomial.nthRootsFinset n (1 : ℂ), (z - (x : ℂ)) :=
      Equiv.prod_comp e.symm (fun x : Polynomial.nthRootsFinset n (1 : ℂ) => z - (x : ℂ))
    have h2 : ∏ x : Polynomial.nthRootsFinset n (1 : ℂ), (z - (x : ℂ))
        = ∏ x ∈ Polynomial.nthRootsFinset n (1 : ℂ), (z - x) :=
      Finset.prod_coe_sort (Polynomial.nthRootsFinset n (1 : ℂ)) (fun x => z - x)
    have h3 : z ^ n - 1 ^ n = ∏ ζ ∈ Polynomial.nthRootsFinset n (1 : ℂ), (z - ζ * 1) :=
      hprim.pow_sub_pow_eq_prod_sub_mul z 1 hn
    rw [one_pow] at h3
    simp only [mul_one] at h3
    have h5 : ∏ i : Fin n, (z - ((e.symm i : Polynomial.nthRootsFinset n (1 : ℂ)) : ℂ))
        = z ^ n - 1 := h1.trans (h2.trans h3.symm)
    rw [← h5] at hz2
    exact hz2

end Submissions.Erdos1039UnitySharpConstant.ImagRays
