import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
Universal finite obstruction for the Hou--Zhao smoothing certificate family.
The final theorem `certificate_product_lower_bound_13_18` derives ab ≥ 13/18
from exactly the original kernel, mixture, symmetry, boundary, and covering
assumptions. The transpose, midpoint moments, and retained-square dual are
proved here from finite sums. No analytic approximation is assumed.
See OBSTRUCTION.md for the stronger handwritten pi-based bound and its scope.
-/
noncomputable section
namespace SmoothingLimit

open Finset

def cdfBefore (p : ℕ → ℝ) (n : ℕ) : ℝ := ∑ i ∈ range n, p i

def midpoint (p : ℕ → ℝ) (n : ℕ) : ℝ := cdfBefore p n + p n / 2

/-- Exact midpoint quadrature identity for t(1-t). -/
theorem midpoint_moment_identity (p : ℕ → ℝ) (n : ℕ) :
    (∑ i ∈ range n, p i * midpoint p i * (1 - midpoint p i)) =
      cdfBefore p n ^ 2 / 2 - cdfBefore p n ^ 3 / 3 +
        (∑ i ∈ range n, p i ^ 3) / 12 := by
  induction n with
  | zero => simp [cdfBefore]
  | succ n ih =>
    rw [sum_range_succ, sum_range_succ, ih]
    have hp : cdfBefore p (n + 1) = cdfBefore p n + p n := by
      simp [cdfBefore, sum_range_succ]
    rw [hp]
    unfold midpoint
    ring

/-- Every probability histogram has at least the continuous midpoint moment. -/
theorem midpoint_moment_ge (p : ℕ → ℝ) (n : ℕ)
    (hp : ∀ i < n, 0 ≤ p i) (hmass : cdfBefore p n = 1) :
    (1 : ℝ) / 6 ≤ ∑ i ∈ range n, p i * midpoint p i * (1 - midpoint p i) := by
  rw [midpoint_moment_identity, hmass]
  have hcube : 0 ≤ ∑ i ∈ range n, p i ^ 3 :=
    sum_nonneg fun i hi => pow_nonneg (hp i (mem_range.mp hi)) 3
  linarith

/-- A finite weighted square-completion dual, allowing signed primal weights. -/
theorem dual_square_completion {ι : Type*} [Fintype ι]
    (μ g M : ι → ℝ) (hμ : ∀ i, 0 ≤ μ i)
    (hdual : 0 ≤ ∑ i, μ i * M i * g i) :
    -(∑ i, μ i * (1 - M i) ^ 2) ≤
      ∑ i, μ i * ((g i + 1) ^ 2 - 1) := by
  have hsquare : 0 ≤ ∑ i, μ i * (g i + 1 - M i) ^ 2 :=
    sum_nonneg fun i _ => mul_nonneg (hμ i) (sq_nonneg _)
  have hid : (∑ i, μ i * ((g i + 1) ^ 2 - 1)) =
      (∑ i, μ i * (g i + 1 - M i) ^ 2) -
      (∑ i, μ i * (1 - M i) ^ 2) + 2 * (∑ i, μ i * M i * g i) := by
    rw [← sum_sub_distrib, mul_sum, ← sum_add_distrib]
    apply sum_congr rfl
    intro i _
    ring
  rw [hid]
  linarith

/-- Weighted finite Cauchy--Schwarz without square roots. -/
theorem weighted_cauchy {ι : Type*} [Fintype ι]
    (μ p u : ι → ℝ) (hμ : ∀ i, 0 ≤ μ i) :
    (∑ i, μ i * p i * u i) ^ 2 ≤
      (∑ i, μ i * p i ^ 2) * (∑ i, μ i * u i ^ 2) := by
  apply sum_sq_le_sum_mul_sum_of_sq_le_mul
  · intro i _
    exact mul_nonneg (hμ i) (sq_nonneg _)
  · intro i _
    exact mul_nonneg (hμ i) (sq_nonneg _)
  · intro i _
    exact le_of_eq (by ring)

/-- The fully algebraic obstruction, with the dual bound explicit. For the
original certificates, index i is a kernel/bin pair and μ_i=λ_kernel. -/
theorem rational_obstruction {ι : Type*} [Fintype ι]
    (μ p M : ι → ℝ) (a b m : ℝ)
    (hμ : ∀ i, 0 ≤ μ i) (hM0 : ∀ i, 0 ≤ M i) (hM1 : ∀ i, M i ≤ 1)
    (hmoment : (1 : ℝ) / 6 ≤ ∑ i, μ i * p i * (M i * (1 - M i)))
    (ha : a = m * ∑ i, μ i * p i ^ 2)
    (hdual : 2 * (∑ i, μ i * (M i * (1 - M i))) ≤ m * b) :
    (2 : ℝ) / 9 ≤ a * b := by
  let u : ι → ℝ := fun i => M i * (1 - M i)
  have hu0 : ∀ i, 0 ≤ u i := fun i =>
    mul_nonneg (hM0 i) (sub_nonneg.mpr (hM1 i))
  have hu1 : ∀ i, u i ≤ (1 : ℝ) / 4 := by
    intro i
    dsimp [u]
    nlinarith [sq_nonneg (M i - 1 / 2)]
  have hA : 0 ≤ ∑ i, μ i * p i ^ 2 :=
    sum_nonneg fun i _ => mul_nonneg (hμ i) (sq_nonneg _)
  have hQ : (∑ i, μ i * u i ^ 2) ≤ (∑ i, μ i * u i) / 4 := by
    rw [sum_div]
    apply sum_le_sum
    intro i _
    have hi : u i ^ 2 ≤ u i / 4 := by
      nlinarith [mul_nonneg (hu0 i) (sub_nonneg.mpr (hu1 i))]
    nlinarith [mul_le_mul_of_nonneg_left hi (hμ i)]
  have hCS := weighted_cauchy μ p u hμ
  have hmoment' : (1 : ℝ) / 6 ≤ ∑ i, μ i * p i * u i := hmoment
  have hprod := mul_le_mul_of_nonneg_left hQ hA
  have hAU : (1 : ℝ) / 9 ≤
      (∑ i, μ i * p i ^ 2) * (∑ i, μ i * u i) := by
    nlinarith [sq_nonneg ((∑ i, μ i * p i * u i) - 1 / 6)]
  have hd := mul_le_mul_of_nonneg_left hdual hA
  rw [ha]
  change (2 : ℝ) / 9 ≤ (m * ∑ i, μ i * p i ^ 2) * b
  change (∑ i, μ i * p i ^ 2) * (2 * (∑ i, μ i * u i)) ≤
    (∑ i, μ i * p i ^ 2) * (m * b) at hd
  nlinarith


/-- Finite integration by parts, including the diagonal exactly once. -/
theorem cdf_product_identity (p g : ℕ → ℝ) (m : ℕ) :
    (∑ i ∈ range m, p i * cdfBefore g i) +
      (∑ i ∈ range m, g i * cdfBefore p i) +
      (∑ i ∈ range m, p i * g i) = cdfBefore p m * cdfBefore g m := by
  induction m with
  | zero => simp [cdfBefore]
  | succ m ih =>
    simp only [sum_range_succ]
    have hp : cdfBefore p (m+1) = cdfBefore p m + p m := by
      simp [cdfBefore, sum_range_succ]
    have hg : cdfBefore g (m+1) = cdfBefore g m + g m := by
      simp [cdfBefore, sum_range_succ]
    rw [hp, hg]
    nlinarith only [ih]

/-- Summing a translate of a finitely supported sequence. -/
theorem shifted_sum (g : ℕ → ℝ) (n i : ℕ) (htail : ∀ j, n ≤ j → g j = 0) :
    (∑ q ∈ range n, g (q+i)) = cdfBefore g n - cdfBefore g i := by
  have hz : (∑ q ∈ range i, g (n+q)) = 0 := by
    apply sum_eq_zero
    intro q _
    exact htail _ (by omega)
  have h1 := sum_range_add g n i
  have h2 := sum_range_add g i n
  rw [hz, add_zero] at h1
  have he : n+i = i+n := by omega
  rw [he, h2] at h1
  change cdfBefore g i + (∑ q ∈ range n, g (i+q)) = cdfBefore g n at h1
  simpa [Nat.add_comm] using (eq_sub_iff_add_eq.mpr (by linarith :
    (∑ q ∈ range n, g (i+q)) + cdfBefore g i = cdfBefore g n))

/-- Exact half-weight covering transpose for one normalized kernel. -/
theorem covering_transpose (p g : ℕ → ℝ) (m n : ℕ)
    (hmass : cdfBefore p m = 1) (htail : ∀ j, n ≤ j → g j = 0) :
    (∑ q ∈ range n, ∑ i ∈ range m, p i * g (q+i)) -
        (∑ i ∈ range m, p i * g i) / 2 =
      cdfBefore g n - (∑ i ∈ range m, (1 - midpoint p i) * g i) := by
  rw [sum_comm]
  simp_rw [← mul_sum, shifted_sum g n _ htail]
  simp_rw [mul_sub]
  rw [sum_sub_distrib, ← sum_mul]
  change cdfBefore p m * cdfBefore g n -
      (∑ i ∈ range m, p i * cdfBefore g i) -
      (∑ i ∈ range m, p i * g i) / 2 = _
  rw [hmass, one_mul]
  have hid := cdf_product_identity p g m
  rw [hmass, one_mul] at hid
  have he : (∑ i ∈ range m, (1 - midpoint p i) * g i) =
      cdfBefore g m - (∑ i ∈ range m, g i * cdfBefore p i) -
      (∑ i ∈ range m, p i * g i) / 2 := by
    unfold cdfBefore
    rw [sum_div, ← sum_sub_distrib, ← sum_sub_distrib]
    apply sum_congr rfl
    intro i _
    unfold midpoint cdfBefore
    ring
  rw [he]
  linarith

/-- CDF midpoint values are in the unit interval. -/
theorem midpoint_bounds (p : ℕ → ℝ) (m : ℕ)
    (hp : ∀ i < m, 0 ≤ p i) (hmass : cdfBefore p m = 1)
    (i : ℕ) (hi : i < m) : 0 ≤ midpoint p i ∧ midpoint p i ≤ 1 := by
  have hpre0 : 0 ≤ cdfBefore p i := by
    apply sum_nonneg
    intro j hj
    exact hp j (lt_trans (mem_range.mp hj) hi)
  have hpost : cdfBefore p (i+1) ≤ cdfBefore p m := by
    apply sum_le_sum_of_subset_of_nonneg
    · exact range_mono (by omega)
    · intro j hj _
      exact hp j (mem_range.mp hj)
  have hrec : cdfBefore p (i+1) = cdfBefore p i + p i := by
    simp [cdfBefore, sum_range_succ]
  rw [hrec, hmass] at hpost
  dsimp [midpoint]
  constructor <;> linarith [hp i hi]

/-- Symmetry forces the discrete first moment to the central bin. -/
theorem symmetric_first_moment (p : ℕ → ℝ) (m : ℕ) (hm : 0 < m)
    (hmass : cdfBefore p m = 1)
    (hsym : ∀ i < m, p (m-1-i) = p i) :
    (∑ i ∈ range m, (i:ℝ) * p i) = ((m:ℝ)-1)/2 := by
  have hrefl := sum_range_reflect (fun i => (i:ℝ) * p i) m
  have he : (∑ i ∈ range m, ((m-1-i:ℕ):ℝ) * p (m-1-i)) =
      ((m:ℝ)-1) * cdfBefore p m - (∑ i ∈ range m, (i:ℝ)*p i) := by
    unfold cdfBefore
    rw [mul_sum, ← sum_sub_distrib]
    apply sum_congr rfl
    intro i hi
    have hi' := mem_range.mp hi
    rw [hsym i hi']
    have hc : ((m-1-i:ℕ):ℝ) = (m:ℝ)-1-i := by
      rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega), Nat.cast_one]
    rw [hc]
    ring
  rw [he, hmass] at hrefl
  linarith

/-- The midpoint CDF of a symmetric probability histogram has mean 1/2. -/
theorem midpoint_sum (p : ℕ → ℝ) (m : ℕ) (hm : 0 < m)
    (hmass : cdfBefore p m = 1)
    (hsym : ∀ i < m, p (m-1-i) = p i) :
    (∑ i ∈ range m, midpoint p i) = (m:ℝ)/2 := by
  have hid := cdf_product_identity p (fun _ => 1) m
  simp only [cdfBefore, sum_const, card_range, nsmul_eq_mul, mul_one, one_mul] at hid
  have hmom := symmetric_first_moment p m hm hmass hsym
  have hmass' : (∑ i ∈ range m, p i) = 1 := hmass
  have he : (∑ i ∈ range m, midpoint p i) =
      (∑ i ∈ range m, cdfBefore p i) + cdfBefore p m / 2 := by
    simp [midpoint, sum_add_distrib, ← sum_div, cdfBefore]
  rw [he, hmass]
  simp only [mul_comm (p _)] at hid
  change (∑ i ∈ range m, (i:ℝ)*p i) + (∑ i ∈ range m, cdfBefore p i) +
    (∑ i ∈ range m, p i) = (∑ i ∈ range m, p i) * (m:ℝ) at hid
  rw [hmom, hmass'] at hid
  linarith


/-- Energy square completion with any number of additional boundary bins. -/
theorem scalar_energy_lower (g M : ℕ → ℝ) (m n : ℕ) (hmn : m ≤ n) :
    2 * (cdfBefore g n - ∑ j ∈ range m, (1-M j)*g j) -
      (∑ j ∈ range m, (1-M j)^2) ≤
      ∑ j ∈ range n, ((g j+1)^2-1) := by
  have hs : (∑ j ∈ range m, g j ^ 2) ≤ ∑ j ∈ range n, g j ^ 2 := by
    exact sum_le_sum_of_subset_of_nonneg (range_mono hmn) (fun _ _ _ => sq_nonneg _)
  have hnon : 0 ≤ ∑ j ∈ range m, (g j+1-M j)^2 :=
    sum_nonneg fun _ _ => sq_nonneg _
  have he1 : (∑ j ∈ range m, (g j+1-M j)^2) =
      (∑ j ∈ range m, g j^2) + 2*(∑ j ∈ range m, (1-M j)*g j) +
      (∑ j ∈ range m, (1-M j)^2) := by
    rw [mul_sum, ← sum_add_distrib, ← sum_add_distrib]
    apply sum_congr rfl
    intro j _
    ring
  have he2 : (∑ j ∈ range n, ((g j+1)^2-1)) =
      (∑ j ∈ range n, g j^2) + 2*cdfBefore g n := by
    unfold cdfBefore
    rw [mul_sum, ← sum_add_distrib]
    apply sum_congr rfl
    intro j _
    ring
  rw [he1] at hnon
  rw [he2]
  linarith

/-- The half-weight aggregate is nonnegative for any nonnegative covers. -/
theorem half_weight_nonneg (C : ℕ → ℝ) (n : ℕ) (hn : 0 < n)
    (hC : ∀ q < n, 0 ≤ C q) :
    0 ≤ (∑ q ∈ range n, C q) - C 0/2 := by
  have h0 := hC 0 hn
  have hh : C 0 ≤ ∑ q ∈ range n, C q :=
    single_le_sum (fun q hq => hC q (mem_range.mp hq)) (mem_range.mpr hn)
  linarith

/-- The exact mixed dual follows from the original signed covering residuals. -/
theorem mixed_dual_nonneg {R : Type*} [Fintype R]
    (lam : R → ℝ) (p g : R → ℕ → ℝ) (m n : ℕ) (hn : 0 < n)
    (hmass : ∀ r, cdfBefore (p r) m = 1)
    (htail : ∀ r j, n ≤ j → g r j = 0)
    (hcover : ∀ q < n, 0 ≤ ∑ r, lam r * ∑ i ∈ range m, p r i*g r (q+i)) :
    0 ≤ ∑ r, lam r * (cdfBefore (g r) n -
      ∑ j ∈ range m, (1-midpoint (p r) j)*g r j) := by
  have hc := half_weight_nonneg
    (fun q => ∑ r, lam r * ∑ i ∈ range m, p r i*g r (q+i)) n hn hcover
  have he : (∑ q ∈ range n, ∑ r, lam r * ∑ i ∈ range m, p r i*g r (q+i)) -
      (∑ r, lam r * ∑ i ∈ range m, p r i*g r (0+i))/2 =
      ∑ r, lam r * (cdfBefore (g r) n -
        ∑ j ∈ range m, (1-midpoint (p r) j)*g r j) := by
    rw [sum_comm]
    simp_rw [← mul_sum]
    rw [sum_div, ← sum_sub_distrib]
    apply sum_congr rfl
    intro r _
    have hr := covering_transpose (p r) (g r) m n (hmass r) (htail r)
    simp only [zero_add]
    nlinarith only [congrArg (fun x => lam r*x) hr]
  rw [he] at hc
  exact hc

/-- Full finite energy dual, before using symmetry. -/
theorem mixed_energy_dual {R : Type*} [Fintype R]
    (lam : R → ℝ) (p g : R → ℕ → ℝ) (m n : ℕ) (hn : 0 < n) (hmn : m ≤ n)
    (hlam : ∀ r, 0 ≤ lam r)
    (hmass : ∀ r, cdfBefore (p r) m = 1)
    (htail : ∀ r j, n ≤ j → g r j = 0)
    (hcover : ∀ q < n, 0 ≤ ∑ r, lam r * ∑ i ∈ range m, p r i*g r (q+i)) :
    -(∑ r, lam r * ∑ j ∈ range m, (1-midpoint (p r) j)^2) ≤
      ∑ r, lam r * ∑ j ∈ range n, ((g r j+1)^2-1) := by
  have hd := mixed_dual_nonneg lam p g m n hn hmass htail hcover
  have he : (∑ r, lam r * (2 * (cdfBefore (g r) n -
      ∑ j ∈ range m, (1-midpoint (p r) j)*g r j) -
      (∑ j ∈ range m, (1-midpoint (p r) j)^2))) ≤
      ∑ r, lam r * ∑ j ∈ range n, ((g r j+1)^2-1) := by
    apply sum_le_sum
    intro r _
    exact mul_le_mul_of_nonneg_left
      (scalar_energy_lower (g r) (midpoint (p r)) m n hmn) (hlam r)
  have hid : (∑ r, lam r * (2 * (cdfBefore (g r) n -
      ∑ j ∈ range m, (1-midpoint (p r) j)*g r j) -
      (∑ j ∈ range m, (1-midpoint (p r) j)^2))) =
      2 * (∑ r, lam r * (cdfBefore (g r) n -
      ∑ j ∈ range m, (1-midpoint (p r) j)*g r j)) -
      (∑ r, lam r * ∑ j ∈ range m, (1-midpoint (p r) j)^2) := by
    rw [mul_sum, ← sum_sub_distrib]
    apply sum_congr rfl
    intro r _
    ring
  rw [hid] at he
  linarith



/-- Retain the square remainder instead of discarding it. -/
theorem scalar_energy_remainder (g M : ℕ → ℝ) (m n : ℕ) (hmn : m ≤ n) :
    (∑ j ∈ range m, (g j+1-M j)^2) +
      2 * (cdfBefore g n - ∑ j ∈ range m, (1-M j)*g j) -
      (∑ j ∈ range m, (1-M j)^2) ≤
      ∑ j ∈ range n, ((g j+1)^2-1) := by
  have hs : (∑ j ∈ range m, g j ^ 2) ≤ ∑ j ∈ range n, g j ^ 2 := by
    exact sum_le_sum_of_subset_of_nonneg (range_mono hmn) (fun _ _ _ => sq_nonneg _)
  have he1 : (∑ j ∈ range m, (g j+1-M j)^2) =
      (∑ j ∈ range m, g j^2) + 2*(∑ j ∈ range m, (1-M j)*g j) +
      (∑ j ∈ range m, (1-M j)^2) := by
    rw [mul_sum, ← sum_add_distrib, ← sum_add_distrib]
    apply sum_congr rfl
    intro j _
    ring
  have he2 : (∑ j ∈ range n, ((g j+1)^2-1)) =
      (∑ j ∈ range n, g j^2) + 2*cdfBefore g n := by
    unfold cdfBefore
    rw [mul_sum, ← sum_add_distrib]
    apply sum_congr rfl
    intro j _
    ring
  rw [he1, he2]
  linarith

/-- Full finite energy dual with its square remainder. -/
theorem mixed_energy_remainder {R : Type*} [Fintype R]
    (lam : R → ℝ) (p g : R → ℕ → ℝ) (m n : ℕ) (hn : 0 < n) (hmn : m ≤ n)
    (hlam : ∀ r, 0 ≤ lam r)
    (hmass : ∀ r, cdfBefore (p r) m = 1)
    (htail : ∀ r j, n ≤ j → g r j = 0)
    (hcover : ∀ q < n, 0 ≤ ∑ r, lam r * ∑ i ∈ range m, p r i*g r (q+i)) :
    (∑ r, lam r * ∑ j ∈ range m, (g r j+1-midpoint (p r) j)^2) ≤
      (∑ r, lam r * ∑ j ∈ range n, ((g r j+1)^2-1)) +
      (∑ r, lam r * ∑ j ∈ range m, (1-midpoint (p r) j)^2) := by
  have hd := mixed_dual_nonneg lam p g m n hn hmass htail hcover
  have he : (∑ r, lam r * ((∑ j ∈ range m, (g r j+1-midpoint (p r) j)^2) +
      2 * (cdfBefore (g r) n - ∑ j ∈ range m, (1-midpoint (p r) j)*g r j) -
      (∑ j ∈ range m, (1-midpoint (p r) j)^2))) ≤
      ∑ r, lam r * ∑ j ∈ range n, ((g r j+1)^2-1) := by
    apply sum_le_sum
    intro r _
    exact mul_le_mul_of_nonneg_left
      (scalar_energy_remainder (g r) (midpoint (p r)) m n hmn) (hlam r)
  have hid : (∑ r, lam r * ((∑ j ∈ range m, (g r j+1-midpoint (p r) j)^2) +
      2 * (cdfBefore (g r) n - ∑ j ∈ range m, (1-midpoint (p r) j)*g r j) -
      (∑ j ∈ range m, (1-midpoint (p r) j)^2))) =
      (∑ r, lam r * ∑ j ∈ range m, (g r j+1-midpoint (p r) j)^2) +
      2 * (∑ r, lam r * (cdfBefore (g r) n -
      ∑ j ∈ range m, (1-midpoint (p r) j)*g r j)) -
      (∑ r, lam r * ∑ j ∈ range m, (1-midpoint (p r) j)^2) := by
    rw [mul_sum, ← sum_add_distrib, ← sum_sub_distrib]
    apply sum_congr rfl
    intro r _
    ring
  rw [hid] at he
  linarith

/-- Exact half-mass identity used by the q=0 cover. -/
theorem midpoint_pairing (p : ℕ → ℝ) (m : ℕ)
    (hmass : cdfBefore p m = 1) :
    (∑ i ∈ range m, p i * midpoint p i) = (1:ℝ)/2 := by
  have h := cdf_product_identity p p m
  rw [hmass] at h
  have he : (∑ i ∈ range m, p i * midpoint p i) =
      (∑ i ∈ range m, p i * cdfBefore p i) +
      (∑ i ∈ range m, p i * p i)/2 := by
    rw [sum_div, ← sum_add_distrib]
    apply sum_congr rfl
    intro i _
    unfold midpoint
    ring
  rw [he]
  linarith

/-- The certificate parameters, definitionally matching SidonConcrete.aValue. -/
def aValue {R : Type*} [Fintype R] (m : ℕ) (lam : R → ℝ) (p : R → ℕ → ℝ) : ℝ :=
  (m:ℝ) * ∑ r, lam r * ∑ i ∈ range m, p r i ^ 2

/-- The certificate parameters, definitionally matching SidonConcrete.bValue. -/
def bValue {R : Type*} [Fintype R] (m L : ℕ) (lam : R → ℝ) (w : R → ℕ → ℝ) : ℝ :=
  1 + 2 * ((∑ r, lam r * ∑ j ∈ range (L*m), w r j ^ 2)/(m:ℝ) - L)

/-- Full half-weight dual bound from exactly the finite covering assumptions. -/
theorem certificate_dual_bound {R : Type*} [Fintype R]
    (m L : ℕ) (hm : 0 < m) (hL : 0 < L)
    (lam : R → ℝ) (p w : R → ℕ → ℝ)
    (hlam_nonneg : ∀ r, 0 ≤ lam r) (hlam : ∑ r, lam r = 1)
    (hmass : ∀ r, ∑ i ∈ range m, p r i = 1)
    (hsym : ∀ r i, i < m → p r (m-1-i) = p r i)
    (hw : ∀ r j, L*m ≤ j → w r j = 1)
    (hc : ∀ q ≤ L*m, 1 ≤ ∑ r, lam r * ∑ i ∈ range m, p r i*w r (q+i)) :
    2 * (∑ r, lam r * ∑ j ∈ range m,
      midpoint (p r) j * (1-midpoint (p r) j)) ≤
      (m:ℝ) * bValue m L lam w := by
  let g : R → ℕ → ℝ := fun r j => w r j-1
  have hn : 0 < L*m := Nat.mul_pos hL hm
  have hmn : m ≤ L*m := by nlinarith
  have hcovg : ∀ q < L*m,
      0 ≤ ∑ r, lam r * ∑ i ∈ range m, p r i*g r (q+i) := by
    intro q hq
    have hq' := hc q (by omega)
    have he : (∑ r, lam r * ∑ i ∈ range m, p r i*g r (q+i)) =
        (∑ r, lam r * ∑ i ∈ range m, p r i*w r (q+i)) - 1 := by
      dsimp [g]
      simp_rw [mul_sub, mul_one, sum_sub_distrib, hmass, mul_sub, mul_one]
      rw [sum_sub_distrib, hlam]
    rw [he]
    linarith
  have hd := mixed_energy_dual lam p g m (L*m) hn hmn hlam_nonneg
    (fun r => hmass r)
    (fun r j hj => by dsimp [g]; rw [hw r j hj]; ring) hcovg
  have hB : (∑ r, lam r * ∑ j ∈ range m, (1-midpoint (p r) j)^2) =
      (m:ℝ)/2 - (∑ r, lam r * ∑ j ∈ range m,
        midpoint (p r) j * (1-midpoint (p r) j)) := by
    have he : ∀ r, (∑ j ∈ range m, (1-midpoint (p r) j)^2) =
        (m:ℝ)/2 - (∑ j ∈ range m,
          midpoint (p r) j * (1-midpoint (p r) j)) := by
      intro r
      have hs := midpoint_sum (p r) m hm (hmass r) (hsym r)
      have hp : (∑ j ∈ range m, (1-midpoint (p r) j)^2) =
          (m:ℝ) - (∑ j ∈ range m, midpoint (p r) j) -
          (∑ j ∈ range m, midpoint (p r) j * (1-midpoint (p r) j)) := by
        have hn' : (m:ℝ) = ∑ j ∈ range m, (1:ℝ) := by simp
        rw [hn', ← sum_sub_distrib, ← sum_sub_distrib]
        apply sum_congr rfl
        intro j _
        ring
      rw [hp, hs]
      ring
    simp_rw [he, mul_sub]
    rw [sum_sub_distrib, ← sum_mul, hlam]
    ring
  have hE : (∑ r, lam r * ∑ j ∈ range (L*m), ((g r j+1)^2-1)) =
      (∑ r, lam r * ∑ j ∈ range (L*m), w r j ^ 2) - ((L*m:ℕ):ℝ) := by
    dsimp [g]
    simp_rw [sub_add_cancel, sum_sub_distrib, sum_const, card_range,
      nsmul_eq_mul, mul_one, mul_sub]
    rw [sum_sub_distrib, ← sum_mul, hlam]
    ring
  rw [hB, hE] at hd
  have hm0 : (m:ℝ) ≠ 0 := by positivity
  have hb : (m:ℝ) * bValue m L lam w = (m:ℝ) + 2 *
      ((∑ r, lam r * ∑ j ∈ range (L*m), w r j ^ 2) - (L:ℝ)*m) := by
    unfold bValue
    field_simp
  rw [hb]
  push_cast at hd
  linarith

/-- The complete certificate dual retaining its boundary-square remainder. -/
theorem certificate_remainder_bound {R : Type*} [Fintype R]
    (m L : ℕ) (hm : 0 < m) (hL : 0 < L)
    (lam : R → ℝ) (p w : R → ℕ → ℝ)
    (hlam_nonneg : ∀ r, 0 ≤ lam r) (hlam : ∑ r, lam r = 1)
    (hmass : ∀ r, ∑ i ∈ range m, p r i = 1)
    (hsym : ∀ r i, i < m → p r (m-1-i) = p r i)
    (hw : ∀ r j, L*m ≤ j → w r j = 1)
    (hc : ∀ q ≤ L*m, 1 ≤ ∑ r, lam r * ∑ i ∈ range m, p r i*w r (q+i)) :
    2 * (∑ r, lam r * ∑ j ∈ range m,
      midpoint (p r) j * (1-midpoint (p r) j)) +
      2 * (∑ r, lam r * ∑ j ∈ range m, (w r j-midpoint (p r) j)^2) ≤
      (m:ℝ) * bValue m L lam w := by
  let g : R → ℕ → ℝ := fun r j => w r j-1
  have hn : 0 < L*m := Nat.mul_pos hL hm
  have hmn : m ≤ L*m := by nlinarith
  have hcovg : ∀ q < L*m,
      0 ≤ ∑ r, lam r * ∑ i ∈ range m, p r i*g r (q+i) := by
    intro q hq
    have hq' := hc q (by omega)
    have he : (∑ r, lam r * ∑ i ∈ range m, p r i*g r (q+i)) =
        (∑ r, lam r * ∑ i ∈ range m, p r i*w r (q+i)) - 1 := by
      dsimp [g]
      simp_rw [mul_sub, mul_one, sum_sub_distrib, hmass, mul_sub, mul_one]
      rw [sum_sub_distrib, hlam]
    rw [he]
    linarith
  have hd := mixed_energy_remainder lam p g m (L*m) hn hmn hlam_nonneg
    (fun r => hmass r)
    (fun r j hj => by dsimp [g]; rw [hw r j hj]; ring) hcovg
  have hB : (∑ r, lam r * ∑ j ∈ range m, (1-midpoint (p r) j)^2) =
      (m:ℝ)/2 - (∑ r, lam r * ∑ j ∈ range m,
        midpoint (p r) j * (1-midpoint (p r) j)) := by
    have he : ∀ r, (∑ j ∈ range m, (1-midpoint (p r) j)^2) =
        (m:ℝ)/2 - (∑ j ∈ range m,
          midpoint (p r) j * (1-midpoint (p r) j)) := by
      intro r
      have hs := midpoint_sum (p r) m hm (hmass r) (hsym r)
      have hp : (∑ j ∈ range m, (1-midpoint (p r) j)^2) =
          (m:ℝ) - (∑ j ∈ range m, midpoint (p r) j) -
          (∑ j ∈ range m, midpoint (p r) j * (1-midpoint (p r) j)) := by
        have hn' : (m:ℝ) = ∑ j ∈ range m, (1:ℝ) := by simp
        rw [hn', ← sum_sub_distrib, ← sum_sub_distrib]
        apply sum_congr rfl
        intro j _
        ring
      rw [hp, hs]
      ring
    simp_rw [he, mul_sub]
    rw [sum_sub_distrib, ← sum_mul, hlam]
    ring
  have hE : (∑ r, lam r * ∑ j ∈ range (L*m), ((g r j+1)^2-1)) =
      (∑ r, lam r * ∑ j ∈ range (L*m), w r j ^ 2) - ((L*m:ℕ):ℝ) := by
    dsimp [g]
    simp_rw [sub_add_cancel, sum_sub_distrib, sum_const, card_range,
      nsmul_eq_mul, mul_one, mul_sub]
    rw [sum_sub_distrib, ← sum_mul, hlam]
    ring
  rw [hB, hE] at hd
  dsimp [g] at hd
  simp only [sub_add_cancel] at hd
  have hm0 : (m:ℝ) ≠ 0 := by positivity
  have hb : (m:ℝ) * bValue m L lam w = (m:ℝ) + 2 *
      ((∑ r, lam r * ∑ j ∈ range (L*m), w r j ^ 2) - (L:ℝ)*m) := by
    unfold bValue
    field_simp
  rw [hb]
  push_cast at hd
  linarith


/-- UNIVERSAL CERTIFICATE OBSTRUCTION: every Hou--Zhao finite certificate has
ab at least 2/9. No positivity assumption on w or on b is required. -/
theorem certificate_product_lower_bound {R : Type*} [Fintype R]
    (m L : ℕ) (hm : 0 < m) (hL : 0 < L)
    (lam : R → ℝ) (p w : R → ℕ → ℝ)
    (hlam_nonneg : ∀ r, 0 ≤ lam r) (hlam : ∑ r, lam r = 1)
    (hp_nonneg : ∀ r i, i < m → 0 ≤ p r i)
    (hmass : ∀ r, ∑ i ∈ range m, p r i = 1)
    (hsym : ∀ r i, i < m → p r (m-1-i) = p r i)
    (hw : ∀ r j, L*m ≤ j → w r j = 1)
    (hc : ∀ q ≤ L*m, 1 ≤ ∑ r, lam r * ∑ i ∈ range m, p r i*w r (q+i)) :
    (2:ℝ)/9 ≤ aValue m lam p * bValue m L lam w := by
  let μ : R × Fin m → ℝ := fun z => lam z.1
  let P : R × Fin m → ℝ := fun z => p z.1 z.2
  let M : R × Fin m → ℝ := fun z => midpoint (p z.1) z.2
  have hμ : ∀ z, 0 ≤ μ z := fun z => hlam_nonneg z.1
  have hM0 : ∀ z, 0 ≤ M z := fun z =>
    (midpoint_bounds (p z.1) m (hp_nonneg z.1) (hmass z.1) z.2 z.2.isLt).1
  have hM1 : ∀ z, M z ≤ 1 := fun z =>
    (midpoint_bounds (p z.1) m (hp_nonneg z.1) (hmass z.1) z.2 z.2.isLt).2
  have hs : (1:ℝ)/6 ≤ ∑ z, μ z * P z * (M z*(1-M z)) := by
    have he : (∑ z, μ z * P z * (M z*(1-M z))) =
        ∑ r, lam r * ∑ i ∈ range m,
          p r i * midpoint (p r) i * (1-midpoint (p r) i) := by
      dsimp [μ, P, M]
      rw [Fintype.sum_prod_type]
      apply sum_congr rfl
      intro r _
      dsimp only
      rw [Fin.sum_univ_eq_sum_range (fun i => lam r * p r i *
        (midpoint (p r) i * (1-midpoint (p r) i))) m, mul_sum]
      apply sum_congr rfl
      intro i _
      ring
    rw [he]
    calc
      (1:ℝ)/6 = ∑ r, lam r * ((1:ℝ)/6) := by rw [← sum_mul, hlam]; ring
      _ ≤ _ := by
        apply sum_le_sum
        intro r _
        exact mul_le_mul_of_nonneg_left
          (midpoint_moment_ge (p r) m (hp_nonneg r) (hmass r)) (hlam_nonneg r)
  have ha : aValue m lam p = (m:ℝ) * ∑ z, μ z * P z ^ 2 := by
    dsimp [aValue, μ, P]
    rw [Fintype.sum_prod_type]
    congr 1
    apply sum_congr rfl
    intro r _
    dsimp only
    rw [Fin.sum_univ_eq_sum_range (fun i => lam r * p r i ^ 2) m, mul_sum]
  have hd : 2 * (∑ z, μ z * (M z*(1-M z))) ≤ (m:ℝ) * bValue m L lam w := by
    have hd' := certificate_dual_bound m L hm hL lam p w
      hlam_nonneg hlam hmass hsym hw hc
    have he : (∑ z, μ z * (M z*(1-M z))) =
        ∑ r, lam r * ∑ i ∈ range m,
          midpoint (p r) i * (1-midpoint (p r) i) := by
      dsimp [μ, M]
      rw [Fintype.sum_prod_type]
      apply sum_congr rfl
      intro r _
      dsimp only
      rw [Fin.sum_univ_eq_sum_range (fun i => lam r *
        (midpoint (p r) i * (1-midpoint (p r) i))) m, mul_sum]
    rw [he]
    exact hd'
  exact rational_obstruction μ P M (aValue m lam p) (bValue m L lam w)
    (m:ℝ) hμ hM0 hM1 hs ha hd


/-- Algebraic combination of the midpoint moment and the q=0 remainder. -/
theorem rational_remainder_obstruction {ι : Type*} [Fintype ι]
    (μ p M V : ι → ℝ) (a b m : ℝ)
    (hμ : ∀ i, 0 ≤ μ i) (hM0 : ∀ i, 0 ≤ M i) (hM1 : ∀ i, M i ≤ 1)
    (hmoment : (1:ℝ)/6 ≤ ∑ i, μ i*p i*(M i*(1-M i)))
    (hpair : (1:ℝ)/2 ≤ ∑ i, μ i*p i*V i)
    (ha : a = m * ∑ i, μ i*p i^2)
    (henergy : 2*(∑ i, μ i*(M i*(1-M i))) + 2*(∑ i, μ i*V i^2) ≤ m*b) :
    (13:ℝ)/18 ≤ a*b := by
  have hA : 0 ≤ ∑ i, μ i*p i^2 :=
    sum_nonneg fun i _ => mul_nonneg (hμ i) (sq_nonneg _)
  have hAU := rational_obstruction μ p M
    (∑ i, μ i*p i^2) (2*(∑ i, μ i*(M i*(1-M i)))) 1
    hμ hM0 hM1 hmoment (by ring) (by simp)
  have hCS := weighted_cauchy μ p V hμ
  have hAS : (1:ℝ)/4 ≤ (∑ i, μ i*p i^2)*(∑ i, μ i*V i^2) := by
    nlinarith [sq_nonneg ((∑ i, μ i*p i*V i)-1/2)]
  have he := mul_le_mul_of_nonneg_left henergy hA
  rw [ha]
  nlinarith


/-- UNIVERSAL CERTIFICATE OBSTRUCTION, strengthened by the q=0 cover. -/
theorem certificate_product_lower_bound_13_18 {R : Type*} [Fintype R]
    (m L : ℕ) (hm : 0 < m) (hL : 0 < L)
    (lam : R → ℝ) (p w : R → ℕ → ℝ)
    (hlam_nonneg : ∀ r, 0 ≤ lam r) (hlam : ∑ r, lam r = 1)
    (hp_nonneg : ∀ r i, i < m → 0 ≤ p r i)
    (hmass : ∀ r, ∑ i ∈ range m, p r i = 1)
    (hsym : ∀ r i, i < m → p r (m-1-i) = p r i)
    (hw : ∀ r j, L*m ≤ j → w r j = 1)
    (hc : ∀ q ≤ L*m, 1 ≤ ∑ r, lam r * ∑ i ∈ range m, p r i*w r (q+i)) :
    (13:ℝ)/18 ≤ aValue m lam p * bValue m L lam w := by
  let μ : R × Fin m → ℝ := fun z => lam z.1
  let P : R × Fin m → ℝ := fun z => p z.1 z.2
  let M : R × Fin m → ℝ := fun z => midpoint (p z.1) z.2
  let V : R × Fin m → ℝ := fun z => w z.1 z.2-midpoint (p z.1) z.2
  have hμ : ∀ z, 0 ≤ μ z := fun z => hlam_nonneg z.1
  have hM0 : ∀ z, 0 ≤ M z := fun z =>
    (midpoint_bounds (p z.1) m (hp_nonneg z.1) (hmass z.1) z.2 z.2.isLt).1
  have hM1 : ∀ z, M z ≤ 1 := fun z =>
    (midpoint_bounds (p z.1) m (hp_nonneg z.1) (hmass z.1) z.2 z.2.isLt).2
  have hs : (1:ℝ)/6 ≤ ∑ z, μ z * P z * (M z*(1-M z)) := by
    have he : (∑ z, μ z * P z * (M z*(1-M z))) =
        ∑ r, lam r * ∑ i ∈ range m,
          p r i * midpoint (p r) i * (1-midpoint (p r) i) := by
      dsimp [μ, P, M]
      rw [Fintype.sum_prod_type]
      apply sum_congr rfl
      intro r _
      dsimp only
      rw [Fin.sum_univ_eq_sum_range (fun i => lam r * p r i *
        (midpoint (p r) i * (1-midpoint (p r) i))) m, mul_sum]
      apply sum_congr rfl
      intro i _
      ring
    rw [he]
    calc
      (1:ℝ)/6 = ∑ r, lam r * ((1:ℝ)/6) := by rw [← sum_mul, hlam]; ring
      _ ≤ _ := by
        apply sum_le_sum
        intro r _
        exact mul_le_mul_of_nonneg_left
          (midpoint_moment_ge (p r) m (hp_nonneg r) (hmass r)) (hlam_nonneg r)
  have ha : aValue m lam p = (m:ℝ) * ∑ z, μ z * P z ^ 2 := by
    dsimp [aValue, μ, P]
    rw [Fintype.sum_prod_type]
    congr 1
    apply sum_congr rfl
    intro r _
    dsimp only
    rw [Fin.sum_univ_eq_sum_range (fun i => lam r * p r i ^ 2) m, mul_sum]
  have hpair : (1:ℝ)/2 ≤ ∑ z, μ z*P z*V z := by
    have he : (∑ z, μ z*P z*V z) =
        ∑ r, lam r * ∑ i ∈ range m, p r i*(w r i-midpoint (p r) i) := by
      dsimp [μ, P, V]
      rw [Fintype.sum_prod_type]
      apply sum_congr rfl
      intro r _
      dsimp only
      rw [Fin.sum_univ_eq_sum_range (fun i =>
        lam r*p r i*(w r i-midpoint (p r) i)) m, mul_sum]
      apply sum_congr rfl
      intro i _
      ring
    have hPm : ∀ r, (∑ i ∈ range m, p r i*midpoint (p r) i) = (1:ℝ)/2 :=
      fun r => midpoint_pairing (p r) m (hmass r)
    rw [he]
    simp_rw [mul_sub, sum_sub_distrib, hPm, mul_sub]
    rw [sum_sub_distrib, ← sum_mul, hlam]
    have h0 : 1 ≤ ∑ r, lam r*∑ i ∈ range m, p r i*w r i := by
      simpa only [zero_add] using hc 0 (by omega)
    linarith
  have hd : 2*(∑ z, μ z*(M z*(1-M z))) + 2*(∑ z, μ z*V z^2) ≤
      (m:ℝ)*bValue m L lam w := by
    have hd' := certificate_remainder_bound m L hm hL lam p w
      hlam_nonneg hlam hmass hsym hw hc
    have heU : (∑ z, μ z*(M z*(1-M z))) =
        ∑ r, lam r*∑ i ∈ range m, midpoint (p r) i*(1-midpoint (p r) i) := by
      dsimp [μ, M]
      rw [Fintype.sum_prod_type]
      apply sum_congr rfl
      intro r _
      dsimp only
      rw [Fin.sum_univ_eq_sum_range (fun i =>
        lam r*(midpoint (p r) i*(1-midpoint (p r) i))) m, mul_sum]
    have heS : (∑ z, μ z*V z^2) =
        ∑ r, lam r*∑ i ∈ range m, (w r i-midpoint (p r) i)^2 := by
      dsimp [μ, V]
      rw [Fintype.sum_prod_type]
      apply sum_congr rfl
      intro r _
      dsimp only
      rw [Fin.sum_univ_eq_sum_range (fun i =>
        lam r*(w r i-midpoint (p r) i)^2) m, mul_sum]
    rw [heU, heS]
    exact hd'
  exact rational_remainder_obstruction μ P M V (aValue m lam p)
    (bValue m L lam w) (m:ℝ) hμ hM0 hM1 hs hpair ha hd


#print axioms midpoint_moment_identity
#print axioms midpoint_moment_ge
#print axioms dual_square_completion
#print axioms weighted_cauchy
#print axioms rational_obstruction
#print axioms certificate_dual_bound
#print axioms certificate_product_lower_bound
#print axioms certificate_remainder_bound
#print axioms certificate_product_lower_bound_13_18

end SmoothingLimit

namespace Submissions.Erdos30SmoothingBarrier13_18.Declan
open Finset

theorem proof : ∀ (R m L : ℕ), 0 < m → 0 < L →
    ∀ (lam : Fin R → ℝ) (p w : Fin R → ℕ → ℝ),
    (∀ r, 0 ≤ lam r) → (∑ r, lam r = 1) →
    (∀ r i, i < m → 0 ≤ p r i) →
    (∀ r, ∑ i ∈ range m, p r i = 1) →
    (∀ r i, i < m → p r (m-1-i) = p r i) →
    (∀ r j, L*m ≤ j → w r j = 1) →
    (∀ q ≤ L*m, 1 ≤ ∑ r, lam r * ∑ i ∈ range m, p r i*w r (q+i)) →
    (13:ℝ)/18 ≤
      ((m:ℝ) * ∑ r, lam r * ∑ i ∈ range m, p r i ^ 2) *
      (1 + 2 * ((∑ r, lam r * ∑ j ∈ range (L*m), w r j ^ 2)/(m:ℝ) - L)) := by
  intro R m L hm hL lam p w hlam_nonneg hlam hp_nonneg hmass hsym hw hc
  exact SmoothingLimit.certificate_product_lower_bound_13_18 m L hm hL lam p w
    hlam_nonneg hlam hp_nonneg hmass hsym hw hc
end Submissions.Erdos30SmoothingBarrier13_18.Declan
