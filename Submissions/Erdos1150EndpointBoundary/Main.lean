import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-
Standalone Lean-checked endpoint bound, with finite domain controls.
The iSup theorem uses only propext, Classical.choice, and Quot.sound.
Jig canonical-bridge verification is a separate step; the full fixed-gap
problem is not resolved by this additive n+3 squared-modulus bound.
-/

open Finset
open scoped ComplexConjugate Polynomial

namespace Submissions.Erdos1150EndpointBoundary.Main

variable {N : ℕ} [NeZero N]

private lemma character_orthogonality (i j : ZMod N) :
    (∑ k : ZMod N,
      conj (ZMod.stdAddChar (k * i)) * ZMod.stdAddChar (k * j)) =
        if i = j then (N : ℂ) else 0 := by
  have hphase (k : ZMod N) :
      conj (ZMod.stdAddChar (k * i)) * ZMod.stdAddChar (k * j) =
        ZMod.stdAddChar (k * (j - i)) := by
    rw [← AddChar.map_neg_eq_conj, ← AddChar.map_add_eq_mul]
    congr 1
    ring
  simp_rw [hphase]
  rw [AddChar.sum_mulShift _ (ZMod.isPrimitive_stdAddChar N)]
  simp [sub_eq_zero, eq_comm]

/-- Unnormalized finite Parseval, with the positive character convention. -/
theorem sum_normSq_fourier (b : ZMod N → ℂ) :
    (∑ k : ZMod N, Complex.normSq
      (∑ j : ZMod N, b j * ZMod.stdAddChar (k * j))) =
        (N : ℝ) * ∑ j : ZMod N, Complex.normSq (b j) := by
  have hcomplex :
      (∑ k : ZMod N,
        conj (∑ j : ZMod N, b j * ZMod.stdAddChar (k * j)) *
          (∑ j : ZMod N, b j * ZMod.stdAddChar (k * j))) =
        (N : ℂ) * ∑ j : ZMod N, conj (b j) * b j := by
    calc
      _ = ∑ k : ZMod N, ∑ i : ZMod N, ∑ j : ZMod N,
          (conj (b i) * b j) *
            (conj (ZMod.stdAddChar (k * i)) * ZMod.stdAddChar (k * j)) := by
        apply sum_congr rfl
        intro k hk
        simp only [map_sum, map_mul, sum_mul, mul_sum]
        rw [sum_comm]
        apply sum_congr rfl
        intro i hi
        apply sum_congr rfl
        intro j hj
        ring
      _ = ∑ i : ZMod N, ∑ j : ZMod N,
          (conj (b i) * b j) *
            (∑ k : ZMod N,
              conj (ZMod.stdAddChar (k * i)) * ZMod.stdAddChar (k * j)) := by
        simp only [mul_sum]
        rw [sum_comm]
        apply sum_congr rfl
        intro i hi
        rw [sum_comm]
      _ = (N : ℂ) * ∑ j : ZMod N, conj (b j) * b j := by
        simp_rw [character_orthogonality]
        simp [mul_comm, mul_sum]
  apply Complex.ofReal_injective
  push_cast
  simpa only [Complex.normSq_eq_conj_mul_self] using hcomplex

/-- At least one finite Fourier sample attains its mean squared modulus. -/
theorem exists_normSq_fourier_ge (b : ZMod N → ℂ) :
    ∃ k : ZMod N, (∑ j : ZMod N, Complex.normSq (b j)) ≤
      Complex.normSq (∑ j : ZMod N, b j * ZMod.stdAddChar (k * j)) := by
  by_contra! h
  have hlt :
      (∑ k : ZMod N, Complex.normSq
        (∑ j : ZMod N, b j * ZMod.stdAddChar (k * j))) <
      ∑ _k : ZMod N, (∑ j : ZMod N, Complex.normSq (b j)) :=
    sum_lt_sum_of_nonempty univ_nonempty (fun k _hk ↦ h k)
  rw [sum_normSq_fourier] at hlt
  simp [ZMod.card] at hlt

private lemma sum_range_eq_sum_zmod (f : ℕ → ℂ) :
    (∑ i ∈ range N, f i) = ∑ j : ZMod N, f j.val := by
  refine sum_bij (fun i _hi ↦ (i : ZMod N))
    (fun _i _hi ↦ mem_univ _) ?_ ?_ ?_
  · intro i hi j hj hij
    have hv := congrArg ZMod.val hij
    simpa only [ZMod.val_natCast_of_lt (mem_range.mp hi),
      ZMod.val_natCast_of_lt (mem_range.mp hj)] using hv
  · intro j _hj
    exact ⟨j.val, mem_range.mpr j.val_lt, ZMod.natCast_zmod_val j⟩
  · intro i hi
    rw [ZMod.val_natCast_of_lt (mem_range.mp hi)]

private lemma stdAddChar_pow (k : ZMod N) (m : ℕ) :
    ZMod.stdAddChar k ^ m = ZMod.stdAddChar (k * (m : ZMod N)) := by
  rw [← AddChar.map_nsmul_eq_pow, nsmul_eq_mul, mul_comm]

private lemma exists_endpoint_rotation (a d : ℂ)
    (ha : a = -1 ∨ a = 1) (hd : d = -1 ∨ d = 1) :
    ∃ w : ℂ, ‖w‖ = 1 ∧ d * w ^ N = a := by
  obtain ⟨w, hw⟩ := IsAlgClosed.exists_pow_nat_eq (a * d) (NeZero.pos N)
  have hp : w ^ (N * 2) = 1 := by
    rw [pow_mul, hw]
    rcases ha with rfl | rfl <;> rcases hd with rfl | rfl <;> norm_num
  refine ⟨w, Complex.norm_eq_one_of_pow_eq_one hp
    (Nat.mul_ne_zero (NeZero.ne N) (by decide)), ?_⟩
  rw [hw]
  rcases ha with rfl | rfl <;> rcases hd with rfl | rfl <;> norm_num

/-- For `N + 1` signs, the squared modulus is at least `N + 3` at a unit point. -/
theorem exists_sum_norm_sq_ge (a : ℕ → ℂ)
    (ha : ∀ i ≤ N, a i = -1 ∨ a i = 1) :
    ∃ z : ℂ, ‖z‖ = 1 ∧ (N : ℝ) + 3 ≤
      ‖∑ i ∈ range (N + 1), a i * z ^ i‖ ^ 2 := by
  obtain ⟨w, hwNorm, hw⟩ := exists_endpoint_rotation (N := N)
    (a 0) (a N) (ha 0 (Nat.zero_le N)) (ha N le_rfl)
  let b : ZMod N → ℂ := fun j ↦
    a j.val * w ^ j.val + if j = 0 then a 0 else 0
  have hfold (k : ZMod N) :
      (∑ j : ZMod N, b j * ZMod.stdAddChar (k * j)) =
        ∑ i ∈ range (N + 1), a i * (w * ZMod.stdAddChar k) ^ i := by
    calc
      _ = (∑ j : ZMod N,
          a j.val * w ^ j.val * ZMod.stdAddChar (k * j)) + a 0 := by
        simp [b, add_mul, sum_add_distrib, ite_mul]
      _ = (∑ i ∈ range N, a i * (w * ZMod.stdAddChar k) ^ i) + a 0 := by
        congr 1
        rw [sum_range_eq_sum_zmod]
        apply sum_congr rfl
        intro j _hj
        rw [mul_pow, stdAddChar_pow, ZMod.natCast_zmod_val]
        ring
      _ = _ := by
        simp [sum_range_succ, mul_pow, stdAddChar_pow, hw]
  have hbnorm (j : ZMod N) :
      Complex.normSq (b j) = 1 + if j = 0 then 3 else 0 := by
    by_cases hj : j = 0
    · subst j
      rcases ha 0 (Nat.zero_le N) with h0 | h0 <;>
        norm_num [b, h0]
    · have haj : ‖a j.val‖ = 1 := by
        rcases ha j.val j.val_lt.le with hj' | hj' <;> simp [hj']
      simp [b, hj, Complex.normSq_eq_norm_sq, norm_pow, hwNorm, haj]
  have hsum : (∑ j : ZMod N, Complex.normSq (b j)) = (N : ℝ) + 3 := by
    simp_rw [hbnorm]
    simp [sum_add_distrib, ZMod.card]
  obtain ⟨k, hk⟩ := exists_normSq_fourier_ge b
  refine ⟨w * ZMod.stdAddChar k, ?_, ?_⟩
  · simp [hwNorm, AddChar.norm_apply]
  · rw [hsum, hfold] at hk
    simpa only [Complex.normSq_eq_norm_sq] using hk

/-- Endpoint improvement over Parseval for every positive-degree Littlewood polynomial. -/
theorem exists_eval_norm_sq_ge (P : ℂ[X]) (hpos : 0 < P.natDegree)
    (ha : ∀ i ≤ P.natDegree, P.coeff i = -1 ∨ P.coeff i = 1) :
    ∃ z : ℂ, ‖z‖ = 1 ∧ (P.natDegree : ℝ) + 3 ≤ ‖P.eval z‖ ^ 2 := by
  let : NeZero P.natDegree := ⟨hpos.ne'⟩
  obtain ⟨z, hz, h⟩ := exists_sum_norm_sq_ge (N := P.natDegree) P.coeff ha
  refine ⟨z, hz, ?_⟩
  rwa [← Polynomial.eval_eq_sum_range z] at h

/-- The exact unit-circle supremum is at least the endpoint-improved Parseval bound. -/
theorem sqrt_degree_add_three_le_iSup (P : ℂ[X]) (hpos : 0 < P.natDegree)
    (ha : ∀ i ≤ P.natDegree, P.coeff i = -1 ∨ P.coeff i = 1) :
    Real.sqrt ((P.natDegree : ℝ) + 3) ≤
      ⨆ z : Metric.sphere (0 : ℂ) 1, ‖P.eval (z : ℂ)‖ := by
  obtain ⟨z, hz, hsq⟩ := exists_eval_norm_sq_ge P hpos ha
  have hsqrt : Real.sqrt ((P.natDegree : ℝ) + 3) ≤ ‖P.eval z‖ :=
    (Real.sqrt_le_left (norm_nonneg _)).mpr hsq
  obtain ⟨M, hM⟩ :=
    (isCompact_sphere (0 : ℂ) 1).bddAbove_image P.continuous.norm.continuousOn
  have hbdd : BddAbove (Set.range fun v : Metric.sphere (0 : ℂ) 1 ↦
      ‖P.eval (v : ℂ)‖) := by
    refine ⟨M, ?_⟩
    rintro _ ⟨v, rfl⟩
    exact hM ⟨v, v.property, rfl⟩
  have hzSphere : z ∈ Metric.sphere (0 : ℂ) 1 := by
    simpa [Metric.mem_sphere, dist_zero_right] using hz
  exact hsqrt.trans (le_ciSup_of_le hbdd ⟨z, hzSphere⟩ le_rfl)

-- Decisive finite controls for endpoint sign alignment and the theorem's domain.
example : ‖(1 + Polynomial.X : ℂ[X]).eval 1‖ ^ 2 = (4 : ℝ) := by
  norm_num

example : ‖(1 - Polynomial.X : ℂ[X]).eval (-1)‖ ^ 2 = (4 : ℝ) := by
  norm_num

example : ¬ 0 < (1 : ℂ[X]).natDegree := by simp

example : ‖(1 : ℂ[X]).eval 1‖ ^ 2 < ((1 : ℂ[X]).natDegree : ℝ) + 3 := by
  norm_num

example : ¬ (∀ i ≤ (1 + Polynomial.X ^ 2 : ℂ[X]).natDegree,
    (1 + Polynomial.X ^ 2 : ℂ[X]).coeff i = -1 ∨
      (1 + Polynomial.X ^ 2 : ℂ[X]).coeff i = 1) := by
  have hdeg : (1 + Polynomial.X ^ 2 : ℂ[X]).natDegree = 2 := by
    simpa only [Polynomial.C_1, add_comm] using
      (Polynomial.natDegree_X_pow_add_C (R := ℂ) (n := 2) (r := 1))
  intro h
  have h1 := h 1 (by rw [hdeg]; decide)
  norm_num [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_one] at h1

theorem proof :
    ∀ (P : ℂ[X]) (n : ℕ),
      (∀ i ≤ P.natDegree, P.coeff i = -1 ∨ P.coeff i = 1) →
      P.natDegree = n → 0 < n →
        (⨆ z : Metric.sphere (0 : ℂ) 1, ‖P.eval (z : ℂ)‖) ≥
          Real.sqrt ((n : ℝ) + 3) := by
  intro P n ha hdeg hpos
  subst n
  exact sqrt_degree_add_three_le_iSup P hpos ha

end Submissions.Erdos1150EndpointBoundary.Main
