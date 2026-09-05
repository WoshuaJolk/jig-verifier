import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.LinearAlgebra.Matrix.Integer
import Mathlib.NumberTheory.Padics.PadicNorm
import Mathlib.Data.Rat.Lemmas
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.PrimeFin
import Mathlib.Data.Finset.Prod
import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false

/-!
Port of Epoch AI's publicly released GPT-6 Astra proof of Erdős126.
This ports an existing mathematical solution and does not claim novelty.
Source: https://github.com/epoch-research/LeanOpenProblems-results/blob/main/runs/bloom68-vega-hxlmrsfzzg3h01o7/Erdos126.erdos_126/Submission/Spec.lean
Summary: https://epoch.ai/files/frontiermath-erdos.pdf (Appendix B.3).
The isolated benchmark file ended with an unused unproved negation; that
unused declaration is omitted here, while the accepted proof is retained.
-/

/-!
# Erdős Problem 126

*Reference:* [erdosproblems.com/126](https://www.erdosproblems.com/126)
-/

open Filter

/-
## A polynomial bound for restricted-sum cliques

For positive vertices, use the reduced denominator of `2 * a / (a + b)`.
A normalized Cauchy determinant bounds the number of vertices sharing a high
prime power in this denominator. A denominator quasi-triangle inequality then
covers the whole set by two families of such balls, giving a cubic bound in
the number of supporting primes. Removing a possible zero costs one vertex.
-/

namespace Erdos126Adelic

open scoped Matrix

/-- One Schur-complement step for the normalized Cauchy kernel. -/
theorem cauchy_schur_step (a b c : ℚ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    2*b/(b+c) - (2*b/(b+a))*(2*a/(a+c)) =
      ((b-a)/(b+a)) * (2*b/(b+c)) * ((c-a)/(c+a)) := by
  have hba : b+a ≠ 0 := ne_of_gt (add_pos hb ha)
  have hbc : b+c ≠ 0 := ne_of_gt (add_pos hb hc)
  have hac : a+c ≠ 0 := ne_of_gt (add_pos ha hc)
  have hca : c+a ≠ 0 := ne_of_gt (add_pos hc ha)
  field_simp; ring

/-- General-dimensional determinant step; iteration is Cauchy's formula. -/
theorem normalized_block_det {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : ℚ) (b : ι → ℚ) (ha : 0 < a) (hb : ∀ i, 0 < b i) :
    (Matrix.fromBlocks (1 : Matrix Unit Unit ℚ)
      (Matrix.of (fun (_ : Unit) j => 2*a/(a+b j)))
      (Matrix.of (fun i (_ : Unit) => 2*b i/(b i+a)))
      (Matrix.of (fun i j => 2*b i/(b i+b j)))).det =
      (∏ i, (b i-a)/(b i+a))^2 *
        (Matrix.of (fun i j => 2*b i/(b i+b j))).det := by
  rw [Matrix.det_fromBlocks_one₁₁]
  let w : ι → ℚ := fun i => (b i-a)/(b i+a)
  let M : Matrix ι ι ℚ := fun i j => 2*b i/(b i+b j)
  have heq : M - (Matrix.of (fun i (_ : Unit) => 2*b i/(b i+a))) *
      (Matrix.of (fun (_ : Unit) j => 2*a/(a+b j))) =
      Matrix.diagonal w * M * Matrix.diagonal w := by
    ext i j
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
    simp only [Matrix.sub_apply, Matrix.mul_apply,
      Finset.univ_unique, Finset.sum_singleton, Matrix.of_apply, M, w]
    exact cauchy_schur_step a (b i) (b j) ha (hb i) (hb j)
  change (M - _).det = _
  rw [heq]
  simp only [Matrix.det_mul, Matrix.det_diagonal]
  change (∏ i, w i) * M.det * (∏ i, w i) = (∏ i, w i)^2 * M.det
  ring

/-- Reindexing by a distinguished first row and column. -/
def headTailEquiv (n : ℕ) : Unit ⊕ Fin n ≃ Fin (n+1) where
  toFun := Sum.elim (fun _ => 0) Fin.succ
  invFun := Fin.cases (Sum.inl ()) Sum.inr
  left_inv x := by
    rcases x with u | i
    · cases u
      rfl
    · simp
  right_inv i := by
    refine Fin.cases ?_ (fun j => ?_) i <;> simp

/-- The rational normalized Cauchy matrix. -/
def normCauchy {n : ℕ} (b : Fin n → ℚ) : Matrix (Fin n) (Fin n) ℚ :=
  Matrix.of (fun i j => 2*b i/(b i+b j))

/-- The determinant recurrence in its ordinary finite-indexed form. -/
theorem normalized_succ_det {n : ℕ} (b : Fin (n+1) → ℚ) (hb : ∀ i, 0 < b i) :
    (normCauchy b).det =
      (∏ i : Fin n, (b i.succ-b 0)/(b i.succ+b 0))^2 *
        (normCauchy (fun i : Fin n => b i.succ)).det := by
  have h := normalized_block_det (b 0) (fun i : Fin n => b i.succ) (hb 0)
    (fun i => hb i.succ)
  have heq : (normCauchy b).submatrix (headTailEquiv n) (headTailEquiv n) =
      Matrix.fromBlocks (1 : Matrix Unit Unit ℚ)
        (Matrix.of (fun (_ : Unit) j => 2*b 0/(b 0+b j.succ)))
        (Matrix.of (fun i (_ : Unit) => 2*b i.succ/(b i.succ+b 0)))
        (normCauchy (fun i : Fin n => b i.succ)) := by
    ext i j
    rcases i with u | i <;> rcases j with v | j
    · cases u
      cases v
      simp [normCauchy, headTailEquiv]
      field_simp [ne_of_gt (hb 0)]; ring
    · cases u
      rfl
    · cases v
      rfl
    · rfl
  rw [← Matrix.det_submatrix_equiv_self (headTailEquiv n) (normCauchy b), heq]
  exact h

/-- A branch-free expression for Cauchy's product over unordered pairs. -/
def cauchyProduct {n : ℕ} (b : Fin n → ℚ) : ℚ :=
  ∏ i : Fin n, ∏ j : Fin n, if i < j then ((b i-b j)/(b i+b j))^2 else 1

/-- The exact principal Cauchy determinant, in all finite dimensions. -/
theorem normalized_cauchy_det {n : ℕ} (b : Fin n → ℚ) (hb : ∀ i, 0 < b i) :
    (normCauchy b).det = cauchyProduct b := by
  induction n with
  | zero => simp [cauchyProduct]
  | succ n ih =>
    rw [normalized_succ_det b hb, ih (fun i => b i.succ) (fun i => hb i.succ)]
    have hs : cauchyProduct b =
        (∏ i : Fin n, ((b 0-b i.succ)/(b 0+b i.succ))^2) *
          cauchyProduct (fun i : Fin n => b i.succ) := by
      simp [cauchyProduct, Fin.prod_univ_succ]
    rw [hs]
    congr 1
    rw [← Finset.prod_pow]
    apply Finset.prod_congr rfl
    intro i hi
    rw [add_comm (b 0) (b i.succ)]
    ring

/-- The ordinary positive-real bounds, proved from the full product formula. -/
theorem normalized_cauchy_det_bounds {n : ℕ} (b : Fin n → ℚ)
    (hb : ∀ i, 0 < b i) (hi : Function.Injective b) :
    0 < (normCauchy b).det ∧ (normCauchy b).det ≤ 1 := by
  have hf : ∀ i j : Fin n,
      0 < (if i < j then ((b i-b j)/(b i+b j))^2 else 1 : ℚ) ∧
      (if i < j then ((b i-b j)/(b i+b j))^2 else 1 : ℚ) ≤ 1 := by
    intro i j
    split_ifs with hij
    · have hne : b i - b j ≠ 0 := sub_ne_zero.mpr (hi.ne hij.ne)
      have hd : 0 < b i+b j := add_pos (hb i) (hb j)
      constructor
      · exact sq_pos_of_ne_zero (div_ne_zero hne (ne_of_gt hd))
      · rw [div_pow]
        apply (div_le_one (sq_pos_of_pos hd)).2
        nlinarith [mul_pos (hb i) (hb j)]
    · norm_num
  rw [normalized_cauchy_det b hb]
  dsimp [cauchyProduct]
  constructor
  · apply Finset.prod_pos
    intro i _
    apply Finset.prod_pos
    intro j _
    exact (hf i j).1
  · apply Finset.prod_le_one
    · intro i _
      exact le_of_lt (Finset.prod_pos (fun j _ => (hf i j).1))
    · intro i _
      exact Finset.prod_le_one (fun j _ => (hf i j).1.le) (fun j _ => (hf i j).2)

/-- A bundled multiplicative p-adic norm for finite products. -/
def pnHom (p : ℕ) [Fact p.Prime] : ℚ →* ℚ where
  toFun := padicNorm p
  map_one' := padicNorm.one
  map_mul' := padicNorm.mul

/-- Quadratic p-adic gain for a complete principal block. -/
theorem normalized_cauchy_norm_bound (p : ℕ) [Fact p.Prime] {n : ℕ}
    (b : Fin n → ℚ) (hb : ∀ i, 0 < b i) (ρ : ℚ) (_hρ : 0 ≤ ρ)
    (hd : ∀ i j, i ≠ j → padicNorm p ((b i-b j)/(b i+b j)) ≤ ρ) :
    padicNorm p (normCauchy b).det ≤ ρ^(n*(n-1)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [normalized_succ_det b hb, padicNorm.mul, IsAbsoluteValue.abv_pow (padicNorm p)]
    have hprod : padicNorm p (∏ i : Fin n, (b i.succ-b 0)/(b i.succ+b 0)) ≤ ρ^n := by
      calc
        padicNorm p (∏ i : Fin n, (b i.succ-b 0)/(b i.succ+b 0)) =
            ∏ i : Fin n, padicNorm p ((b i.succ-b 0)/(b i.succ+b 0)) := by
          exact map_prod (pnHom p) _ _
        _ ≤ ∏ _i : Fin n, ρ := Finset.prod_le_prod
          (fun i _ => padicNorm.nonneg _) (fun i _ => hd i.succ 0 (Fin.succ_ne_zero i))
        _ = ρ^n := by simp
    have hsquare : (padicNorm p (∏ i : Fin n, (b i.succ-b 0)/(b i.succ+b 0)))^2 ≤ (ρ^n)^2 :=
      pow_le_pow_left₀ (padicNorm.nonneg _) hprod 2
    have htail := ih (fun i => b i.succ) (fun i => hb i.succ)
      (fun i j h => hd i.succ j.succ (Fin.succ_injective n |>.ne h))
    have hmul := mul_le_mul hsquare htail (padicNorm.nonneg _) (sq_nonneg (ρ^n))
    have hex : n*2+n*(n-1) = (n+1)*((n+1)-1) := by
      cases n <;> simp; ring
    simpa [← pow_mul, ← pow_add, hex] using hmul

/-- Clearing a common entry denominator clears the determinant to its dimension. -/
theorem scaled_det_integral {n : ℕ} (M : Matrix (Fin n) (Fin n) ℚ) (Q : ℕ)
    (hd : ∀ i j, (M i j).den ∣ Q) : ∃ z : ℤ, (z : ℚ) = (Q : ℚ)^n*M.det := by
  let Z : Matrix (Fin n) (Fin n) ℤ :=
    Matrix.of (fun i j => (M i j).num * (Q/(M i j).den : ℕ))
  have heq : Z.map (fun x : ℤ => (x : ℚ)) = (Q : ℚ) • M := by
    ext i j
    simp only [Z, Matrix.map_apply, Matrix.of_apply, Int.cast_mul,
      Int.cast_natCast, Matrix.smul_apply, smul_eq_mul]
    rw [← Rat.mul_den_eq_num]
    have hQ : ((Q/(M i j).den : ℕ) : ℚ) * (M i j).den = Q := by
      exact_mod_cast Nat.div_mul_cancel (hd i j)
    calc
      (M i j * (M i j).den) * (Q/(M i j).den : ℕ) =
          (((Q/(M i j).den : ℕ) : ℚ) * (M i j).den) * M i j := by ring
      _ = (Q : ℚ)*M i j := by rw [hQ]
  refine ⟨Z.det, ?_⟩
  rw [Int.cast_det, heq, Matrix.det_smul]
  simp

/-- The elementary expression behind the denominator quasi-triangle bound. -/
theorem transport_identity (a b c : ℚ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    2*a/(a+b) =
      ((2*a/(a+c))*(2-2*b/(b+c))) /
        ((2*a/(a+c)) + (2*b/(b+c)) - (2*a/(a+c))*(2*b/(b+c))) := by
  have hac : a+c ≠ 0 := ne_of_gt (add_pos ha hc)
  have hbc : b+c ≠ 0 := ne_of_gt (add_pos hb hc)
  have hab : a+b ≠ 0 := ne_of_gt (add_pos ha hb)
  have hc0 : c ≠ 0 := ne_of_gt hc
  have hden : (2*a/(a+c)) + (2*b/(b+c)) - (2*a/(a+c))*(2*b/(b+c)) =
      2*c*(a+b)/((a+c)*(b+c)) := by
    field_simp; ring
  rw [hden]
  field_simp; ring

/-- Positivity prevents the intermediate integer denominator from vanishing. -/
theorem transport_den_bounds (x y : ℚ)
    (hx : 0 < x) (hx2 : x < 2) (hy : 0 < y) (hy2 : y < 2) :
    0 < x+y-x*y ∧ x+y-x*y < 2 := by
  constructor
  · have h₁ := mul_pos hx (sub_pos.mpr hy2)
    have h₂ := mul_pos hy (sub_pos.mpr hx2)
    nlinarith
  · have h₁ := mul_pos hx hy
    have h₂ := mul_pos (sub_pos.mpr hx2) (sub_pos.mpr hy2)
    nlinarith

/-- The two-endpoint covering step, stated without logarithms or roots. -/
theorem far_endpoint (T x y : ℝ) (hT : 4 ≤ T)
    (hx : 0 < x) (hy : 0 < y) (h : T < 2*x*y) :
    T < x^4 ∨ T < y^4 := by
  by_contra hf
  push_neg at hf
  have hm : x^2*y^2 ≤ T := by
    nlinarith [sq_nonneg (x^2-y^2)]
  have hp : T^2 < (2*x*y)^2 := by
    exact sq_lt_sq₀ (by linarith) (by positivity) |>.2 h
  nlinarith

/-- Uniform local transfer, including p=2, after the normalization by 2a. -/
theorem small_padic_ball_ratio (p : ℕ) [Fact p.Prime] (t u ρ : ℚ)
    (hρ : ρ < 1) (ht : padicNorm p t ≤ ρ) (hu : padicNorm p u ≤ ρ) :
    padicNorm p ((t-u)/(t+u-1)) ≤ ρ := by
  have hsum : padicNorm p (t+u) ≤ ρ :=
    padicNorm.nonarchimedean.trans (max_le ht hu)
  have hne : padicNorm p (t+u) ≠ padicNorm p (-1) := by
    simpa using ne_of_lt (hsum.trans_lt hρ)
  have hden : padicNorm p (t+u-1) = 1 := by
    rw [sub_eq_add_neg, padicNorm.add_eq_max_of_ne hne]
    simpa using max_eq_right (hsum.trans hρ.le)
  rw [padicNorm.div, hden, div_one]
  exact padicNorm.sub.trans (max_le ht hu)

/-- Algebraic form of the local transfer for genuine vertices. -/
theorem ball_ratio_identity (a b c : ℚ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    (b-c)/(b+c) =
      (((a+b)/(2*a))-((a+c)/(2*a))) /
        (((a+b)/(2*a))+((a+c)/(2*a))-1) := by
  have ha0 := ne_of_gt ha
  have hbc : b+c ≠ 0 := ne_of_gt (add_pos hb hc)
  have hden : ((a+b)/(2*a))+((a+c)/(2*a))-1 = (b+c)/(2*a) := by
    field_simp; ring
  rw [hden]
  field_simp; ring

/-- A power in a reduced denominator makes the reciprocal p-adically small. -/
theorem reciprocal_norm_of_den_dvd (p e : ℕ) [hp : Fact p.Prime] (q : ℚ)
    (he : 1 ≤ e) (hd : p^e ∣ q.den) :
    padicNorm p q⁻¹ ≤ (p : ℚ)^(-(e : ℤ)) := by
  have hpd : p ∣ q.den := Nat.dvd_of_pow_dvd he hd
  have hn : ¬(p : ℤ) ∣ q.num := by
    intro hn
    have hpnum : p ∣ q.num.natAbs := Int.natCast_dvd.mp hn
    have hg : p ∣ q.num.natAbs.gcd q.den := Nat.dvd_gcd hpnum hpd
    rw [q.reduced.gcd_eq_one] at hg
    have hpeq : p = 1 := Nat.eq_one_of_dvd_one hg
    exact hp.out.ne_one hpeq
  rw [Rat.inv_def, Rat.divInt_eq_div, padicNorm.div,
    (padicNorm.int_eq_one_iff q.num).mpr hn, div_one]
  exact padicNorm.dvd_iff_norm_le.mp (Int.natCast_dvd_natCast.mpr hd)

/-- Divisibility plus the strict real determinant bound gives the height tax. -/
theorem integer_power_tax (p e m Q z : ℕ) (hm : 0 < m) (hz : 0 < z)
    (hdiv : p^(m*(m-1)*e) ∣ z) (hsmall : z < Q^m) :
    p^((m-1)*e) < Q := by
  have hle : p^(m*(m-1)*e) ≤ z := Nat.le_of_dvd hz hdiv
  have hp : (p^((m-1)*e))^m < Q^m := by
    calc
      (p^((m-1)*e))^m = p^(m*(m-1)*e) := by
        rw [← pow_mul]
        congr 1
        ring
      _ ≤ z := hle
      _ < Q^m := hsmall
  exact (Nat.pow_lt_pow_iff_left (ne_of_gt hm)).mp hp

/-- The complete many-anchor arithmetic height tax, with every normalization explicit.
No S-unit theorem is an input. The denominator bound Q is shared by the whole block. -/
theorem denominator_ball_tax (p e m Q : ℕ) [hp : Fact p.Prime]
    (a : ℚ) (b : Fin m → ℚ) (ha : 0 < a) (hb : ∀ i, 0 < b i)
    (hi : Function.Injective b) (hm : 0 < m) (hQ : 0 < Q) (he : 1 ≤ e)
    (hball : ∀ i, p^e ∣ (2*a/(a+b i)).den)
    (hclear : ∀ i j, (2*b i/(b i+b j)).den ∣ Q) :
    p^((m-1)*e) ≤ Q := by
  let ρ : ℚ := (p : ℚ)^(-(e : ℤ))
  have hpQ : (1 : ℚ) < p := by exact_mod_cast hp.out.one_lt
  have hρpos : 0 < ρ := zpow_pos (lt_trans (by norm_num) hpQ) _
  have hρlt : ρ < 1 := by
    dsimp [ρ]
    calc
      (p : ℚ)^(-(e : ℤ)) < (p : ℚ)^(0 : ℤ) := by
        apply (zpow_lt_zpow_iff_right₀ hpQ).2
        omega
      _ = 1 := zpow_zero _
  have hsmall : ∀ i, padicNorm p ((a+b i)/(2*a)) ≤ ρ := by
    intro i
    have h := reciprocal_norm_of_den_dvd p e (2*a/(a+b i)) he (hball i)
    simpa only [inv_div] using h
  have hpair : ∀ i j, i ≠ j → padicNorm p ((b i-b j)/(b i+b j)) ≤ ρ := by
    intro i j _
    rw [ball_ratio_identity a (b i) (b j) ha (hb i) (hb j)]
    exact small_padic_ball_ratio p _ _ ρ hρlt (hsmall i) (hsmall j)
  have hdetnorm := normalized_cauchy_norm_bound p b hb ρ hρpos.le hpair
  have hdetreal := normalized_cauchy_det_bounds b hb hi
  obtain ⟨z, hz⟩ := scaled_det_integral (normCauchy b) Q hclear
  have hzposQ : (0 : ℚ) < z := by
    rw [hz]
    exact mul_pos (pow_pos (by exact_mod_cast hQ) m) hdetreal.1
  have hzpos : 0 < z := by exact_mod_cast hzposQ
  have hzleQ : (z : ℚ) ≤ (Q : ℚ)^m := by
    rw [hz]
    exact mul_le_of_le_one_right (by positivity) hdetreal.2
  have hnormz : padicNorm p z ≤ ρ^(m*(m-1)) := by
    rw [hz, padicNorm.mul, IsAbsoluteValue.abv_pow (padicNorm p)]
    have hq : (padicNorm p (Q : ℚ))^m ≤ 1 :=
      pow_le_one₀ (padicNorm.nonneg _) (padicNorm.of_nat Q)
    exact (mul_le_of_le_one_left (padicNorm.nonneg _) hq).trans hdetnorm
  have hrhoexp : ρ^(m*(m-1)) = (p : ℚ)^(-((m*(m-1)*e : ℕ) : ℤ)) := by
    dsimp [ρ]
    rw [← zpow_natCast, ← zpow_mul]
    congr 1
    push_cast
    ring
  rw [hrhoexp] at hnormz
  have hdiv : ((p^(m*(m-1)*e) : ℕ) : ℤ) ∣ z :=
    padicNorm.dvd_iff_norm_le.mpr hnormz
  have hpz : ((p^(m*(m-1)*e) : ℕ) : ℤ) ≤ z := Int.le_of_dvd hzpos hdiv
  have hzle : z ≤ ((Q^m : ℕ) : ℤ) := by exact_mod_cast hzleQ
  have hpow : p^(m*(m-1)*e) ≤ Q^m := by exact_mod_cast hpz.trans hzle
  have hpowe : (p^((m-1)*e))^m ≤ Q^m := by
    convert hpow using 1
    rw [← pow_mul]
    congr 1
    ring
  exact (Nat.pow_le_pow_iff_left (ne_of_gt hm)).mp hpowe

/-- Exact, rounding-free bound for each high prime-power ball. -/
theorem high_ball_card (k m p e T Q : ℕ) (hk : 0 < k) (hp : 0 < p)
    (hQ : Q ≤ T^k) (hhigh : T < p^(4*k*e))
    (htax : p^((m-1)*e) ≤ Q) : m ≤ 4*k^2 := by
  by_contra hm
  have hm' : 4*k^2 ≤ m-1 := by omega
  have he : (4*k*e)*k ≤ (m-1)*e := by
    calc
      (4*k*e)*k = (4*k^2)*e := by ring
      _ ≤ (m-1)*e := Nat.mul_le_mul_right e hm'
  have hpow : (p^(4*k*e))^k ≤ p^((m-1)*e) := by
    rw [← pow_mul]
    exact Nat.pow_le_pow_right hp he
  have hlt : T^k < (p^(4*k*e))^k := Nat.pow_lt_pow_left hhigh (ne_of_gt hk)
  exact (not_lt_of_ge (hpow.trans (htax.trans hQ))) hlt

/-- Full denominator calculation for the transport map. -/
theorem transport_den_quasitriangle (r s : ℚ)
    (hr : 0 < r) (hr2 : r < 2) (hs : 0 < s) (hs2 : s < 2) :
    (((r*(2-s)/(r+s-r*s)).den : ℕ) : ℤ) < 2*(r.den : ℤ)*(s.den : ℤ) := by
  let N : ℤ := r.num*(2*(s.den : ℤ)-s.num)
  let L : ℤ := r.num*(s.den : ℤ)+s.num*(r.den : ℤ)-r.num*s.num
  have hv : (0 : ℚ) < r.den := by exact_mod_cast r.den_pos
  have hy : (0 : ℚ) < s.den := by exact_mod_cast s.den_pos
  have hD := transport_den_bounds r s hr hr2 hs hs2
  have hL : (L : ℚ) = (r+s-r*s)*(r.den : ℚ)*(s.den : ℚ) := by
    dsimp [L]
    push_cast
    rw [← Rat.mul_den_eq_num r, ← Rat.mul_den_eq_num s]
    ring
  have hN : (N : ℚ) = (r*(2-s))*(r.den : ℚ)*(s.den : ℚ) := by
    dsimp [N]
    push_cast
    rw [← Rat.mul_den_eq_num r, ← Rat.mul_den_eq_num s]
    ring
  have hL0Q : (0 : ℚ) < L := by
    rw [hL]
    exact mul_pos (mul_pos hD.1 hv) hy
  have hL0 : 0 < L := by exact_mod_cast hL0Q
  have hLltQ : (L : ℚ) < 2*(r.den : ℚ)*(s.den : ℚ) := by
    rw [hL]
    exact mul_lt_mul_of_pos_right (mul_lt_mul_of_pos_right hD.2 hv) hy
  have hLlt : L < 2*(r.den : ℤ)*(s.den : ℤ) := by exact_mod_cast hLltQ
  have hrepr : r*(2-s)/(r+s-r*s) = Rat.divInt N L := by
    rw [← Rat.intCast_div_eq_divInt, hN, hL]
    field_simp
  have hd : (((r*(2-s)/(r+s-r*s)).den : ℕ) : ℤ) ∣ L := by
    rw [hrepr]
    exact Rat.den_dvd N L
  exact lt_of_le_of_lt (Int.le_of_dvd hL0 hd) hLlt

/-- The normalized denominator quasi-triangle inequality for actual vertices. -/
theorem denominator_quasitriangle (a b c : ℚ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    (2*a/(a+b)).den < 2*(2*a/(a+c)).den*(2*b/(b+c)).den := by
  have hr : 0 < 2*a/(a+c) := by positivity
  have hs : 0 < 2*b/(b+c) := by positivity
  have hr2 : 2*a/(a+c) < 2 := by
    apply (div_lt_iff₀ (add_pos ha hc)).2
    nlinarith
  have hs2 : 2*b/(b+c) < 2 := by
    apply (div_lt_iff₀ (add_pos hb hc)).2
    nlinarith
  have h := transport_den_quasitriangle (2*a/(a+c)) (2*b/(b+c)) hr hr2 hs hs2
  rw [← transport_identity a b c ha hb hc] at h
  exact_mod_cast h

/-- A rounding-free prime-power pigeonhole principle. -/
theorem high_prime_factor (S : Finset ℕ) (d T : ℕ) (f : ℕ → ℕ)
    (hk : 0 < S.card) (hd : d = ∏ p ∈ S, p^(f p)) (hlarge : T < d^4) :
    ∃ p ∈ S, T < p^(4*S.card*f p) := by
  by_contra hn
  push_neg at hn
  have hpow : d^(4*S.card) ≤ T^S.card := by
    calc
      d^(4*S.card) = ∏ p ∈ S, p^(4*S.card*f p) := by
        rw [hd, ← Finset.prod_pow]
        apply Finset.prod_congr rfl
        intro p hp
        rw [← pow_mul]
        congr 1
        ring
      _ ≤ ∏ _p ∈ S, T := Finset.prod_le_prod' hn
      _ = T^S.card := by simp
  have hlt := Nat.pow_lt_pow_left hlarge (ne_of_gt hk)
  rw [← pow_mul] at hlt
  exact (not_lt_of_ge hpow) hlt

/-- Vertices assigned to a high prime-power ball. -/
def highBall {n : ℕ} (b : Fin n → ℚ) (a : ℚ) (p T k : ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun i => T < p^(4*k*((2*a/(a+b i)).den.factorization p)))

/-- Cardinality form of the fully formalized arithmetic height tax. -/
theorem highBall_card {n : ℕ} (b : Fin n → ℚ) (a : ℚ) (p T k Q : ℕ)
    [hp : Fact p.Prime] (hb : ∀ i, 0 < b i) (ha : 0 < a) (hi : Function.Injective b)
    (hT : 4 ≤ T) (hk : 0 < k) (hQ : 0 < Q) (hQT : Q ≤ T^k)
    (hclear : ∀ i j, (2*b i/(b i+b j)).den ∣ Q) :
    (highBall b a p T k).card ≤ 4*k^2 := by
  let B := highBall b a p T k
  change B.card ≤ 4*k^2
  by_cases hB : B.Nonempty
  · obtain ⟨i, hiB, hmin⟩ := Finset.exists_min_image B
      (fun i => (2*a/(a+b i)).den.factorization p) hB
    let e := (2*a/(a+b i)).den.factorization p
    have hhigh : T < p^(4*k*e) := by simpa [B, highBall, e] using hiB
    have he : 1 ≤ e := by
      by_contra he
      have he0 : e = 0 := by omega
      simp [he0] at hhigh
      omega
    let f : Fin B.card → Fin n := fun j => (B.equivFin.symm j).val
    have hf : ∀ j, f j ∈ B := fun j => (B.equivFin.symm j).property
    have hfi : Function.Injective f := by
      intro j l hjl
      exact B.equivFin.symm.injective (Subtype.ext hjl)
    have hball : ∀ j : Fin B.card, p^e ∣ (2*a/(a+b (f j))).den := by
      intro j
      exact (Nat.pow_dvd_pow p (hmin (f j) (hf j))).trans (Nat.ordProj_dvd _ _)
    have htax := denominator_ball_tax p e B.card Q a (fun j => b (f j)) ha
      (fun j => hb (f j)) (hi.comp hfi) (Finset.card_pos.mpr hB) hQ he hball
      (fun j l => hclear (f j) (f l))
    exact high_ball_card k B.card p e T Q hk hp.out.pos hQT hhigh htax
  · have h0 : B.card = 0 := Finset.card_eq_zero.mpr (Finset.not_nonempty_iff_eq_empty.mp hB)
    simp [h0]

/-- The cubic bound from explicit denominator-support data. The common
    denominator and its budget are constructed in `denominator_budget`. -/
theorem cubic_bound_of_denominator_data {n : ℕ} (b : Fin n → ℚ)
    (hb : ∀ i, 0 < b i) (hi : Function.Injective b) (S : Finset ℕ)
    (hS : ∀ p ∈ S, p.Prime) (hk : 0 < S.card) (T Q : ℕ)
    (hT : 4 ≤ T) (hQ : 0 < Q) (hQT : Q ≤ T^S.card)
    (hclear : ∀ i j, (2*b i/(b i+b j)).den ∣ Q)
    (hfactor : ∀ i j, (2*b i/(b i+b j)).den =
      ∏ p ∈ S, p^((2*b i/(b i+b j)).den.factorization p))
    (u v : Fin n) (huv : (2*b u/(b u+b v)).den = T) :
    n ≤ 8*S.card^3 := by
  let F : Fin n → Finset (Fin n) := fun c => S.biUnion (fun p => highBall b (b c) p T S.card)
  have hcap : ∀ c, (F c).card ≤ S.card*(4*S.card^2) := by
    intro c
    calc
      (F c).card ≤ ∑ p ∈ S, (highBall b (b c) p T S.card).card := Finset.card_biUnion_le
      _ ≤ ∑ _p ∈ S, 4*S.card^2 := by
        apply Finset.sum_le_sum
        intro p hp
        letI : Fact p.Prime := ⟨hS p hp⟩
        exact highBall_card b (b c) p T S.card Q hb (hb c) hi hT hk hQ hQT hclear
      _ = S.card*(4*S.card^2) := by simp
  have hcover : (Finset.univ : Finset (Fin n)) ⊆ F u ∪ F v := by
    intro i _
    have htri := denominator_quasitriangle (b u) (b v) (b i) (hb u) (hb v) (hb i)
    rw [huv] at htri
    have hfarQ := far_endpoint (T : ℝ) ((2*b u/(b u+b i)).den : ℝ)
      ((2*b v/(b v+b i)).den : ℝ) (by exact_mod_cast hT)
      (by exact_mod_cast (2*b u/(b u+b i)).den_pos)
      (by exact_mod_cast (2*b v/(b v+b i)).den_pos) (by exact_mod_cast htri)
    have hfar : T < (2*b u/(b u+b i)).den^4 ∨ T < (2*b v/(b v+b i)).den^4 := by
      exact_mod_cast hfarQ
    have hgood : ∀ c, T < (2*b c/(b c+b i)).den^4 → i ∈ F c := by
      intro c hc
      obtain ⟨p,hp,hpow⟩ := high_prime_factor S (2*b c/(b c+b i)).den T
        (fun p => (2*b c/(b c+b i)).den.factorization p) hk (hfactor c i) hc
      apply Finset.mem_biUnion.mpr
      refine ⟨p,hp,?_⟩
      simpa [highBall] using hpow
    rcases hfar with hu | hv
    · exact Finset.mem_union_left _ (hgood u hu)
    · exact Finset.mem_union_right _ (hgood v hv)
  calc
    n = (Finset.univ : Finset (Fin n)).card := by simp
    _ ≤ (F u ∪ F v).card := Finset.card_le_card hcover
    _ ≤ (F u).card+(F v).card := Finset.card_union_le _ _
    _ ≤ S.card*(4*S.card^2)+S.card*(4*S.card^2) := Nat.add_le_add (hcap u) (hcap v)
    _ = 8*S.card^3 := by ring

/-- Prime-factor reconstruction over any finite superset of the support. -/
theorem factorization_over_support (d : ℕ) (hd : 0 < d) (S : Finset ℕ)
    (hS : d.primeFactors ⊆ S) : d = ∏ p ∈ S, p^(d.factorization p) := by
  calc
    d = d.factorization.prod (fun p e => p^e) :=
      (Nat.factorization_prod_pow_eq_self (ne_of_gt hd)).symm
    _ = ∏ p ∈ S, p^(d.factorization p) :=
      Finsupp.prod_of_support_subset d.factorization
        (by simpa only [Nat.support_factorization] using hS) (fun p e => p^e) (by simp)

/-- A common denominator with budget T^k, constructed from coordinatewise maximum powers. -/
theorem denominator_budget {ι : Type*} [Fintype ι] [Nonempty ι]
    (d : ι → ℕ) (hd : ∀ i, 0 < d i) (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    (hsupp : ∀ i, (d i).primeFactors ⊆ S) (T : ℕ) (hT : ∀ i, d i ≤ T) :
    ∃ Q : ℕ, 0 < Q ∧ Q ≤ T^S.card ∧ (∀ i, d i ∣ Q) := by
  let E : ℕ → ℕ := fun p => Finset.univ.sup (fun i => (d i).factorization p)
  let Q : ℕ := ∏ p ∈ S, p^(E p)
  have hQ : 0 < Q := Finset.prod_pos (fun p hp => pow_pos (hS p hp).pos _)
  have hpow : ∀ p ∈ S, p^(E p) ≤ T := by
    intro p _
    obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_sup Finset.univ Finset.univ_nonempty
      (fun i => (d i).factorization p)
    have hiE : E p = (d i).factorization p := hi
    rw [hiE]
    exact (Nat.le_of_dvd (hd i) (Nat.ordProj_dvd _ _)).trans (hT i)
  have hQT : Q ≤ T^S.card := by
    calc
      Q ≤ ∏ _p ∈ S, T := Finset.prod_le_prod' hpow
      _ = T^S.card := by simp
  refine ⟨Q,hQ,hQT,?_⟩
  intro i
  rw [factorization_over_support (d i) (hd i) S (hsupp i)]
  apply Finset.prod_dvd_prod_of_dvd
  intro p hp
  apply Nat.pow_dvd_pow
  change (d i).factorization p ≤ Finset.univ.sup (fun j => (d j).factorization p)
  exact Finset.le_sup (f := fun j : ι => (d j).factorization p) (Finset.mem_univ i)

/-- A small-denominator cross-row has at most fifteen distinct positive vertices.
The exact Farey count is seven; fifteen keeps this auxiliary formal bound elementary. -/
theorem small_denominator_card {n : ℕ} (b : Fin n → ℚ) (c : ℚ)
    (hb : ∀ i, 0 < b i) (hc : 0 < c) (hi : Function.Injective b)
    (hd : ∀ i, (2*b i/(b i+c)).den ≤ 3) : n ≤ 15 := by
  let q : Fin n → ℚ := fun i => 2*b i/(b i+c)
  have hqpos : ∀ i, 0 < q i := by
    intro i
    exact div_pos (mul_pos (by norm_num) (hb i)) (add_pos (hb i) hc)
  have hqlt : ∀ i, q i < 2 := by
    intro i
    dsimp [q]
    apply (div_lt_iff₀ (add_pos (hb i) hc)).2
    nlinarith [hb i]
  have hnum : ∀ i, 1 ≤ (q i).num ∧ (q i).num ≤ 5 := by
    intro i
    have hp : 0 < (q i).num := Rat.num_pos.mpr (hqpos i)
    have ht : ((q i).num : ℚ) < 2*((q i).den : ℚ) := by
      have h := mul_lt_mul_of_pos_right (hqlt i)
        (by exact_mod_cast (q i).den_pos : (0 : ℚ) < (q i).den)
      simpa only [Rat.mul_den_eq_num] using h
    have hden : ((q i).den : ℚ) ≤ 3 := by exact_mod_cast hd i
    have huQ : ((q i).num : ℚ) < 6 := by linarith
    have hu : (q i).num < 6 := by exact_mod_cast huQ
    omega
  let V : Finset (ℤ × ℕ) := (Finset.Icc (1 : ℤ) 5).product (Finset.Icc (1 : ℕ) 3)
  have hmaps : Set.MapsTo (fun i => ((q i).num,(q i).den))
      (↑(Finset.univ : Finset (Fin n))) (↑V) := by
    intro i _
    change ((q i).num,(q i).den) ∈ V
    apply Finset.mem_product.mpr
    refine ⟨Finset.mem_Icc.mpr (hnum i), Finset.mem_Icc.mpr ?_⟩
    have hpos := (q i).den_pos
    have hle := hd i
    change (q i).den ≤ 3 at hle
    omega
  have hinj : Set.InjOn (fun i => ((q i).num,(q i).den))
      (↑(Finset.univ : Finset (Fin n))) := by
    intro i _ j _ hij
    have hnumij := congrArg Prod.fst hij
    have hdenij := congrArg Prod.snd hij
    change (q i).num = (q j).num at hnumij
    change (q i).den = (q j).den at hdenij
    have hqij : q i = q j := by
      rw [← Rat.num_div_den (q i), ← Rat.num_div_den (q j), hnumij, hdenij]
    dsimp [q] at hqij
    have hbi : b i+c ≠ 0 := ne_of_gt (add_pos (hb i) hc)
    have hbj : b j+c ≠ 0 := ne_of_gt (add_pos (hb j) hc)
    have heq := (div_eq_div_iff hbi hbj).mp hqij
    apply hi
    apply mul_left_cancel₀ (ne_of_gt hc)
    nlinarith [heq]
  have hcard := Finset.card_le_card_of_injOn _ hmaps hinj
  norm_num [V] at hcard
  exact hcard

/-- The full cardinality theorem for normalized denominator support.
It is stronger than the positive-integer sum-support application. -/
theorem cardinality_of_denominator_support {n : ℕ} (b : Fin n → ℚ)
    (hb : ∀ i, 0 < b i) (hi : Function.Injective b) (S : Finset ℕ)
    (hS : ∀ p ∈ S, p.Prime)
    (hsupp : ∀ i j, (2*b i/(b i+b j)).den.primeFactors ⊆ S) :
    n ≤ 15+8*S.card^3 := by
  by_cases hn : n = 0
  · simp [hn]
  have hnpos : 0 < n := Nat.pos_of_ne_zero hn
  let c : Fin n := ⟨0,hnpos⟩
  letI : Nonempty (Fin n) := ⟨c⟩
  let d : Fin n × Fin n → ℕ := fun ij => (2*b ij.1/(b ij.1+b ij.2)).den
  let T : ℕ := Finset.univ.sup d
  have hd : ∀ ij, 0 < d ij := fun ij => (2*b ij.1/(b ij.1+b ij.2)).den_pos
  have hdT : ∀ ij, d ij ≤ T := fun ij => Finset.le_sup (Finset.mem_univ ij)
  by_cases hT : 4 ≤ T
  · obtain ⟨Q,hQ,hQT,hclear⟩ := denominator_budget d hd S hS (fun ij => hsupp ij.1 ij.2) T hdT
    obtain ⟨ij,_,hij⟩ := Finset.exists_mem_eq_sup Finset.univ Finset.univ_nonempty d
    have hmax : (2*b ij.1/(b ij.1+b ij.2)).den = T := hij.symm
    have hfactor : ∀ i j, (2*b i/(b i+b j)).den =
        ∏ p ∈ S, p^((2*b i/(b i+b j)).den.factorization p) := by
      intro i j
      exact factorization_over_support _ (hd (i,j)) S (hsupp i j)
    have hk : 0 < S.card := by
      by_contra hk
      have hS0 : S = ∅ := Finset.card_eq_zero.mp (by omega)
      have hm := hfactor ij.1 ij.2
      simp only [hS0, Finset.prod_empty] at hm
      rw [hmax] at hm
      omega
    have hbound := cubic_bound_of_denominator_data b hb hi S hS hk T Q hT hQ hQT
      (fun i j => hclear (i,j)) hfactor ij.1 ij.2 hmax
    omega
  · have hsmall : n ≤ 15 := small_denominator_card b (b c) hb (hb c) hi (by
      intro i
      have h := hdT (i,c)
      change (2*b i/(b i+b c)).den ≤ T at h
      omega)
    omega

/-- The requested positive-integer sum-support hypothesis implies the denominator hypothesis. -/
theorem positive_integer_clique_bound {n : ℕ} (a : Fin n → ℕ)
    (ha : ∀ i, 0 < a i) (hi : Function.Injective a) (S : Finset ℕ)
    (hS : ∀ p ∈ S, p.Prime)
    (hsum : ∀ i j, i ≠ j → (a i+a j).primeFactors ⊆ S) :
    n ≤ 15+8*S.card^3 := by
  let b : Fin n → ℚ := fun i => a i
  have hb : ∀ i, 0 < b i := by intro i; dsimp [b]; exact_mod_cast ha i
  have hbi : Function.Injective b := by
    intro i j hij
    apply hi
    dsimp [b] at hij
    exact_mod_cast hij
  apply cardinality_of_denominator_support b hb hbi S hS
  intro i j
  by_cases hij : i = j
  · subst j
    have heq : 2*b i/(b i+b i) = 1 := by
      field_simp [ne_of_gt (hb i)]; ring
    simp [heq]
  · have hdenI : (((2*b i/(b i+b j)).den : ℕ) : ℤ) ∣ (a i+a j : ℕ) := by
      have h := Rat.den_dvd (2*(a i : ℤ)) ((a i+a j : ℕ) : ℤ)
      simpa [Rat.divInt_eq_div, b] using h
    have hden : (2*b i/(b i+b j)).den ∣ a i+a j := by exact_mod_cast hdenI
    intro p hp
    obtain ⟨hpp,hpd,_⟩ := Nat.mem_primeFactors.mp hp
    apply hsum i j hij
    exact Nat.mem_primeFactors.mpr ⟨hpp,hpd.trans hden,ne_of_gt (Nat.add_pos_left (ha i) _)⟩

/-- Finset formulation for positive integer cliques. -/
theorem positive_finset_clique_bound (A S : Finset ℕ)
    (hA : ∀ a ∈ A, 0 < a) (hS : ∀ p ∈ S, p.Prime)
    (hsum : ∀ a ∈ A, ∀ b ∈ A, a ≠ b → (a+b).primeFactors ⊆ S) :
    A.card ≤ 15+8*S.card^3 := by
  let f : Fin A.card → ℕ := fun i => (A.equivFin.symm i).val
  have hf : ∀ i, f i ∈ A := fun i => (A.equivFin.symm i).property
  have hfi : Function.Injective f := by
    intro i j hij
    exact A.equivFin.symm.injective (Subtype.ext hij)
  exact positive_integer_clique_bound f (fun i => hA (f i) (hf i)) hfi S hS
    (fun i j hij => hsum (f i) (hf i) (f j) (hf j) (hfi.ne hij))

/-- A possible zero costs at most one point; no diagonal sum is assumed smooth. -/
theorem natural_finset_clique_bound (A S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    (hsum : ∀ a ∈ A, ∀ b ∈ A, a ≠ b → (a+b).primeFactors ⊆ S) :
    A.card ≤ 16+8*S.card^3 := by
  have hpos : ∀ a ∈ A.erase 0, 0 < a := by
    intro a ha
    exact Nat.pos_of_ne_zero (Finset.mem_erase.mp ha).1
  have hsub : A.erase 0 ⊆ A := Finset.erase_subset 0 A
  have h := positive_finset_clique_bound (A.erase 0) S hpos hS
    (fun a ha b hb hab => hsum a (hsub ha) b (hsub hb) hab)
  by_cases hz : 0 ∈ A
  · have hc := Finset.card_erase_add_one hz
    omega
  · rw [Finset.erase_eq_of_notMem hz] at h
    omega

/-- The exact restricted-sum product used by the problem specification. -/
def restrictedSumProduct (A : Finset ℕ) : ℕ :=
  ∏ x ∈ A.offDiag, (x.1+x.2)

/-- A cubic constraint for the actual prime support of the restricted-sum product. -/
theorem restricted_product_cubic_bound (A : Finset ℕ) :
    A.card ≤ 16+8*(restrictedSumProduct A).primeFactors.card^3 := by
  have hprod : 0 < restrictedSumProduct A := by
    apply Finset.prod_pos
    intro x hx
    have hne := (Finset.mem_offDiag.mp hx).2.2
    omega
  apply natural_finset_clique_bound A (restrictedSumProduct A).primeFactors
  · intro p hp
    exact (Nat.mem_primeFactors.mp hp).1
  · intro a ha b hb hab p hp
    obtain ⟨hpp,hpd,_⟩ := Nat.mem_primeFactors.mp hp
    have hpair : (a,b) ∈ A.offDiag := Finset.mem_offDiag.mpr ⟨ha,hb,hab⟩
    have hsumprod : a+b ∣ restrictedSumProduct A :=
      Finset.dvd_prod_of_mem (fun x : ℕ × ℕ => x.1+x.2) hpair
    exact Nat.mem_primeFactors.mpr ⟨hpp,hpd.trans hsumprod,ne_of_gt hprod⟩

/-- Greatest uniform lower bounds inherit the cubic constraint, without assuming
that a minimizing configuration has already been chosen. -/
theorem maximal_lower_bound_cubic (f : ℕ → ℕ)
    (hf : ∀ n, IsGreatest
      {m | ∀ A : Finset ℕ, A.card = n → m ≤ (restrictedSumProduct A).primeFactors.card}
      (f n)) : ∀ n, n ≤ 16+8*(f n)^3 := by
  intro n
  by_contra hn
  have hs : f n+1 ∈
      {m | ∀ A : Finset ℕ, A.card = n → m ≤ (restrictedSumProduct A).primeFactors.card} := by
    intro A hA
    have hb := restricted_product_cubic_bound A
    rw [hA] at hb
    by_contra hh
    have hk : (restrictedSumProduct A).primeFactors.card ≤ f n := by omega
    have hpow := Nat.pow_le_pow_left hk 3
    omega
  have hbad := (hf n).2 hs
  omega

/-- The polynomial constraint gives the required superlogarithmic divergence. -/
theorem ratio_tendsto_atTop_of_cubic_bound (f : ℕ → ℕ)
    (hf : ∀ n, n ≤ 16+8*(f n)^3) :
    Filter.Tendsto (fun n => (f n : ℝ)/Real.log (n : ℝ)) Filter.atTop Filter.atTop := by
  apply Filter.tendsto_atTop.2
  intro R
  let C : ℝ := max R 1
  have hnat : Filter.Tendsto (fun n : ℕ => (n : ℝ)) Filter.atTop Filter.atTop :=
    tendsto_natCast_atTop_atTop
  have hlog : Filter.Tendsto (fun n : ℕ => Real.log (n : ℝ)^3/(n : ℝ))
      Filter.atTop (nhds 0) := by
    simpa only [Function.comp_def, one_mul, add_zero] using
      (Real.tendsto_pow_log_div_mul_add_atTop 1 0 3 one_ne_zero).comp hnat
  have hconst : Filter.Tendsto (fun n : ℕ => (16 : ℝ)/(n : ℝ)) Filter.atTop (nhds 0) :=
    Filter.Tendsto.div_atTop tendsto_const_nhds hnat
  have hlim : Filter.Tendsto
      (fun n : ℕ => 16/(n : ℝ)+8*C^3*(Real.log (n : ℝ)^3/(n : ℝ)))
      Filter.atTop (nhds 0) := by
    simpa using hconst.add (hlog.const_mul (8*C^3))
  have he := hlim.eventually_lt_const (by norm_num : (0 : ℝ) < 1)
  filter_upwards [he, Filter.eventually_ge_atTop (2 : ℕ)] with n hn hn2
  have hnreal : (1 : ℝ) < n := by exact_mod_cast (by omega : 1 < n)
  have hnpos : (0 : ℝ) < n := lt_trans (by norm_num) hnreal
  have hlogpos : 0 < Real.log (n : ℝ) := Real.log_pos hnreal
  have hsmall : 16+8*(C*Real.log (n : ℝ))^3 < (n : ℝ) := by
    apply (div_lt_one hnpos).1
    convert hn using 1; ring
  have hpoly : (n : ℝ) ≤ 16+8*(f n : ℝ)^3 := by exact_mod_cast hf n
  by_contra hh
  have hlt : (f n : ℝ)/Real.log (n : ℝ) < C :=
    lt_of_lt_of_le (lt_of_not_ge hh) (le_max_left R 1)
  have hm : (f n : ℝ) < C*Real.log (n : ℝ) := (div_lt_iff₀ hlogpos).1 hlt
  have hpow := pow_le_pow_left₀ (Nat.cast_nonneg (f n)) hm.le 3
  nlinarith

/-- The polynomial cardinality bound implies the maximal-lower-bound
    divergence formulation. -/
theorem erdos126_from_maximal_lower_bound (f : ℕ → ℕ)
    (hf : ∀ n, IsGreatest
      {m | ∀ A : Finset ℕ, A.card = n → m ≤ (restrictedSumProduct A).primeFactors.card}
      (f n)) :
    Filter.Tendsto (fun n => (f n : ℝ)/Real.log (n : ℝ)) Filter.atTop Filter.atTop :=
  ratio_tendsto_atTop_of_cubic_bound f (maximal_lower_bound_cubic f hf)

end Erdos126Adelic

namespace Erdos126

def IsMaximalAddFactorsCard (f : ℕ → ℕ) : Prop := ∀ n,
    IsGreatest
      { m | ∀ (A : Finset ℕ), A.card = n →
        m ≤ (∏ ⟨a, b⟩ ∈ A.offDiag, (a + b)).primeFactors.card}
      (f n)

/--
Let $f(n)$ be maximal such that if $A\subseteq\mathbb{N}$ has $|A| = n$ then
$\prod_{a\neq b\in A}(a + b)$ has at least $f(n)$ distinct prime factors.
Is it true that $\frac{f(n)}{\log n} \to\infty$?
-/
theorem erdos_126 : ∀ (f : ℕ → ℕ), IsMaximalAddFactorsCard f →
    Tendsto (fun n => f n / Real.log n) atTop atTop := by
  intro f hf
  apply Erdos126Adelic.erdos126_from_maximal_lower_bound f
  simpa only [IsMaximalAddFactorsCard, Erdos126Adelic.restrictedSumProduct] using hf

end Erdos126

namespace Jig59Canonical

open Filter
open scoped Topology

/-- `f n` is the largest universal lower bound for the number of distinct
prime factors in the product of all ordered pairwise sums from an `n`-set. -/
def IsMaximalAddFactorsCard (f : ℕ → ℕ) : Prop :=
  ∀ n,
    IsGreatest
      {m | ∀ (A : Finset ℕ), A.card = n →
        m ≤ (∏ p ∈ A.offDiag, (p.1 + p.2)).primeFactors.card}
      (f n)

/-- Erdős problem 126: the universal number of distinct prime factors grows
faster than every constant multiple of `log n`. -/
abbrev statement : Prop :=
  ∀ (f : ℕ → ℕ), IsMaximalAddFactorsCard f →
    Tendsto (fun n : ℕ => (f n : ℝ) / Real.log n) atTop atTop

/-- Exact equality of Jig59's root predicate with the published source predicate. -/
theorem predicate_eq (f : ℕ → ℕ) :
    IsMaximalAddFactorsCard f = Erdos126.IsMaximalAddFactorsCard f := rfl

/-- Port of the previously published Epoch AI/GPT-6 Astra solution. -/
theorem solution : statement := by
  intro f hf
  exact Erdos126.erdos_126 f hf


end Jig59Canonical

namespace Submissions.Erdos126AdditivePrimeFactors.EpochPort

theorem proof : Jig59Canonical.statement := Jig59Canonical.solution

end Submissions.Erdos126AdditivePrimeFactors.EpochPort
