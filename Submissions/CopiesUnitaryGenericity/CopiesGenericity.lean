/-
Submission for `Statements.CopiesUnitaryGenericity`.

For every `k ≥ 2` and every family of nonzero vectors `v : Fin n → Fin k → ℂ` that is
tight and `(k+1)`-spanning, some unitary `U` makes the two-block family `(v, U·v)`
cross-nonorthogonal and transversal.

Proof strategy (real-polynomial genericity on the unitary group):
* LAYER W (witnesses): for each single condition (a cross pairing `(i,j)`, or a
  subset pair `(S,T)` demanding `rk = min k (rk S + rk T)`), construct one unitary
  achieving it, via orthonormal-basis surgery on `EuclideanSpace ℂ (Fin k)`.
* LAYER P (parameterization): the Cayley transform `x ↦ (1 - S x) * (1 + S x)⁻¹`
  parameterizes (almost all of) the unitary group by real parameters
  `x : Fin k × Fin k → ℝ`, with `S x` skew-Hermitian. Each condition, composed with
  the Cayley map and cleared of denominators, is (the nonvanishing of) a polynomial
  in `MvPolynomial (Fin k × Fin k) ℂ`. Each witness (adjusted by a unimodular phase
  so that `1 + W` is invertible) yields a real point where the condition polynomial
  does not vanish, so each polynomial is nonzero; their product is nonzero, and a
  nonzero polynomial over `ℂ` does not vanish at some *real* point (one-variable
  induction + finiteness of roots).  Evaluating the Cayley map there gives one
  unitary satisfying all conditions simultaneously.
* LAYER T (minors): the rank conditions are caught polynomially by `det (P * C U)`
  where `C U` is a `k × r` matrix of chosen columns of the combined family and `P`
  a fixed `r × k` matrix (the conjugate-transpose of the witness columns), using
  positive-definiteness of the Hermitian Gram matrix.
-/
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Group.Fin.Basic
import Mathlib.Algebra.Group.Units.Equiv
import Mathlib.Data.Fin.SuccPred
import Mathlib.Algebra.Star.BigOperators
import Mathlib.Data.Complex.Basic

namespace Submissions.CopiesUnitaryGenericity.CopiesGenericity

open Matrix

variable {k : ℕ}

/-- Hermitian pairing, conjugate-linear in the first slot. -/
abbrev pair (x y : Fin k → ℂ) : ℂ := ∑ r, star (x r) * y r

noncomputable abbrev rk {ι : Type} (v : ι → Fin k → ℂ) (S : Finset ι) : ℕ :=
  Module.finrank ℂ (Submodule.span ℂ (Set.range fun i : (S : Set ι) => v i))

abbrev Tight {ι : Type} [Fintype ι] (v : ι → Fin k → ℂ) : Prop :=
  ∀ S : Finset ι, S.card ≤ k - 1 → LinearIndependent ℂ fun i : (S : Set ι) => v i

abbrev Spanning {ι : Type} [Fintype ι] (v : ι → Fin k → ℂ) : Prop :=
  ∀ S : Finset ι, S.card = k + 1 →
    Submodule.span ℂ (Set.range fun i : (S : Set ι) => v i) = ⊤

abbrev Transversal {n₁ n₂ : ℕ} (u : Fin n₁ → Fin k → ℂ) (w : Fin n₂ → Fin k → ℂ) :
    Prop :=
  ∀ (S : Finset (Fin n₁)) (T : Finset (Fin n₂)),
    rk (Sum.elim u w) (S.disjSum T) = min k (rk u S + rk w T)

/-- A matrix is unitary when `U * star U = 1`. -/
abbrev IsUnitary (U : Matrix (Fin k) (Fin k) ℂ) : Prop :=
  U * star U = 1

/-- Apply a `k × k` matrix to a coordinate vector. -/
abbrev applyMat (U : Matrix (Fin k) (Fin k) ℂ) (x : Fin k → ℂ) : Fin k → ℂ :=
  U.mulVec x

noncomputable section

/-! ### Section A: generalities on the pairing -/

lemma pair_comm_star {m : ℕ} (x y : Fin m → ℂ) : star (pair x y) = pair y x := by
  rw [star_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [star_mul', star_star]
  ring

lemma pair_smul_right {m : ℕ} (c : ℂ) (x y : Fin m → ℂ) :
    pair x (c • y) = c * pair x y := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

lemma pair_add_right {m : ℕ} (x y z : Fin m → ℂ) :
    pair x (y + z) = pair x y + pair x z := by
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun r _ => ?_
  simp [mul_add]

lemma pair_neg_right {m : ℕ} (x y : Fin m → ℂ) : pair x (-y) = -pair x y := by
  rw [eq_neg_iff_add_eq_zero, ← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero fun r _ => ?_
  simp

lemma pair_zero_right {m : ℕ} (x : Fin m → ℂ) : pair x 0 = 0 := by
  refine Finset.sum_eq_zero fun r _ => ?_
  simp

lemma pair_self_real {m : ℕ} (x : Fin m → ℂ) :
    pair x x = ((∑ r, Complex.normSq (x r) : ℝ) : ℂ) := by
  push_cast
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [Complex.star_def, mul_comm, Complex.mul_conj]

lemma pair_self_eq_zero {m : ℕ} {x : Fin m → ℂ} (h : pair x x = 0) : x = 0 := by
  rw [pair_self_real] at h
  have h0 : (∑ r, Complex.normSq (x r) : ℝ) = 0 := by exact_mod_cast h
  have hz := (Finset.sum_eq_zero_iff_of_nonneg
    (fun (r : Fin m) _ => Complex.normSq_nonneg (x r))).mp h0
  funext r
  exact Complex.normSq_eq_zero.mp (hz r (Finset.mem_univ r))

lemma pair_self_ne_zero {m : ℕ} {x : Fin m → ℂ} (hx : x ≠ 0) : pair x x ≠ 0 :=
  fun h => hx (pair_self_eq_zero h)

/-- The rectangular adjoint identity for the pairing. -/
lemma pair_mulVec_left {m r : ℕ} (M : Matrix (Fin m) (Fin r) ℂ) (a : Fin r → ℂ)
    (b : Fin m → ℂ) : pair (M.mulVec a) b = pair a (Mᴴ.mulVec b) := by
  calc pair (M.mulVec a) b
      = ∑ i, ∑ t, star (M i t) * star (a t) * b i := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Matrix.mulVec_apply_eq_sum, star_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun t _ => ?_
        rw [star_mul']
    _ = ∑ t, ∑ i, star (M i t) * star (a t) * b i := Finset.sum_comm
    _ = pair a (Mᴴ.mulVec b) := by
        refine Finset.sum_congr rfl fun t _ => ?_
        rw [Matrix.mulVec_apply_eq_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Matrix.conjTranspose_apply]
        ring

/-! ### Section B: the unit circle and phase adjustment -/

/-- The set of unimodular complex numbers is infinite. -/
lemma unimodular_infinite : {z : ℂ | star z * z = 1}.Infinite := by
  have key : ∀ x : ℝ, ((x : ℂ) + Complex.I) ≠ 0 := by
    intro x h
    have hi := congrArg Complex.im h
    simp at hi
  have hconj : ∀ x : ℝ, (starRingEnd ℂ) ((x : ℂ) + Complex.I) = (x : ℂ) - Complex.I := by
    intro x
    rw [map_add, Complex.conj_ofReal, Complex.conj_I, sub_eq_add_neg]
  have hconj0 : ∀ x : ℝ, (starRingEnd ℂ) ((x : ℂ) + Complex.I) ≠ 0 := by
    intro x h
    rw [hconj] at h
    have hi := congrArg Complex.im h
    simp at hi
  refine Set.infinite_of_injective_forall_mem
    (f := fun x : ℝ => (starRingEnd ℂ) ((x : ℂ) + Complex.I) / ((x : ℂ) + Complex.I)) ?_ ?_
  · intro x y h
    simp only at h
    rw [div_eq_div_iff (key x) (key y), hconj, hconj] at h
    have hxy : ((x : ℂ) - y) = 0 := by
      have h2 : (2 : ℂ) * Complex.I * ((x : ℂ) - y) = 0 := by linear_combination h
      have h3 : ((2 : ℂ) * Complex.I) ≠ 0 := by
        simp [Complex.I_ne_zero]
      exact (mul_eq_zero.mp h2).resolve_left h3
    exact_mod_cast sub_eq_zero.mp hxy
  · intro x
    show (starRingEnd ℂ) _ / _ ∈ {z : ℂ | star z * z = 1}
    simp only [Set.mem_ofPred_eq, Complex.star_def]
    rw [map_div₀, Complex.conj_conj, div_mul_div_comm,
      mul_comm ((starRingEnd ℂ) ((x : ℂ) + Complex.I)) ((x : ℂ) + Complex.I)]
    exact div_self (mul_ne_zero (key x) (hconj0 x))

lemma unimodular_ne_zero {c : ℂ} (hc : star c * c = 1) : c ≠ 0 := by
  intro h
  rw [h, mul_zero] at hc
  exact zero_ne_one hc

/-- Any matrix admits a unimodular phase `c` such that `1 + c • M` is nonsingular. -/
lemma exists_phase_det {m : ℕ} (M : Matrix (Fin m) (Fin m) ℂ) :
    ∃ c : ℂ, star c * c = 1 ∧ ((1 : Matrix (Fin m) (Fin m) ℂ) + c • M).det ≠ 0 := by
  classical
  set Mat : Matrix (Fin m) (Fin m) (Polynomial ℂ) :=
    (1 : Matrix (Fin m) (Fin m) (Polynomial ℂ)) +
      (Polynomial.X : Polynomial ℂ) • M.map Polynomial.C with hMat
  set Q : Polynomial ℂ := Mat.det with hQ
  have hev : ∀ z : ℂ, Q.eval z = ((1 : Matrix (Fin m) (Fin m) ℂ) + z • M).det := by
    intro z
    have h1 : (Polynomial.evalRingHom z) Q
        = (((Polynomial.evalRingHom z)).mapMatrix Mat).det := RingHom.map_det _ _
    have h2 : ((Polynomial.evalRingHom z)).mapMatrix Mat
        = (1 : Matrix (Fin m) (Fin m) ℂ) + z • M := by
      rw [hMat, map_add, map_one]
      congr 1
      ext i j
      simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul,
        Polynomial.coe_evalRingHom, Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_C]
    simpa [h2] using h1
  have hQ0 : Q ≠ 0 := by
    intro h
    have h0 := hev 0
    rw [h] at h0
    simp at h0
  obtain ⟨c, hc⟩ :=
    (unimodular_infinite.sdiff (Polynomial.finite_setOfPred_isRoot hQ0)).nonempty
  refine ⟨c, hc.1, ?_⟩
  rw [← hev]
  exact fun h => hc.2 h

/-! ### Section C: a nonzero polynomial does not vanish at some real point -/

lemma exists_real_eval_ne_zero : ∀ {m : ℕ} (p : MvPolynomial (Fin m) ℂ), p ≠ 0 →
    ∃ x : Fin m → ℝ, MvPolynomial.eval (fun i => (x i : ℂ)) p ≠ 0 := by
  intro m
  induction m with
  | zero =>
    intro p hp
    obtain ⟨c, rfl⟩ := MvPolynomial.C_surjective (Fin 0) p
    refine ⟨fun i => i.elim0, ?_⟩
    rw [MvPolynomial.eval_C]
    intro h
    exact hp (by rw [h, map_zero])
  | succ m ih =>
    intro p hp
    set q := MvPolynomial.finSuccEquiv ℂ m p with hqdef
    have hq0 : q ≠ 0 := by
      intro h
      apply hp
      have h2 := congrArg (MvPolynomial.finSuccEquiv ℂ m).symm h
      rwa [hqdef, AlgEquiv.symm_apply_apply, map_zero] at h2
    obtain ⟨d, hd⟩ : ∃ d, q.coeff d ≠ 0 := by
      by_contra h
      exact hq0 (Polynomial.ext fun d => by
        rw [Polynomial.coeff_zero]
        by_contra hne
        exact h ⟨d, hne⟩)
    obtain ⟨x, hx⟩ := ih _ hd
    set Q : Polynomial ℂ := q.map (MvPolynomial.eval (fun i => (x i : ℂ))) with hQdef
    have hQ0 : Q ≠ 0 := by
      intro h
      apply hx
      have hc : Q.coeff d = 0 := by rw [h]; simp
      rwa [hQdef, Polynomial.coeff_map] at hc
    have hinf : (Set.range ((↑) : ℝ → ℂ)).Infinite :=
      Set.infinite_range_of_injective Complex.ofReal_injective
    obtain ⟨z, hz⟩ := (hinf.sdiff (Polynomial.finite_setOfPred_isRoot hQ0)).nonempty
    obtain ⟨t, rfl⟩ := hz.1
    refine ⟨Fin.cons t x, ?_⟩
    have hcons : (fun i => ((Fin.cons t x : Fin (m+1) → ℝ) i : ℂ))
        = Fin.cons (t : ℂ) (fun i => (x i : ℂ)) := by
      funext i
      refine Fin.cases ?_ ?_ i <;> simp
    rw [hcons, MvPolynomial.eval_eq_eval_mv_eval']
    exact fun h => hz.2 h

/-- The version over the index type `Fin k × Fin k` used by the Cayley parameters. -/
lemma exists_real_eval_ne_zero' {m : ℕ} (p : MvPolynomial (Fin m × Fin m) ℂ)
    (hp : p ≠ 0) :
    ∃ x : Fin m × Fin m → ℝ, MvPolynomial.eval (fun s => (x s : ℂ)) p ≠ 0 := by
  have hren : MvPolynomial.rename (⇑(finProdFinEquiv : Fin m × Fin m ≃ Fin (m * m))) p ≠ 0 := by
    intro h
    apply hp
    apply MvPolynomial.rename_injective _ finProdFinEquiv.injective
    simpa using h
  obtain ⟨x, hx⟩ := exists_real_eval_ne_zero _ hren
  refine ⟨fun s => x (finProdFinEquiv s), ?_⟩
  have : (fun s : Fin m × Fin m => ((x (finProdFinEquiv s) : ℝ) : ℂ))
      = (fun i => (x i : ℂ)) ∘ ⇑finProdFinEquiv := rfl
  rw [this, ← MvPolynomial.eval_rename]
  exact hx

/-! ### Section D: the Cayley transform -/

/-- The skew-Hermitian matrix built from real parameters. -/
def sMat {m : ℕ} (x : Fin m × Fin m → ℝ) : Matrix (Fin m) (Fin m) ℂ :=
  Matrix.of fun p q =>
    if p = q then Complex.I * (x (p, p) : ℂ)
    else if p < q then (x (p, q) : ℂ) + Complex.I * (x (q, p) : ℂ)
    else -(x (q, p) : ℂ) + Complex.I * (x (p, q) : ℂ)

lemma sMat_skew {m : ℕ} (x : Fin m × Fin m → ℝ) : (sMat x)ᴴ = -(sMat x) := by
  ext p q
  rw [Matrix.conjTranspose_apply, Matrix.neg_apply]
  simp only [sMat, Matrix.of_apply]
  rcases lt_trichotomy p q with h | h | h
  · rw [if_neg h.ne', if_neg (asymm h), if_neg h.ne, if_pos h]
    simp only [Complex.star_def, map_add, map_neg, map_mul, Complex.conj_I,
      Complex.conj_ofReal]
    ring
  · subst h
    rw [if_pos rfl]
    simp only [Complex.star_def, map_mul, Complex.conj_I, Complex.conj_ofReal]
    ring
  · rw [if_neg h.ne, if_pos h, if_neg h.ne', if_neg (asymm h)]
    simp only [Complex.star_def, map_add, map_mul, Complex.conj_I, Complex.conj_ofReal]
    ring

/-- `1 + S` is nonsingular for skew-Hermitian `S`. -/
lemma det_one_add_skew_ne_zero {m : ℕ} {S : Matrix (Fin m) (Fin m) ℂ}
    (hS : Sᴴ = -S) : ((1 : Matrix (Fin m) (Fin m) ℂ) + S).det ≠ 0 := by
  classical
  intro hdet
  obtain ⟨w, hw0, hw⟩ := (Matrix.exists_mulVec_eq_zero_iff).mpr hdet
  have h1 : w + S.mulVec w = 0 := by
    calc w + S.mulVec w = (1 + S).mulVec w := by rw [Matrix.add_mulVec, Matrix.one_mulVec]
      _ = 0 := hw
  have h2 : pair w w + pair w (S.mulVec w) = 0 := by
    have h3 := congrArg (fun z => pair w z) h1
    simpa [pair_add_right, pair_zero_right] using h3
  set z := pair w (S.mulVec w) with hzdef
  have h3 : star z = -z := by
    rw [hzdef, pair_comm_star, pair_mulVec_left S w w, hS, Matrix.neg_mulVec, pair_neg_right]
  have hz2 : z = -pair w w := eq_neg_of_add_eq_zero_right h2
  have h4 : star z = z := by
    rw [hz2, pair_self_real, star_neg]
    simp [Complex.conj_ofReal]
  rw [h4] at h3
  have hz0 : z = 0 := by
    have h6 : (2 : ℂ) * z = 0 := by linear_combination h3
    exact (mul_eq_zero.mp h6).resolve_left two_ne_zero
  have hww : pair w w = 0 := by
    rw [hz0] at h2
    simpa using h2
  exact hw0 (pair_self_eq_zero hww)

/-- The Cayley transform of the real parameter point `x`. -/
def cayley {m : ℕ} (x : Fin m × Fin m → ℝ) : Matrix (Fin m) (Fin m) ℂ :=
  (1 - sMat x) * (1 + sMat x)⁻¹

lemma cayley_unitary_aux {m : ℕ} {S : Matrix (Fin m) (Fin m) ℂ} (hS : Sᴴ = -S) :
    ((1 - S) * (1 + S)⁻¹) * ((1 - S) * (1 + S)⁻¹)ᴴ = 1 := by
  classical
  set A := (1 : Matrix (Fin m) (Fin m) ℂ) + S with hA
  set B := (1 : Matrix (Fin m) (Fin m) ℂ) - S with hB
  have hdetA : A.det ≠ 0 := det_one_add_skew_ne_zero hS
  have hAH : Aᴴ = B := by
    rw [hA, hB, Matrix.conjTranspose_add, Matrix.conjTranspose_one, hS, sub_eq_add_neg]
  have hBH : Bᴴ = A := by
    rw [hB, hA, Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hS, sub_neg_eq_add]
  have hdetB : B.det ≠ 0 := by
    rw [← hAH, Matrix.det_conjTranspose, star_ne_zero]
    exact hdetA
  have hUA : IsUnit A.det := isUnit_iff_ne_zero.mpr hdetA
  have hUB : IsUnit B.det := isUnit_iff_ne_zero.mpr hdetB
  have hcomm : A * B = B * A := by
    rw [hA, hB]
    noncomm_ring
  have hinvH : (A⁻¹)ᴴ = B⁻¹ := by rw [Matrix.conjTranspose_nonsing_inv, hAH]
  have hswap : A⁻¹ * B⁻¹ = B⁻¹ * A⁻¹ := by
    rw [← Matrix.mul_inv_rev, ← Matrix.mul_inv_rev, hcomm]
  calc (B * A⁻¹) * (B * A⁻¹)ᴴ
      = B * A⁻¹ * ((A⁻¹)ᴴ * Bᴴ) := by rw [Matrix.conjTranspose_mul]
    _ = B * (A⁻¹ * B⁻¹) * A := by rw [hinvH, hBH]; simp [Matrix.mul_assoc]
    _ = B * (B⁻¹ * A⁻¹) * A := by rw [hswap]
    _ = (B * B⁻¹) * (A⁻¹ * A) := by simp [Matrix.mul_assoc]
    _ = 1 := by rw [Matrix.mul_nonsing_inv _ hUB, Matrix.nonsing_inv_mul _ hUA, one_mul]

lemma cayley_unitary {m : ℕ} (x : Fin m × Fin m → ℝ) :
    cayley x * (cayley x)ᴴ = 1 :=
  cayley_unitary_aux (sMat_skew x)

/-- Every skew-Hermitian matrix arises from real parameters. -/
lemma skew_reaches {m : ℕ} {S₀ : Matrix (Fin m) (Fin m) ℂ} (hS : S₀ᴴ = -S₀) :
    ∃ x : Fin m × Fin m → ℝ, sMat x = S₀ := by
  classical
  have hskew : ∀ p q, star (S₀ q p) = -(S₀ p q) := by
    intro p q
    have h1 : S₀ᴴ p q = (-S₀) p q := by rw [hS]
    rwa [Matrix.conjTranspose_apply, Matrix.neg_apply] at h1
  set f : Fin m × Fin m → ℝ := fun pq => if pq.1 = pq.2 then (S₀ pq.1 pq.1).im
    else if pq.1 < pq.2 then (S₀ pq.1 pq.2).re else (S₀ pq.2 pq.1).im with hf
  have hf1 : ∀ p, f (p, p) = (S₀ p p).im := fun p => by simp [hf]
  have hf2 : ∀ p q : Fin m, p < q → f (p, q) = (S₀ p q).re := fun p q h => by
    simp [hf, h.ne, h]
  have hf3 : ∀ p q : Fin m, q < p → f (p, q) = (S₀ q p).im := fun p q h => by
    simp [hf, h.ne', asymm h]
  refine ⟨f, ?_⟩
  ext p q
  simp only [sMat, Matrix.of_apply]
  rcases lt_trichotomy p q with h | h | h
  · rw [if_neg h.ne, if_pos h, hf2 p q h, hf3 q p h]
    apply Complex.ext <;> simp
  · subst h
    rw [if_pos rfl, hf1 p]
    have hre : (S₀ p p).re = 0 := by
      have h1 := congrArg Complex.re (hskew p p)
      simp only [Complex.star_def, Complex.conj_re, Complex.neg_re] at h1
      linarith
    apply Complex.ext <;> simp [hre]
  · rw [if_neg h.ne', if_neg (asymm h), hf2 q p h, hf3 p q h]
    have hval : S₀ p q = -star (S₀ q p) := by
      have h1 := hskew p q
      linear_combination h1
    rw [hval]
    apply Complex.ext <;> simp

/-- Unimodular scalar multiples of unitaries are unitary. -/
lemma smul_unitary {m : ℕ} {c : ℂ} {W : Matrix (Fin m) (Fin m) ℂ}
    (hc : star c * c = 1) (hW : W * Wᴴ = 1) : (c • W) * (c • W)ᴴ = 1 := by
  rw [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hW,
    show c * star c = 1 from by rw [mul_comm]; exact hc]
  simp

/-- Any unitary `W` with `1 + W` nonsingular is in the image of the Cayley map. -/
lemma cayley_reaches {m : ℕ} {W : Matrix (Fin m) (Fin m) ℂ}
    (hW : W * Wᴴ = 1) (hdet : ((1 : Matrix (Fin m) (Fin m) ℂ) + W).det ≠ 0) :
    ∃ x : Fin m × Fin m → ℝ, cayley x = W := by
  classical
  set A := (1 : Matrix (Fin m) (Fin m) ℂ) + W with hA
  have hUA : IsUnit A.det := isUnit_iff_ne_zero.mpr hdet
  set S₀ := (1 - W) * A⁻¹ with hS0
  have hWH : Wᴴ * W = 1 := mul_eq_one_comm.mp hW
  have hAH : Aᴴ = 1 + Wᴴ := by
    rw [hA, Matrix.conjTranspose_add, Matrix.conjTranspose_one]
  have hdetAH : (Aᴴ).det ≠ 0 := by
    rw [Matrix.det_conjTranspose, star_ne_zero]
    exact hdet
  have hUAH : IsUnit (Aᴴ).det := isUnit_iff_ne_zero.mpr hdetAH
  have hkey : (1 - Wᴴ) * A = -(Aᴴ * (1 - W)) := by
    rw [hA, hAH]
    have e1 : ((1 : Matrix (Fin m) (Fin m) ℂ) - Wᴴ) * (1 + W)
        = 1 + W - Wᴴ - Wᴴ * W := by noncomm_ring
    have e2 : ((1 : Matrix (Fin m) (Fin m) ℂ) + Wᴴ) * (1 - W)
        = 1 - W + Wᴴ - Wᴴ * W := by noncomm_ring
    rw [e1, e2, hWH]
    abel
  have hskew : S₀ᴴ = -S₀ := by
    rw [hS0, Matrix.conjTranspose_mul, Matrix.conjTranspose_nonsing_inv,
      Matrix.conjTranspose_sub, Matrix.conjTranspose_one]
    have h2 : (Aᴴ)⁻¹ * ((1 - Wᴴ) * A) * A⁻¹ = (Aᴴ)⁻¹ * (-(Aᴴ * (1 - W))) * A⁻¹ := by
      rw [hkey]
    calc (Aᴴ)⁻¹ * (1 - Wᴴ)
        = (Aᴴ)⁻¹ * ((1 - Wᴴ) * A) * A⁻¹ := by
          rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hUA,
            Matrix.mul_one]
      _ = (Aᴴ)⁻¹ * (-(Aᴴ * (1 - W))) * A⁻¹ := h2
      _ = -((Aᴴ)⁻¹ * Aᴴ * (1 - W) * A⁻¹) := by
          simp [Matrix.mul_assoc]
      _ = -((1 - W) * A⁻¹) := by
          rw [Matrix.nonsing_inv_mul _ hUAH, Matrix.one_mul]
  obtain ⟨x, hx⟩ := skew_reaches hskew
  refine ⟨x, ?_⟩
  have hAA : A * A⁻¹ = 1 := Matrix.mul_nonsing_inv _ hUA
  have hsum : A + (1 - W) = (2 : ℂ) • (1 : Matrix (Fin m) (Fin m) ℂ) := by
    rw [hA, two_smul]
    abel
  have hdiff : A - (1 - W) = (2 : ℂ) • W := by
    rw [hA, two_smul]
    abel
  have h1pS : 1 + S₀ = (2 : ℂ) • A⁻¹ := by
    rw [hS0]
    calc (1 : Matrix (Fin m) (Fin m) ℂ) + (1 - W) * A⁻¹
        = A * A⁻¹ + (1 - W) * A⁻¹ := by rw [hAA]
      _ = (A + (1 - W)) * A⁻¹ := (Matrix.add_mul _ _ _).symm
      _ = ((2 : ℂ) • (1 : Matrix (Fin m) (Fin m) ℂ)) * A⁻¹ := by rw [hsum]
      _ = (2 : ℂ) • A⁻¹ := by rw [Matrix.smul_mul, Matrix.one_mul]
  have h1mS : 1 - S₀ = (2 : ℂ) • (W * A⁻¹) := by
    rw [hS0]
    calc (1 : Matrix (Fin m) (Fin m) ℂ) - (1 - W) * A⁻¹
        = A * A⁻¹ - (1 - W) * A⁻¹ := by rw [hAA]
      _ = (A - (1 - W)) * A⁻¹ := (Matrix.sub_mul _ _ _).symm
      _ = ((2 : ℂ) • W) * A⁻¹ := by rw [hdiff]
      _ = (2 : ℂ) • (W * A⁻¹) := Matrix.smul_mul _ _ _
  have hinv : (1 + S₀)⁻¹ = (2⁻¹ : ℂ) • A := by
    apply Matrix.inv_eq_right_inv
    rw [h1pS, Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.nonsing_inv_mul _ hUA]
    norm_num
  show (1 - sMat x) * (1 + sMat x)⁻¹ = W
  rw [hx]
  rw [h1mS, hinv, Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_assoc,
    Matrix.nonsing_inv_mul _ hUA, Matrix.mul_one]
  norm_num

/-! ### Section E: matrices over the polynomial ring and evaluation bridges -/

/-- The generic skew-Hermitian matrix over the polynomial ring. -/
def Spoly (m : ℕ) : Matrix (Fin m) (Fin m) (MvPolynomial (Fin m × Fin m) ℂ) :=
  Matrix.of fun p q =>
    if p = q then MvPolynomial.C Complex.I * MvPolynomial.X (p, p)
    else if p < q then
      MvPolynomial.X (p, q) + MvPolynomial.C Complex.I * MvPolynomial.X (q, p)
    else -MvPolynomial.X (q, p) + MvPolynomial.C Complex.I * MvPolynomial.X (p, q)

/-- Evaluation at a real parameter point, as a ring hom. -/
def evalx {m : ℕ} (x : Fin m × Fin m → ℝ) :
    MvPolynomial (Fin m × Fin m) ℂ →+* ℂ :=
  MvPolynomial.eval (fun pq => (x pq : ℂ))

lemma evalx_mat_Spoly {m : ℕ} (x : Fin m × Fin m → ℝ) :
    (Spoly m).map (evalx x) = sMat x := by
  ext p q
  rw [Matrix.map_apply]
  simp only [Spoly, sMat, Matrix.of_apply]
  rcases lt_trichotomy p q with h | h | h
  · rw [if_neg h.ne, if_pos h, if_neg h.ne, if_pos h]
    simp [evalx]
  · subst h
    rw [if_pos rfl, if_pos rfl]
    simp [evalx]
  · rw [if_neg h.ne', if_neg (asymm h), if_neg h.ne', if_neg (asymm h)]
    simp [evalx]

/-- `1 + S` over the polynomial ring. -/
def Apoly (m : ℕ) : Matrix (Fin m) (Fin m) (MvPolynomial (Fin m × Fin m) ℂ) :=
  1 + Spoly m

/-- The numerator matrix `(1 - S) * adjugate (1 + S)` over the polynomial ring. -/
def Npoly (m : ℕ) : Matrix (Fin m) (Fin m) (MvPolynomial (Fin m × Fin m) ℂ) :=
  (1 - Spoly m) * (Apoly m).adjugate

/-- The denominator polynomial `det (1 + S)`. -/
def Dpoly (m : ℕ) : MvPolynomial (Fin m × Fin m) ℂ := (Apoly m).det

lemma evalx_mat_Apoly {m : ℕ} (x : Fin m × Fin m → ℝ) :
    (evalx x).mapMatrix (Apoly m) = 1 + sMat x := by
  rw [Apoly, map_add, map_one, RingHom.mapMatrix_apply, evalx_mat_Spoly]

lemma evalx_Dpoly {m : ℕ} (x : Fin m × Fin m → ℝ) :
    evalx x (Dpoly m) = (1 + sMat x).det := by
  rw [Dpoly, RingHom.map_det, evalx_mat_Apoly]

lemma evalx_Dpoly_ne_zero {m : ℕ} (x : Fin m × Fin m → ℝ) :
    evalx x (Dpoly m) ≠ 0 := by
  rw [evalx_Dpoly]
  exact det_one_add_skew_ne_zero (sMat_skew x)

lemma evalx_mat_Npoly {m : ℕ} (x : Fin m × Fin m → ℝ) :
    (Npoly m).map (evalx x) = ((1 + sMat x).det) • cayley x := by
  have h : (evalx x).mapMatrix (Npoly m)
      = ((1 : Matrix (Fin m) (Fin m) ℂ) - sMat x) * (1 + sMat x).adjugate := by
    rw [Npoly, map_mul, map_sub, map_one, RingHom.map_adjugate, evalx_mat_Apoly,
      RingHom.mapMatrix_apply, evalx_mat_Spoly]
  rw [← RingHom.mapMatrix_apply, h]
  have hdet : (1 + sMat x).det ≠ 0 := det_one_add_skew_ne_zero (sMat_skew x)
  have hadj : (1 + sMat x).adjugate = (1 + sMat x).det • (1 + sMat x)⁻¹ := by
    rw [Matrix.inv_def, Ring.inverse_eq_inv, smul_smul, mul_inv_cancel₀ hdet, one_smul]
  rw [hadj, Matrix.mul_smul, cayley]

lemma evalx_mulVec {m r : ℕ} (x : Fin m × Fin m → ℝ)
    (M : Matrix (Fin m) (Fin r) (MvPolynomial (Fin m × Fin m) ℂ))
    (c : Fin r → MvPolynomial (Fin m × Fin m) ℂ) (i : Fin m) :
    evalx x ((M.mulVec c) i) = ((M.map (evalx x)).mulVec (fun t => evalx x (c t))) i := by
  rw [Matrix.mulVec_apply_eq_sum, Matrix.mulVec_apply_eq_sum, map_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [map_mul, Matrix.map_apply]

/-! ### Section F: witnesses via orthonormal bases on Euclidean space -/

open scoped InnerProductSpace

lemma pair_eq_inner {m : ℕ} (x y : EuclideanSpace ℂ (Fin m)) :
    pair (WithLp.ofLp x) (WithLp.ofLp y) = inner ℂ x y := by
  rw [PiLp.inner_apply]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [RCLike.inner_apply, Complex.star_def]
  ring

lemma euclid_decomp {m : ℕ} (x : EuclideanSpace ℂ (Fin m)) :
    x = ∑ i, x i • EuclideanSpace.single i (1 : ℂ) := by
  classical
  conv_lhs => rw [← (EuclideanSpace.basisFun (Fin m) ℂ).sum_repr x]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply]

/-- The matrix of a linear isometry equivalence of Euclidean space. -/
def matOf {m : ℕ}
    (g : EuclideanSpace ℂ (Fin m) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin m)) :
    Matrix (Fin m) (Fin m) ℂ :=
  Matrix.of fun i j => g (EuclideanSpace.single j 1) i

lemma matOf_mulVec {m : ℕ}
    (g : EuclideanSpace ℂ (Fin m) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin m)) (y : Fin m → ℂ) :
    (matOf g).mulVec y = WithLp.ofLp (g (WithLp.toLp 2 y)) := by
  funext i
  rw [Matrix.mulVec_apply_eq_sum]
  conv_rhs => rw [euclid_decomp (WithLp.toLp 2 y)]
  rw [map_sum, WithLp.ofLp_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_smul, WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul, matOf, Matrix.of_apply]
  ring

lemma matOf_unitary {m : ℕ}
    (g : EuclideanSpace ℂ (Fin m) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin m)) :
    (matOf g) * (matOf g)ᴴ = 1 := by
  classical
  rw [← mul_eq_one_comm]
  ext i j
  rw [Matrix.mul_apply, Matrix.one_apply]
  have h1 : ∑ r, ((matOf g)ᴴ) i r * (matOf g) r j
      = pair (WithLp.ofLp (g (EuclideanSpace.single i 1)))
          (WithLp.ofLp (g (EuclideanSpace.single j 1))) := by
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [Matrix.conjTranspose_apply, matOf, Matrix.of_apply, Matrix.of_apply]
  rw [h1, pair_eq_inner, LinearIsometryEquiv.inner_map_map,
    EuclideanSpace.inner_single_left]
  simp

/-- Any orthonormal family indexed by `Fin r` extends to an orthonormal basis whose
first `r` vectors are the given family. -/
lemma exists_adapted_onb {m r : ℕ} (hr : r ≤ m)
    (w : Fin r → EuclideanSpace ℂ (Fin m)) (hw : Orthonormal ℂ w) :
    ∃ b : OrthonormalBasis (Fin m) ℂ (EuclideanSpace ℂ (Fin m)),
      ∀ t : Fin r, b (Fin.castLE hr t) = w t := by
  classical
  set v₀ : Fin m → EuclideanSpace ℂ (Fin m) := fun i =>
    if h : (i : ℕ) < r then w ⟨i, h⟩ else 0 with hv₀
  set s : Set (Fin m) := {i : Fin m | (i : ℕ) < r} with hs
  have hcard : Module.finrank ℂ (EuclideanSpace ℂ (Fin m)) = Fintype.card (Fin m) := by
    rw [finrank_euclideanSpace_fin, Fintype.card_fin]
  have hv : ∀ (i : Fin m) (h : (i : ℕ) < r), v₀ i = w ⟨i, h⟩ := by
    intro i h
    simp only [hv₀]
    rw [dif_pos h]
  have hres : Orthonormal ℂ (s.domRestrict v₀) := by
    have hcomp : s.domRestrict v₀ = w ∘ (fun i : s => (⟨(i : Fin m), i.2⟩ : Fin r)) := by
      funext i
      exact hv (i : Fin m) i.2
    rw [hcomp]
    refine hw.comp _ ?_
    intro a b hab
    have h2 : (⟨(a : Fin m), a.2⟩ : Fin r) = (⟨(b : Fin m), b.2⟩ : Fin r) := hab
    apply Subtype.ext
    apply Fin.ext
    exact congrArg (fun z : Fin r => (z : ℕ)) h2
  obtain ⟨b, hb⟩ := hres.exists_orthonormalBasis_extension_of_card_eq hcard
  refine ⟨b, fun t => ?_⟩
  have ht : ((Fin.castLE hr t : Fin m) : ℕ) < r := t.2
  have hmem : (Fin.castLE hr t : Fin m) ∈ s := ht
  rw [hb _ hmem, hv _ ht]
  congr 1

/-- Every subspace of Euclidean space has an orthonormal spanning family indexed by
`Fin (finrank A)`. -/
lemma subspace_onb {m : ℕ} (A : Submodule ℂ (EuclideanSpace ℂ (Fin m))) :
    ∃ w : Fin (Module.finrank ℂ A) → EuclideanSpace ℂ (Fin m),
      Orthonormal ℂ w ∧ Submodule.span ℂ (Set.range w) = A := by
  refine ⟨fun t => ((stdOrthonormalBasis ℂ A) t : EuclideanSpace ℂ (Fin m)), ?_, ?_⟩
  · exact (A.subtypeₗᵢ.orthonormal_comp_iff).mpr (stdOrthonormalBasis ℂ A).orthonormal
  · have h1 : Set.range (fun t => ((stdOrthonormalBasis ℂ A) t : EuclideanSpace ℂ (Fin m)))
        = A.subtype '' (Set.range (stdOrthonormalBasis ℂ A)) := by
      rw [← Set.range_comp]
      rfl
    have h2 : Submodule.span ℂ (Set.range (⇑(stdOrthonormalBasis ℂ A))) = ⊤ := by
      rw [← OrthonormalBasis.coe_toBasis]
      exact Module.Basis.span_eq _
    rw [h1, Submodule.span_image, h2, Submodule.map_top, Submodule.range_subtype]

/-- The normalized nonzero vector as an orthonormal singleton family. -/
lemma orthonormal_normalize {m : ℕ} {x : EuclideanSpace ℂ (Fin m)} (hx : x ≠ 0) :
    Orthonormal ℂ (fun _ : Fin 1 => ((‖x‖⁻¹ : ℝ) : ℂ) • x) := by
  rw [orthonormal_iff_ite]
  intro i j
  have hij : i = j := Subsingleton.elim i j
  subst hij
  rw [if_pos rfl, inner_smul_left, inner_smul_right, inner_self_eq_norm_sq_to_K,
    Complex.conj_ofReal]
  have hnorm : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  have hnorm' : ((‖x‖ : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hnorm
  push_cast
  field_simp
  norm_cast

/-- W1': some unitary makes the cross pairing of two nonzero vectors nonzero. -/
lemma exists_unitary_pair_ne_zero {m : ℕ} (hm : 0 < m) {x y : Fin m → ℂ}
    (hx : x ≠ 0) (hy : y ≠ 0) :
    ∃ W : Matrix (Fin m) (Fin m) ℂ, W * Wᴴ = 1 ∧ pair x (W.mulVec y) ≠ 0 := by
  classical
  set xE : EuclideanSpace ℂ (Fin m) := WithLp.toLp 2 x with hxE
  set yE : EuclideanSpace ℂ (Fin m) := WithLp.toLp 2 y with hyE
  have hxE0 : xE ≠ 0 := fun h => hx (congrArg WithLp.ofLp h)
  have hyE0 : yE ≠ 0 := fun h => hy (congrArg WithLp.ofLp h)
  have h1m : 1 ≤ m := hm
  obtain ⟨bx, hbx⟩ := exists_adapted_onb h1m _ (orthonormal_normalize hxE0)
  obtain ⟨by', hby⟩ := exists_adapted_onb h1m _ (orthonormal_normalize hyE0)
  set g := by'.equiv bx (Equiv.refl (Fin m)) with hg
  refine ⟨matOf g, matOf_unitary g, ?_⟩
  rw [matOf_mulVec]
  have hgy : g yE = (‖yE‖ : ℂ) • (((‖xE‖⁻¹ : ℝ) : ℂ) • xE) := by
    have hyy : yE = (‖yE‖ : ℂ) • (((‖yE‖⁻¹ : ℝ) : ℂ) • yE) := by
      rw [smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hyE0),
        Complex.ofReal_one, one_smul]
    conv_lhs => rw [hyy]
    rw [map_smul]
    congr 1
    have h0 : (((‖yE‖⁻¹ : ℝ) : ℂ) • yE) = by' (Fin.castLE h1m 0) := (hby 0).symm
    rw [h0, hg, OrthonormalBasis.equiv_apply_basis]
    simpa using hbx 0
  rw [hgy, WithLp.ofLp_smul, WithLp.ofLp_smul, pair_smul_right, pair_smul_right]
  have hox : WithLp.ofLp xE = x := rfl
  rw [hox]
  apply mul_ne_zero
  · rw [Complex.ofReal_ne_zero]
    exact norm_ne_zero_iff.mpr hyE0
  apply mul_ne_zero
  · rw [Complex.ofReal_ne_zero]
    exact inv_ne_zero (norm_ne_zero_iff.mpr hxE0)
  · exact pair_self_ne_zero hx

/-- The index bookkeeping for W2: the first `a` indices together with the rotation
by `a` of the first `b` indices make up exactly the first `min m (a+b)` indices. -/
lemma index_union {m a b : ℕ} [NeZero m] (hm : 0 < m) (ha : a ≤ m) (hb : b ≤ m) :
    {i : Fin m | (i : ℕ) < a} ∪ (⇑(Equiv.addLeft (Fin.ofNat m a)) '' {i : Fin m | (i : ℕ) < b})
      = {i : Fin m | (i : ℕ) < min m (a + b)} := by
  have hσval : ∀ j : Fin m, ((Fin.ofNat m a + j : Fin m) : ℕ) = ((a % m) + (j : ℕ)) % m := by
    intro j
    rw [Fin.val_add, Fin.val_ofNat]
  ext i
  simp only [Set.mem_union, Set.mem_ofPred_eq, Set.mem_image, Equiv.coe_addLeft]
  constructor
  · rintro (h | ⟨j, hj, rfl⟩)
    · exact lt_of_lt_of_le h (le_min ha (Nat.le_add_right a b))
    · rw [hσval j, lt_min_iff]
      have hjm : (j : ℕ) < m := j.isLt
      by_cases ham : a < m
      · rw [Nat.mod_eq_of_lt ham]
        by_cases hsum : a + (j : ℕ) < m
        · rw [Nat.mod_eq_of_lt hsum]
          omega
        · have h2 : (a + (j : ℕ)) % m = a + (j : ℕ) - m := by
            rw [Nat.mod_eq_sub_mod (by omega)]
            exact Nat.mod_eq_of_lt (by omega)
          rw [h2]
          omega
      · have ham' : a = m := le_antisymm ha (le_of_not_gt ham)
        have hlt : ((a % m) + (j : ℕ)) % m < m := Nat.mod_lt _ hm
        omega
  · intro hi
    rw [lt_min_iff] at hi
    by_cases hia : (i : ℕ) < a
    · exact Or.inl hia
    · right
      have ham : a < m := lt_of_le_of_lt (le_of_not_gt hia) hi.1
      refine ⟨⟨(i : ℕ) - a, by omega⟩, ?_, ?_⟩
      · show (i : ℕ) - a < b
        omega
      · apply Fin.ext
        rw [hσval]
        show ((a % m) + ((i : ℕ) - a)) % m = (i : ℕ)
        rw [Nat.mod_eq_of_lt ham]
        have h3 : a + ((i : ℕ) - a) = (i : ℕ) := by omega
        rw [h3, Nat.mod_eq_of_lt hi.1]

/-- W2: some unitary puts `B` in generic position relative to `A`: the sup of `A`
with the image of `B` has the maximal possible rank `min m (finrank A + finrank B)`. -/
lemma exists_unitary_sup_finrank {m : ℕ} (hm : 0 < m)
    (A B : Submodule ℂ (Fin m → ℂ)) :
    ∃ W : Matrix (Fin m) (Fin m) ℂ, W * Wᴴ = 1 ∧
      Module.finrank ℂ (A ⊔ Submodule.map (Matrix.mulVecLin W) B :
          Submodule ℂ (Fin m → ℂ))
        = min m (Module.finrank ℂ A + Module.finrank ℂ B) := by
  classical
  have : NeZero m := ⟨hm.ne'⟩
  set eL : EuclideanSpace ℂ (Fin m) →ₗ[ℂ] (Fin m → ℂ) :=
    (WithLp.linearEquiv 2 ℂ (Fin m → ℂ)).toLinearMap with heL
  set eLi : (Fin m → ℂ) →ₗ[ℂ] EuclideanSpace ℂ (Fin m) :=
    (WithLp.linearEquiv 2 ℂ (Fin m → ℂ)).symm.toLinearMap with heLi
  set A' : Submodule ℂ (EuclideanSpace ℂ (Fin m)) := Submodule.map eLi A with hA'def
  set B' : Submodule ℂ (EuclideanSpace ℂ (Fin m)) := Submodule.map eLi B with hB'def
  have hmapback : ∀ X : Submodule ℂ (Fin m → ℂ),
      Submodule.map eL (Submodule.map eLi X) = X := by
    intro X
    ext z
    simp only [Submodule.mem_map]
    constructor
    · rintro ⟨y, ⟨u, hu, rfl⟩, rfl⟩
      simpa [heL, heLi] using hu
    · intro hz
      exact ⟨eLi z, ⟨z, hz, rfl⟩, by simp [heL, heLi]⟩
  have hfinL : ∀ X : Submodule ℂ (EuclideanSpace ℂ (Fin m)),
      Module.finrank ℂ (Submodule.map eL X) = Module.finrank ℂ X := by
    intro X
    exact LinearEquiv.finrank_map_eq (WithLp.linearEquiv 2 ℂ (Fin m → ℂ)) X
  have hfinA : Module.finrank ℂ A' = Module.finrank ℂ A := by
    rw [hA'def]
    exact LinearEquiv.finrank_map_eq (WithLp.linearEquiv 2 ℂ (Fin m → ℂ)).symm A
  have hfinB : Module.finrank ℂ B' = Module.finrank ℂ B := by
    rw [hB'def]
    exact LinearEquiv.finrank_map_eq (WithLp.linearEquiv 2 ℂ (Fin m → ℂ)).symm B
  set a := Module.finrank ℂ A' with hadef
  set b := Module.finrank ℂ B' with hbdef
  have hEfin : Module.finrank ℂ (EuclideanSpace ℂ (Fin m)) = m := finrank_euclideanSpace_fin
  have haM : a ≤ m := by
    rw [hadef]
    calc Module.finrank ℂ A' ≤ Module.finrank ℂ (EuclideanSpace ℂ (Fin m)) := A'.finrank_le
      _ = m := hEfin
  have hbM : b ≤ m := by
    rw [hbdef]
    calc Module.finrank ℂ B' ≤ Module.finrank ℂ (EuclideanSpace ℂ (Fin m)) := B'.finrank_le
      _ = m := hEfin
  obtain ⟨wA, hwA_on, hwA_span⟩ := subspace_onb A'
  obtain ⟨wB, hwB_on, hwB_span⟩ := subspace_onb B'
  obtain ⟨eA, heA⟩ := exists_adapted_onb haM wA hwA_on
  obtain ⟨eB, heB⟩ := exists_adapted_onb hbM wB hwB_on
  set σ : Equiv.Perm (Fin m) := Equiv.addLeft (Fin.ofNat m a) with hσ
  set g := eB.equiv eA σ with hg
  set gmap : EuclideanSpace ℂ (Fin m) →ₗ[ℂ] EuclideanSpace ℂ (Fin m) :=
    g.toLinearEquiv.toLinearMap with hgmap
  refine ⟨matOf g, matOf_unitary g, ?_⟩
  have hAA' : Submodule.map eL A' = A := by
    rw [hA'def]
    exact hmapback A
  have hbridge : Submodule.map (Matrix.mulVecLin (matOf g)) B
      = Submodule.map eL (Submodule.map gmap B') := by
    rw [hB'def]
    ext z
    simp only [Submodule.mem_map, Matrix.mulVecLin_apply]
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine ⟨gmap (eLi y), ⟨eLi y, ⟨y, hy, rfl⟩, rfl⟩, ?_⟩
      rw [matOf_mulVec]
      rfl
    · rintro ⟨w, ⟨u, ⟨y, hy, rfl⟩, rfl⟩, rfl⟩
      refine ⟨y, hy, ?_⟩
      rw [matOf_mulVec]
      rfl
  have hA'span : A' = Submodule.span ℂ (Set.range fun t : Fin a => eA (Fin.castLE haM t)) := by
    rw [← hwA_span]
    congr 1
    rw [show (fun t : Fin a => eA (Fin.castLE haM t)) = wA from funext heA]
  have hB'span : B' = Submodule.span ℂ (Set.range fun t : Fin b => eB (Fin.castLE hbM t)) := by
    rw [← hwB_span]
    congr 1
    rw [show (fun t : Fin b => eB (Fin.castLE hbM t)) = wB from funext heB]
  have hmapg : Submodule.map gmap B'
      = Submodule.span ℂ (Set.range fun t : Fin b => eA (σ (Fin.castLE hbM t))) := by
    rw [hB'span, Submodule.map_span]
    congr 1
    rw [← Set.range_comp]
    congr 1
    funext t
    simp only [Function.comp_apply, hgmap, LinearEquiv.coe_coe,
      LinearIsometryEquiv.coe_toLinearEquiv]
    rw [hg]
    exact OrthonormalBasis.equiv_apply_basis eB eA σ _
  have hmnM : min m (a + b) ≤ m := min_le_left _ _
  have hidx := index_union (a := a) (b := b) hm haM hbM
  have hsup : A' ⊔ Submodule.map gmap B'
      = Submodule.span ℂ (Set.range fun t : Fin (min m (a + b)) => eA (Fin.castLE hmnM t)) := by
    rw [hA'span, hmapg, ← Submodule.span_union]
    congr 1
    have h1 : (Set.range fun t : Fin a => eA (Fin.castLE haM t))
        = ⇑eA '' {i : Fin m | (i : ℕ) < a} := by
      rw [← Fin.range_castLE haM, ← Set.range_comp]
      rfl
    have h2 : (Set.range fun t : Fin b => eA (σ (Fin.castLE hbM t)))
        = ⇑eA '' (⇑σ '' {i : Fin m | (i : ℕ) < b}) := by
      rw [← Fin.range_castLE hbM, ← Set.range_comp, ← Set.range_comp]
      rfl
    have h3 : (Set.range fun t : Fin (min m (a + b)) => eA (Fin.castLE hmnM t))
        = ⇑eA '' {i : Fin m | (i : ℕ) < min m (a + b)} := by
      rw [← Fin.range_castLE hmnM, ← Set.range_comp]
      rfl
    rw [h1, h2, h3, ← Set.image_union, hσ, hidx]
  have hrank : Module.finrank ℂ
      (Submodule.span ℂ (Set.range fun t : Fin (min m (a + b)) => eA (Fin.castLE hmnM t)))
      = min m (a + b) := by
    have hli : LinearIndependent ℂ (fun t : Fin (min m (a + b)) => eA (Fin.castLE hmnM t)) :=
      (eA.orthonormal.linearIndependent).comp _ (Fin.castLE_injective hmnM)
    rw [finrank_span_eq_card hli, Fintype.card_fin]
  calc Module.finrank ℂ (A ⊔ Submodule.map (Matrix.mulVecLin (matOf g)) B :
          Submodule ℂ (Fin m → ℂ))
      = Module.finrank ℂ (Submodule.map eL A' ⊔ Submodule.map eL (Submodule.map gmap B') :
          Submodule ℂ (Fin m → ℂ)) := by rw [hAA', hbridge]
    _ = Module.finrank ℂ (Submodule.map eL (A' ⊔ Submodule.map gmap B')) := by
        rw [Submodule.map_sup]
    _ = Module.finrank ℂ (A' ⊔ Submodule.map gmap B' :
          Submodule ℂ (EuclideanSpace ℂ (Fin m))) := hfinL _
    _ = min m (a + b) := by rw [hsup, hrank]
    _ = min m (Module.finrank ℂ A + Module.finrank ℂ B) := by rw [hfinA, hfinB]

/-! ### Section G: rank bookkeeping for the combined family -/

lemma span_restrict_eq {m : ℕ} {ι : Type} (v : ι → Fin m → ℂ) (S : Finset ι) :
    Submodule.span ℂ (Set.range fun i : (S : Set ι) => v i)
      = Submodule.span ℂ (v '' (S : Set ι)) := by
  rw [Set.image_eq_range]

lemma rk_eq_span_image {m : ℕ} {ι : Type} (v : ι → Fin m → ℂ) (S : Finset ι) :
    rk v S = Module.finrank ℂ (Submodule.span ℂ (v '' (S : Set ι))) := by
  rw [rk, span_restrict_eq]

lemma coe_disjSum_set {n₁ n₂ : ℕ} (S : Finset (Fin n₁)) (T : Finset (Fin n₂)) :
    ((S.disjSum T : Finset (Fin n₁ ⊕ Fin n₂)) : Set (Fin n₁ ⊕ Fin n₂))
      = Sum.inl '' (S : Set (Fin n₁)) ∪ Sum.inr '' (T : Set (Fin n₂)) := by
  ext x
  simp only [Finset.mem_coe, Finset.mem_disjSum, Set.mem_union, Set.mem_image]

lemma span_disjSum {m n₁ n₂ : ℕ} (u : Fin n₁ → Fin m → ℂ) (w : Fin n₂ → Fin m → ℂ)
    (S : Finset (Fin n₁)) (T : Finset (Fin n₂)) :
    Submodule.span ℂ
        (Set.range fun i : ((S.disjSum T : Finset (Fin n₁ ⊕ Fin n₂)) : Set (Fin n₁ ⊕ Fin n₂)) =>
          Sum.elim u w i)
      = Submodule.span ℂ (u '' (S : Set (Fin n₁))) ⊔ Submodule.span ℂ (w '' (T : Set (Fin n₂))) := by
  rw [span_restrict_eq, coe_disjSum_set, Set.image_union, ← Submodule.span_union]
  congr 2
  · rw [Set.image_image]
    exact Set.image_congr fun a _ => rfl
  · rw [Set.image_image]
    exact Set.image_congr fun a _ => rfl

lemma rk_disjSum_eq {m n₁ n₂ : ℕ} (u : Fin n₁ → Fin m → ℂ) (w : Fin n₂ → Fin m → ℂ)
    (S : Finset (Fin n₁)) (T : Finset (Fin n₂)) :
    rk (Sum.elim u w) (S.disjSum T)
      = Module.finrank ℂ
          (Submodule.span ℂ (u '' (S : Set (Fin n₁))) ⊔ Submodule.span ℂ (w '' (T : Set (Fin n₂))) :
            Submodule ℂ (Fin m → ℂ)) := by
  rw [rk, span_disjSum]

lemma finrank_sup_le {m : ℕ} (X Y : Submodule ℂ (Fin m → ℂ)) :
    Module.finrank ℂ (X ⊔ Y : Submodule ℂ (Fin m → ℂ))
      ≤ min m (Module.finrank ℂ X + Module.finrank ℂ Y) := by
  rw [le_min_iff]
  constructor
  · calc Module.finrank ℂ (X ⊔ Y : Submodule ℂ (Fin m → ℂ))
        ≤ Module.finrank ℂ (Fin m → ℂ) := Submodule.finrank_le _
      _ = m := by rw [Module.finrank_pi, Fintype.card_fin]
  · have h := Submodule.finrank_sup_add_finrank_inf_eq X Y
    omega

/-- The `≤` half of transversality, valid for arbitrary second block. -/
lemma rk_disjSum_le {m n₁ n₂ : ℕ} (u : Fin n₁ → Fin m → ℂ) (w : Fin n₂ → Fin m → ℂ)
    (S : Finset (Fin n₁)) (T : Finset (Fin n₂)) :
    rk (Sum.elim u w) (S.disjSum T) ≤ min m (rk u S + rk w T) := by
  rw [rk_disjSum_eq, rk_eq_span_image u S, rk_eq_span_image w T]
  exact finrank_sup_le _ _

/-- Rank is invariant under an invertible (e.g. unitary) matrix acting on the family. -/
lemma finrank_map_matrix {m : ℕ} {W : Matrix (Fin m) (Fin m) ℂ} (hW : W * Wᴴ = 1)
    (X : Submodule ℂ (Fin m → ℂ)) :
    Module.finrank ℂ (Submodule.map (Matrix.mulVecLin W) X) = Module.finrank ℂ X := by
  classical
  have h1 : Wᴴ * W = 1 := mul_eq_one_comm.mp hW
  set e : (Fin m → ℂ) ≃ₗ[ℂ] (Fin m → ℂ) := LinearEquiv.ofLinearMap
    (Matrix.mulVecLin W) (Matrix.mulVecLin Wᴴ)
    (by rw [← Matrix.mulVecLin_mul, hW, Matrix.mulVecLin_one])
    (by rw [← Matrix.mulVecLin_mul, h1, Matrix.mulVecLin_one]) with he
  have hcoe : (e : (Fin m → ℂ) →ₗ[ℂ] (Fin m → ℂ)) = Matrix.mulVecLin W := by
    rw [he]
    exact LinearEquiv.toLinearMap_ofLinearMap _ _ _ _
  rw [← hcoe]
  exact LinearEquiv.finrank_map_eq e X

lemma span_image_mulVecLin {m n₂ : ℕ} (U : Matrix (Fin m) (Fin m) ℂ)
    (w : Fin n₂ → Fin m → ℂ) (T : Finset (Fin n₂)) :
    Submodule.span ℂ ((fun j => U.mulVec (w j)) '' (T : Set (Fin n₂)))
      = Submodule.map (Matrix.mulVecLin U) (Submodule.span ℂ (w '' (T : Set (Fin n₂)))) := by
  rw [Submodule.map_span]
  congr 1
  rw [Set.image_image]
  exact Set.image_congr fun a _ => rfl

/-- Unitary invariance of the rank of a block. -/
lemma rk_image_unitary {m n₂ : ℕ} {U : Matrix (Fin m) (Fin m) ℂ} (hU : U * Uᴴ = 1)
    (w : Fin n₂ → Fin m → ℂ) (T : Finset (Fin n₂)) :
    rk (fun j => U.mulVec (w j)) T = rk w T := by
  rw [rk_eq_span_image, rk_eq_span_image, span_image_mulVecLin, finrank_map_matrix hU]

/-- The lower bound on the combined rank from independent columns inside the family. -/
lemma rk_ge_of_cols {m n₁ n₂ r : ℕ} (u : Fin n₁ → Fin m → ℂ) (w : Fin n₂ → Fin m → ℂ)
    (S : Finset (Fin n₁)) (T : Finset (Fin n₂)) (col : Fin r → Fin m → ℂ)
    (hmem : ∀ t, col t ∈ (u '' (S : Set (Fin n₁)) ∪ w '' (T : Set (Fin n₂))))
    (hli : LinearIndependent ℂ col) :
    r ≤ rk (Sum.elim u w) (S.disjSum T) := by
  rw [rk_disjSum_eq]
  have h2 : Submodule.span ℂ (Set.range col)
      ≤ Submodule.span ℂ (u '' (S : Set (Fin n₁))) ⊔ Submodule.span ℂ (w '' (T : Set (Fin n₂))) := by
    rw [← Submodule.span_union]
    apply Submodule.span_mono
    rintro z ⟨t, rfl⟩
    exact hmem t
  calc r = Module.finrank ℂ (Submodule.span ℂ (Set.range col)) := by
        rw [finrank_span_eq_card hli, Fintype.card_fin]
    _ ≤ _ := Submodule.finrank_mono h2

/-- Scaling the matrix by a nonzero constant does not change the image submodule. -/
lemma map_smul_mulVecLin {m : ℕ} {c : ℂ} (hc : c ≠ 0) (W : Matrix (Fin m) (Fin m) ℂ)
    (B : Submodule ℂ (Fin m → ℂ)) :
    Submodule.map (Matrix.mulVecLin (c • W)) B = Submodule.map (Matrix.mulVecLin W) B := by
  ext z
  simp only [Submodule.mem_map, Matrix.mulVecLin_apply]
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨c • y, B.smul_mem c hy, ?_⟩
    rw [Matrix.smul_mulVec, Matrix.mulVec_smul]
  · rintro ⟨y, hy, rfl⟩
    refine ⟨c⁻¹ • y, B.smul_mem c⁻¹ hy, ?_⟩
    rw [Matrix.smul_mulVec, Matrix.mulVec_smul, smul_smul, mul_inv_cancel₀ hc, one_smul]

/-! ### Section H: Gram determinants and column independence -/

lemma mulVec_eq_sum_smul_cols {m r : ℕ} (C : Matrix (Fin m) (Fin r) ℂ) (lam : Fin r → ℂ) :
    C.mulVec lam = ∑ t, lam t • (fun i => C i t) := by
  funext i
  rw [Matrix.mulVec_apply_eq_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun t _ => ?_
  simp [mul_comm]

lemma cols_ker {m r : ℕ} {C : Matrix (Fin m) (Fin r) ℂ}
    (h : LinearIndependent ℂ (fun t : Fin r => (fun i : Fin m => C i t)))
    {lam : Fin r → ℂ} (h0 : C.mulVec lam = 0) : lam = 0 := by
  have h1 := (Fintype.linearIndependent_iff.mp h) lam
    (by rw [← mulVec_eq_sum_smul_cols, h0])
  funext t
  exact h1 t

/-- Positive-definiteness of the Hermitian Gram matrix: injective columns give a
nonzero Gram determinant. -/
lemma det_gram_ne_zero {m r : ℕ} {C : Matrix (Fin m) (Fin r) ℂ}
    (h : ∀ lam : Fin r → ℂ, C.mulVec lam = 0 → lam = 0) : (Cᴴ * C).det ≠ 0 := by
  classical
  intro hdet
  obtain ⟨lam, hlam0, hlam⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  have h1 : pair (C.mulVec lam) (C.mulVec lam) = 0 := by
    rw [pair_mulVec_left, Matrix.mulVec_mulVec, hlam, pair_zero_right]
  exact hlam0 (h lam (pair_self_eq_zero h1))

/-- A nonzero `det (P * C)` certifies that the columns of `C` are independent. -/
lemma cols_independent_of_det {m r : ℕ} {P : Matrix (Fin r) (Fin m) ℂ}
    {C : Matrix (Fin m) (Fin r) ℂ} (hdet : (P * C).det ≠ 0) :
    LinearIndependent ℂ (fun t : Fin r => (fun i : Fin m => C i t)) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro lam hlam
  have hC : C.mulVec lam = 0 := by
    rw [mulVec_eq_sum_smul_cols]
    exact hlam
  have h2 : (P * C).mulVec lam = 0 := by
    rw [← Matrix.mulVec_mulVec, hC, Matrix.mulVec_zero]
  have h3 : lam = 0 := by
    by_contra hne
    exact hdet (Matrix.exists_mulVec_eq_zero_iff.mp ⟨lam, hne, h2⟩)
  intro t
  rw [h3]
  rfl

/-! ### Section I: the condition polynomials -/

/-- The constant polynomial vector attached to `y`. -/
def vecPoly {m : ℕ} (y : Fin m → ℂ) : Fin m → MvPolynomial (Fin m × Fin m) ℂ :=
  fun s => MvPolynomial.C (y s)

/-- The polynomial column of the combined family: constants on the left block,
`Npoly ·  y` on the right block. -/
def wPoly {m n : ℕ} (v : Fin n → Fin m → ℂ) :
    Fin n ⊕ Fin n → Fin m → MvPolynomial (Fin m × Fin m) ℂ :=
  Sum.elim (fun i => vecPoly (v i)) (fun j => (Npoly m).mulVec (vecPoly (v j)))

lemma evalx_wPoly_inl {m n : ℕ} (v : Fin n → Fin m → ℂ) (x : Fin m × Fin m → ℝ)
    (i : Fin n) (r : Fin m) : evalx x (wPoly v (Sum.inl i) r) = v i r := by
  simp [wPoly, vecPoly, evalx]

lemma evalx_wPoly_inr {m n : ℕ} (v : Fin n → Fin m → ℂ) (x : Fin m × Fin m → ℝ)
    (j : Fin n) (r : Fin m) :
    evalx x (wPoly v (Sum.inr j) r)
      = evalx x (Dpoly m) * ((cayley x).mulVec (v j) r) := by
  have h1 : evalx x (wPoly v (Sum.inr j) r)
      = (((Npoly m).map (evalx x)).mulVec (fun s => evalx x (vecPoly (v j) s))) r := by
    rw [wPoly, Sum.elim_inr]
    exact evalx_mulVec x (Npoly m) (vecPoly (v j)) r
  have h2 : (fun s => evalx x (vecPoly (v j) s)) = v j := by
    funext s
    simp [vecPoly, evalx]
  rw [h1, h2, evalx_mat_Npoly, Matrix.smul_mulVec, evalx_Dpoly]
  rfl

/-- The pairing condition polynomial. -/
def gPair {m n : ℕ} (v : Fin n → Fin m → ℂ) (i j : Fin n) :
    MvPolynomial (Fin m × Fin m) ℂ :=
  ∑ r, MvPolynomial.C (star (v i r)) * wPoly v (Sum.inr j) r

lemma evalx_C {m : ℕ} (x : Fin m × Fin m → ℝ) (c : ℂ) :
    evalx x (MvPolynomial.C c) = c :=
  MvPolynomial.eval_C c

lemma evalx_gPair {m n : ℕ} (v : Fin n → Fin m → ℂ) (i j : Fin n)
    (x : Fin m × Fin m → ℝ) :
    evalx x (gPair v i j) = evalx x (Dpoly m) * pair (v i) ((cayley x).mulVec (v j)) := by
  rw [gPair, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [map_mul, evalx_C, evalx_wPoly_inr]
  ring

/-- The matrix of chosen polynomial columns. -/
def colPolyMat {m n r : ℕ} (v : Fin n → Fin m → ℂ) (aIdx : Fin r → Fin n ⊕ Fin n) :
    Matrix (Fin m) (Fin r) (MvPolynomial (Fin m × Fin m) ℂ) :=
  Matrix.of fun i t => wPoly v (aIdx t) i

/-- The matrix of chosen scalar columns at a given matrix `U`. -/
def colMat {m n r : ℕ} (v : Fin n → Fin m → ℂ) (U : Matrix (Fin m) (Fin m) ℂ)
    (aIdx : Fin r → Fin n ⊕ Fin n) : Matrix (Fin m) (Fin r) ℂ :=
  Matrix.of fun i t => Sum.elim v (fun j => U.mulVec (v j)) (aIdx t) i

/-- The rank condition polynomial. -/
def gRank {m n r : ℕ} (v : Fin n → Fin m → ℂ) (P : Matrix (Fin r) (Fin m) ℂ)
    (aIdx : Fin r → Fin n ⊕ Fin n) : MvPolynomial (Fin m × Fin m) ℂ :=
  ((P.map MvPolynomial.C) * colPolyMat v aIdx).det

/-- The per-column denominator scaling factors. -/
def sclFac {m n : ℕ} (x : Fin m × Fin m → ℝ) : Fin n ⊕ Fin n → ℂ :=
  Sum.elim (fun _ => (1 : ℂ)) (fun _ => evalx x (Dpoly m))

lemma sclFac_ne_zero {m n : ℕ} (x : Fin m × Fin m → ℝ) (a : Fin n ⊕ Fin n) :
    sclFac x a ≠ 0 := by
  rcases a with i | j
  · simp [sclFac]
  · simpa [sclFac] using evalx_Dpoly_ne_zero x

lemma evalx_gRank {m n r : ℕ} (v : Fin n → Fin m → ℂ) (P : Matrix (Fin r) (Fin m) ℂ)
    (aIdx : Fin r → Fin n ⊕ Fin n) (x : Fin m × Fin m → ℝ) :
    evalx x (gRank v P aIdx)
      = (∏ t, sclFac x (aIdx t)) * (P * colMat v (cayley x) aIdx).det := by
  rw [gRank, RingHom.map_det, RingHom.mapMatrix_apply, Matrix.map_mul]
  have hP : (P.map MvPolynomial.C).map (evalx x) = P := by
    ext i j
    simp [Matrix.map_apply, evalx]
  have hC : (colPolyMat v aIdx).map (evalx x)
      = Matrix.of (fun i t => sclFac x (aIdx t) * colMat v (cayley x) aIdx i t) := by
    ext i t
    rw [Matrix.map_apply]
    cases haIdx : aIdx t with
    | inl i' =>
        rw [colPolyMat, Matrix.of_apply, haIdx, evalx_wPoly_inl, Matrix.of_apply,
          colMat, Matrix.of_apply, haIdx]
        simp [sclFac]
    | inr j =>
        rw [colPolyMat, Matrix.of_apply, haIdx, evalx_wPoly_inr, Matrix.of_apply,
          colMat, Matrix.of_apply, haIdx]
        simp [sclFac]
  rw [hP, hC]
  have hPC : P * Matrix.of (fun i t => sclFac x (aIdx t) * colMat v (cayley x) aIdx i t)
      = Matrix.of (fun s t => sclFac x (aIdx t) * (P * colMat v (cayley x) aIdx) s t) := by
    ext s t
    rw [Matrix.mul_apply, Matrix.of_apply, Matrix.mul_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Matrix.of_apply]
    ring
  rw [hPC]
  exact Matrix.det_mul_row (fun t => sclFac x (aIdx t)) (P * colMat v (cayley x) aIdx)

/-! ### Section J: existence of nonvanishing points for each condition polynomial -/

/-- The pairing condition: its polynomial is nonzero at some real point and detects
nonorthogonality of the cross pairing. -/
lemma pair_condition {m n : ℕ} (hm : 0 < m) (v : Fin n → Fin m → ℂ)
    (i j : Fin n) (hvi : v i ≠ 0) (hvj : v j ≠ 0) :
    ∃ g : MvPolynomial (Fin m × Fin m) ℂ,
      (∃ x₀ : Fin m × Fin m → ℝ, evalx x₀ g ≠ 0) ∧
      ∀ x : Fin m × Fin m → ℝ, evalx x g ≠ 0 →
        pair (v i) ((cayley x).mulVec (v j)) ≠ 0 := by
  refine ⟨gPair v i j, ?_, ?_⟩
  · obtain ⟨W, hWu, hWp⟩ := exists_unitary_pair_ne_zero hm hvi hvj
    obtain ⟨c, hc, hcdet⟩ := exists_phase_det W
    have hc0 : c ≠ 0 := unimodular_ne_zero hc
    have hW'u : (c • W) * (c • W)ᴴ = 1 := smul_unitary hc hWu
    obtain ⟨x₀, hx₀⟩ := cayley_reaches hW'u hcdet
    refine ⟨x₀, ?_⟩
    rw [evalx_gPair, hx₀]
    apply mul_ne_zero (evalx_Dpoly_ne_zero x₀)
    rw [Matrix.smul_mulVec, pair_smul_right]
    exact mul_ne_zero hc0 hWp
  · intro x hx h0
    rw [evalx_gPair, h0, mul_zero] at hx
    exact hx rfl

/-- The rank condition for a subset pair: its polynomial is nonzero at some real point
and forces the combined family to reach the maximal rank. -/
lemma rank_condition {m n : ℕ} (hm : 0 < m) (v : Fin n → Fin m → ℂ)
    (S T : Finset (Fin n)) :
    ∃ g : MvPolynomial (Fin m × Fin m) ℂ,
      (∃ x₀ : Fin m × Fin m → ℝ, evalx x₀ g ≠ 0) ∧
      ∀ x : Fin m × Fin m → ℝ, evalx x g ≠ 0 →
        min m (rk v S + rk v T)
          ≤ rk (Sum.elim v fun j => (cayley x).mulVec (v j)) (S.disjSum T) := by
  classical
  obtain ⟨W, hWu, hWr⟩ := exists_unitary_sup_finrank hm
    (Submodule.span ℂ (v '' (S : Set (Fin n)))) (Submodule.span ℂ (v '' (T : Set (Fin n))))
  obtain ⟨c, hc, hcdet⟩ := exists_phase_det W
  have hc0 : c ≠ 0 := unimodular_ne_zero hc
  have hW'u : (c • W) * (c • W)ᴴ = 1 := smul_unitary hc hWu
  set W' := c • W with hW'def
  -- the combined span at `W'` has the maximal rank
  have hspan : Module.finrank ℂ (Submodule.span ℂ
        (v '' (S : Set (Fin n)) ∪ (fun j => W'.mulVec (v j)) '' (T : Set (Fin n))))
      = min m (rk v S + rk v T) := by
    rw [Submodule.span_union, span_image_mulVecLin, hW'def, map_smul_mulVecLin hc0, hWr,
      rk_eq_span_image, rk_eq_span_image]
  -- extract independent columns realizing the rank
  set Vset : Set (Fin m → ℂ) :=
    v '' (S : Set (Fin n)) ∪ (fun j => W'.mulVec (v j)) '' (T : Set (Fin n)) with hVset
  obtain ⟨sset, hsub, hsspan, hsli⟩ := exists_linearIndependent ℂ Vset
  have hfin : sset.Finite := hsli.setFinite
  have : Fintype ↥sset := hfin.fintype
  have hindep : LinearIndepOn ℂ id sset := hsli
  have hcard : Fintype.card ↥sset = min m (rk v S + rk v T) := by
    have h1 : Module.finrank ℂ (Submodule.span ℂ sset) = sset.toFinset.card :=
      finrank_span_set_eq_card hindep
    rw [hsspan, hspan] at h1
    rw [← Set.toFinset_card, ← h1]
  set e : Fin (min m (rk v S + rk v T)) ≃ ↥sset :=
    (Fintype.equivFinOfCardEq hcard).symm with he
  set col : Fin (min m (rk v S + rk v T)) → (Fin m → ℂ) := fun t => ((e t : ↥sset) : Fin m → ℂ)
    with hcol
  have hcol_li : LinearIndependent ℂ col := hsli.comp _ e.injective
  have hcol_mem : ∀ t, col t ∈ Vset := fun t => hsub (e t).2
  -- choose realizing indices
  have hidx : ∀ t, ∃ a : Fin n ⊕ Fin n,
      Sum.elim (fun i => i ∈ S) (fun j => j ∈ T) a ∧
      Sum.elim v (fun j => W'.mulVec (v j)) a = col t := by
    intro t
    rcases hcol_mem t with ⟨i, hiS, hvi⟩ | ⟨j, hjT, hvj⟩
    · exact ⟨Sum.inl i, hiS, hvi⟩
    · exact ⟨Sum.inr j, hjT, hvj⟩
  choose aIdx haIdx1 haIdx2 using hidx
  have hcolMat : ∀ t, (fun i => colMat v W' aIdx i t) = col t := by
    intro t
    funext i
    rw [colMat, Matrix.of_apply]
    exact congrFun (haIdx2 t) i
  set P : Matrix (Fin (min m (rk v S + rk v T))) (Fin m) ℂ := (colMat v W' aIdx)ᴴ with hP
  have hgram : (P * colMat v W' aIdx).det ≠ 0 := by
    rw [hP]
    apply det_gram_ne_zero
    intro lam h0
    apply cols_ker ?_ h0
    have hcols : (fun t => (fun i => colMat v W' aIdx i t)) = col := funext hcolMat
    rw [hcols]
    exact hcol_li
  refine ⟨gRank v P aIdx, ?_, ?_⟩
  · obtain ⟨x₀, hx₀⟩ := cayley_reaches hW'u hcdet
    refine ⟨x₀, ?_⟩
    rw [evalx_gRank, hx₀]
    apply mul_ne_zero
    · rw [Finset.prod_ne_zero_iff]
      exact fun t _ => sclFac_ne_zero x₀ (aIdx t)
    · exact hgram
  · intro x hx
    rw [evalx_gRank] at hx
    have hdet : (P * colMat v (cayley x) aIdx).det ≠ 0 := by
      intro h0
      rw [h0, mul_zero] at hx
      exact hx rfl
    have hli := cols_independent_of_det hdet
    apply rk_ge_of_cols v (fun j => (cayley x).mulVec (v j)) S T
      (fun t => (fun i => colMat v (cayley x) aIdx i t)) ?_ hli
    intro t
    rcases haIdx3 : aIdx t with i | j
    · left
      refine ⟨i, ?_, ?_⟩
      · have := haIdx1 t
        rwa [haIdx3] at this
      · funext i'
        rw [colMat, Matrix.of_apply, haIdx3]
        rfl
    · right
      refine ⟨j, ?_, ?_⟩
      · have := haIdx1 t
        rwa [haIdx3] at this
      · funext i'
        rw [colMat, Matrix.of_apply, haIdx3]
        rfl

/-! ### Section K: assembly of the main theorem -/

theorem proof : ∀ (k n : ℕ), 2 ≤ k →
    ∀ (v : Fin n → Fin k → ℂ),
      (∀ i, v i ≠ 0) → Tight v → Spanning v →
      ∃ U : Matrix (Fin k) (Fin k) ℂ,
        IsUnitary U ∧
        (∀ (i j : Fin n),
          pair (v i) (applyMat U (v j)) ≠ 0) ∧
        Transversal v (fun j => applyMat U (v j)) := by
  intro k n hk v hv0 _tight _spanning
  classical
  have hm : 0 < k := by omega
  have hpairs : ∀ ij : Fin n × Fin n, ∃ g : MvPolynomial (Fin k × Fin k) ℂ,
      (∃ x₀ : Fin k × Fin k → ℝ, evalx x₀ g ≠ 0) ∧
      ∀ x : Fin k × Fin k → ℝ, evalx x g ≠ 0 →
        pair (v ij.1) ((cayley x).mulVec (v ij.2)) ≠ 0 :=
    fun ij => pair_condition hm v ij.1 ij.2 (hv0 _) (hv0 _)
  have hranks : ∀ ST : Finset (Fin n) × Finset (Fin n),
      ∃ g : MvPolynomial (Fin k × Fin k) ℂ,
      (∃ x₀ : Fin k × Fin k → ℝ, evalx x₀ g ≠ 0) ∧
      ∀ x : Fin k × Fin k → ℝ, evalx x g ≠ 0 →
        min k (rk v ST.1 + rk v ST.2)
          ≤ rk (Sum.elim v fun j => (cayley x).mulVec (v j)) (ST.1.disjSum ST.2) :=
    fun ST => rank_condition hm v ST.1 ST.2
  choose gp hgp1 hgp2 using hpairs
  choose gr hgr1 hgr2 using hranks
  set G : MvPolynomial (Fin k × Fin k) ℂ :=
    (∏ ij : Fin n × Fin n, gp ij) * (∏ ST : Finset (Fin n) × Finset (Fin n), gr ST) with hG
  have hG0 : G ≠ 0 := by
    rw [hG]
    apply mul_ne_zero
    · rw [Finset.prod_ne_zero_iff]
      intro ij _
      obtain ⟨x₀, hx₀⟩ := hgp1 ij
      intro h
      rw [h, map_zero] at hx₀
      exact hx₀ rfl
    · rw [Finset.prod_ne_zero_iff]
      intro ST _
      obtain ⟨x₀, hx₀⟩ := hgr1 ST
      intro h
      rw [h, map_zero] at hx₀
      exact hx₀ rfl
  obtain ⟨x, hx⟩ := exists_real_eval_ne_zero' G hG0
  have hxG : evalx x G ≠ 0 := hx
  have hfac_p : ∀ ij : Fin n × Fin n, evalx x (gp ij) ≠ 0 := by
    intro ij h0
    apply hxG
    rw [hG, map_mul]
    apply mul_eq_zero_of_left
    rw [map_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ ij) h0
  have hfac_r : ∀ ST : Finset (Fin n) × Finset (Fin n), evalx x (gr ST) ≠ 0 := by
    intro ST h0
    apply hxG
    rw [hG, map_mul]
    apply mul_eq_zero_of_right
    rw [map_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ ST) h0
  refine ⟨cayley x, ?_, ?_, ?_⟩
  · show cayley x * star (cayley x) = 1
    rw [Matrix.star_eq_conjTranspose]
    exact cayley_unitary x
  · intro i j
    exact hgp2 (i, j) x (hfac_p (i, j))
  · intro S T
    have hUu : cayley x * (cayley x)ᴴ = 1 := cayley_unitary x
    apply le_antisymm
    · exact rk_disjSum_le v (fun j => applyMat (cayley x) (v j)) S T
    · have h2 := hgr2 (S, T) x (hfac_r (S, T))
      have h3 : rk (fun j => (cayley x).mulVec (v j)) T = rk v T :=
        rk_image_unitary hUu v T
      calc min k (rk v S + rk (fun j => applyMat (cayley x) (v j)) T)
          = min k (rk v S + rk v T) := by rw [h3]
        _ ≤ _ := h2

end

end Submissions.CopiesUnitaryGenericity.CopiesGenericity
