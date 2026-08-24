import Mathlib

/-!
# Finite positive-Hermitian genericity

This file gives an algebraic replacement for the informal assertion that the
positive-definite Hermitian cone is Zariski dense.  The key construction pulls
a polynomial in a matrix `K` back along `K = star L * L`, writes the entries of
`L` in independent real and imaginary coordinates, and proves that this
pullback is injective by an explicit polynomial retraction.

No measure theory, classical Zariski topology, or unproved density statement is
used.
-/

namespace Submissions.FinitePositiveHermitianGenericity.Genericity

open Matrix MvPolynomial
open scoped Matrix ComplexConjugate ComplexOrder MatrixOrder

noncomputable section

abbrev MatVar (k : ℕ) := Fin k × Fin k

/-- Real and imaginary coordinate variables for a complex matrix. -/
abbrev GramVar (k : ℕ) := Bool × Fin k × Fin k

private def delta {k : ℕ} (i j : Fin k) : ℂ :=
  if i = j then 1 else 0

/-- The polynomial matrix `L = A + iB`. -/
def lPoly {k : ℕ} (i j : Fin k) : MvPolynomial (GramVar k) ℂ :=
  X (false, i, j) + C Complex.I * X (true, i, j)

/-- The entrywise conjugate polynomial matrix `A - iB`. -/
def lBarPoly {k : ℕ} (i j : Fin k) : MvPolynomial (GramVar k) ℂ :=
  X (false, i, j) - C Complex.I * X (true, i, j)

/-- The universal Gram-matrix entry `(LᴴL)ᵢⱼ`. -/
def gramEntry {k : ℕ} (ij : MatVar k) : MvPolynomial (GramVar k) ℂ :=
  ∑ r : Fin k, lBarPoly r ij.1 * lPoly r ij.2

/-- Pullback of matrix polynomials along `K = LᴴL`. -/
def gramPull {k : ℕ} :
    MvPolynomial (MatVar k) ℂ →ₐ[ℂ] MvPolynomial (GramVar k) ℂ :=
  bind₁ gramEntry

/-- Polynomial substitution used as a left inverse of `gramPull`.

It imposes `A + iB = X` and `A - iB = 1`.
-/
def gramRetractCoord {k : ℕ} (v : GramVar k) :
    MvPolynomial (MatVar k) ℂ :=
  if v.1 then
    C ((2 * Complex.I)⁻¹) *
      (X (v.2.1, v.2.2) - C (delta v.2.1 v.2.2))
  else
    C ((2 : ℂ)⁻¹) *
      (X (v.2.1, v.2.2) + C (delta v.2.1 v.2.2))

def gramRetract {k : ℕ} :
    MvPolynomial (GramVar k) ℂ →ₐ[ℂ] MvPolynomial (MatVar k) ℂ :=
  bind₁ gramRetractCoord

lemma gramRetract_lPoly {k : ℕ} (i j : Fin k) :
    gramRetract (lPoly i j) = X (i, j) := by
  simp only [gramRetract, lPoly, map_add, map_mul, bind₁_X_right,
    gramRetractCoord, Bool.false_eq_true, if_false, if_true, map_C]
  rw [show (2 * Complex.I : ℂ)⁻¹ = -Complex.I / 2 by
    field_simp [Complex.I_ne_zero]
    simpa [pow_two] using congrArg Neg.neg Complex.I_mul_I]
  norm_num
  have hI :
      (C Complex.I : MvPolynomial (MatVar k) ℂ) *
          C (-Complex.I / 2) = C (1 / 2) := by
    rw [← map_mul]
    apply congrArg C
    calc
      Complex.I * (-Complex.I / 2) =
          -(Complex.I * Complex.I) / 2 := by ring
      _ = 1 / 2 := by rw [Complex.I_mul_I]; ring
  rw [← mul_assoc (C Complex.I), hI]
  ring_nf
  calc
    C (1 / 2 : ℂ) * X (i, j) * 2 =
        (C (1 / 2 : ℂ) * C (2 : ℂ)) * X (i, j) := by
          rw [show (2 : MvPolynomial (MatVar k) ℂ) = C (2 : ℂ) from
            (map_ofNat C 2).symm]
          ring
    _ = X (i, j) := by rw [← map_mul]; norm_num

lemma gramRetract_lBarPoly {k : ℕ} (i j : Fin k) :
    gramRetract (lBarPoly i j) = C (delta i j) := by
  simp only [gramRetract, lBarPoly, map_sub, map_mul, bind₁_X_right,
    gramRetractCoord, Bool.false_eq_true, if_false, if_true, map_C]
  rw [show (2 * Complex.I : ℂ)⁻¹ = -Complex.I / 2 by
    field_simp [Complex.I_ne_zero]
    simpa [pow_two] using congrArg Neg.neg Complex.I_mul_I]
  norm_num
  have hI :
      (C Complex.I : MvPolynomial (MatVar k) ℂ) *
          C (-Complex.I / 2) = C (1 / 2) := by
    rw [← map_mul]
    apply congrArg C
    calc
      Complex.I * (-Complex.I / 2) =
          -(Complex.I * Complex.I) / 2 := by ring
      _ = 1 / 2 := by rw [Complex.I_mul_I]; ring
  rw [← mul_assoc (C Complex.I), hI]
  ring_nf
  calc
    C (1 / 2 : ℂ) * C (delta i j) * 2 =
        (C (1 / 2 : ℂ) * C (2 : ℂ)) * C (delta i j) := by
          rw [show (2 : MvPolynomial (MatVar k) ℂ) = C (2 : ℂ) from
            (map_ofNat C 2).symm]
          ring
    _ = C (delta i j) := by rw [← map_mul]; norm_num

/-- The explicit polynomial retraction sends a universal Gram entry back to
the corresponding universal matrix variable. -/
lemma gramRetract_gramEntry {k : ℕ} (ij : MatVar k) :
    gramRetract (gramEntry ij) = X ij := by
  rcases ij with ⟨i, j⟩
  simp only [gramEntry, map_sum, map_mul, gramRetract_lBarPoly,
    gramRetract_lPoly]
  simp [delta, X]

/-- Missing local lemma 1: the Hermitian Gram pullback on matrix polynomials is
injective. -/
lemma gramPull_injective {k : ℕ} : Function.Injective (gramPull (k := k)) := by
  intro p q hpq
  have h := congrArg (fun f => gramRetract (k := k) f) hpq
  rw [gramPull, gramRetract, bind₁_bind₁, bind₁_bind₁] at h
  have hc :
      (fun i : MatVar k => (bind₁ gramRetractCoord) (gramEntry i)) =
        (X : MatVar k → MvPolynomial (MatVar k) ℂ) := by
    funext i
    exact gramRetract_gramEntry i
  rw [hc] at h
  simpa only [bind₁_X_left, AlgHom.id_apply] using h

/-- The determinant of the polynomial matrix `L`. -/
def lDetPoly {k : ℕ} : MvPolynomial (GramVar k) ℂ :=
  Matrix.det (Matrix.of fun i j : Fin k => lPoly i j)

private def identityGramEval {k : ℕ} : GramVar k → ℂ
  | (false, i, j) => delta i j
  | (true, _, _) => 0

lemma eval_lPoly_identity {k : ℕ} (i j : Fin k) :
    eval (identityGramEval (k := k)) (lPoly i j) = delta i j := by
  simp [lPoly, identityGramEval]

lemma lDetPoly_ne_zero {k : ℕ} : lDetPoly (k := k) ≠ 0 := by
  intro h
  have hz : eval (identityGramEval (k := k)) (lDetPoly (k := k)) = 0 := by
    simp [h]
  have ho : eval (identityGramEval (k := k)) (lDetPoly (k := k)) = 1 := by
    unfold lDetPoly
    rw [(eval (identityGramEval (k := k))).map_det]
    convert Matrix.det_one (n := Fin k)
    ext i j
    simp [eval_lPoly_identity, delta, Matrix.one_apply]
  exact one_ne_zero (ho.symm.trans hz)

/-- Missing local lemma 2: an independent finite row family has a nonzero
square coordinate minor. -/
lemma exists_nonzero_coord_minor {k d : ℕ} (A : Fin d → Fin k → ℂ)
    (hA : LinearIndependent ℂ A) :
    ∃ e : Fin d → Fin k, Function.Injective e ∧
      (Matrix.of fun p q => A p (e q)).det ≠ 0 := by
  classical
  let cols : Fin k → (Fin d → ℂ) := fun j p => A p j
  obtain ⟨κ, a, ha, hspan, hli⟩ := exists_linearIndependent' ℂ cols
  have : Finite κ := LinearIndependent.finite (R := ℂ) (M := Fin d → ℂ) hli
  let : Fintype κ := Fintype.ofFinite κ
  let M : Matrix (Fin d) (Fin k) ℂ := A
  have hfinrank_cols :
      Module.finrank ℂ (Submodule.span ℂ (Set.range cols)) = d := by
    have hA' : LinearIndependent ℂ M.row := hA
    have hr : M.rank = d := by
      simpa [Fintype.card_fin] using (LinearIndependent.rank_matrix (M := M) hA')
    have hcols : cols = M.col := by
      funext j p
      rfl
    rw [hcols, ← rank_eq_finrank_span_cols, hr]
  have hcard : Fintype.card κ = d := by
    have h := (linearIndependent_iff_card_eq_finrank_span (R := ℂ)).mp hli
    rw [Set.finrank] at h
    rw [h, hspan, hfinrank_cols]
  let e : Fin d → Fin k :=
    fun i => a ((Fintype.equivFin κ).symm (Fin.cast hcard.symm i))
  have he : Function.Injective e :=
    ha.comp <| (Fintype.equivFin κ).symm.injective.comp
      (Fin.cast_injective hcard.symm)
  have hli_e : LinearIndependent ℂ (fun i : Fin d => cols (e i)) :=
    hli.comp _ <| (Fintype.equivFin κ).symm.injective.comp
      (Fin.cast_injective hcard.symm)
  refine ⟨e, he, ?_⟩
  let B : Matrix (Fin d) (Fin d) ℂ := Matrix.of fun p q => A p (e q)
  have hcol : LinearIndependent ℂ B.col := by
    have : B.col = fun q : Fin d => cols (e q) := by
      funext q p
      rfl
    simpa [this] using hli_e
  exact (nonsingular_iff_det_ne_zero (R := ℂ)).mp
    (Nonsingular.of_linearIndependent_col hcol)

/-- Linear-equivalence placement lemma used by the transversality reduction:
two subspaces of equal dimension are carried to one another by an ambient
linear automorphism. -/
lemma exists_linearEquiv_map_eq_of_finrank_eq {k : ℕ}
    (W W' : Submodule ℂ (Fin k → ℂ))
    (hrank : Module.finrank ℂ W = Module.finrank ℂ W') :
    ∃ g : (Fin k → ℂ) ≃ₗ[ℂ] (Fin k → ℂ),
      W.map g.toLinearMap = W' := by
  let f : W ≃ₗ[ℂ] W' :=
    Classical.choice (FiniteDimensional.nonempty_linearEquiv_of_finrank_eq hrank)
  obtain ⟨g, hg⟩ := Submodule.exists_linearEquiv_restrict_eq f
  refine ⟨g, Submodule.eq_of_le_of_finrank_eq ?_ ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    have hfx : (f ⟨x, hx⟩ : Fin k → ℂ) ∈ W' := (f ⟨x, hx⟩).property
    simpa [hg ⟨x, hx⟩] using hfx
  · rw [g.finrank_map_eq, hrank]

/-- A valuation of all Gram coordinates by embedded real numbers. -/
def IsRealValuation {k : ℕ} (z : GramVar k → ℂ) : Prop :=
  z ∈ Set.pi Set.univ (fun _ => Set.range ((↑) : ℝ → ℂ))

lemma exists_real_eval_ne_zero {k : ℕ}
    (p : MvPolynomial (GramVar k) ℂ) (hp : p ≠ 0) :
    ∃ z : GramVar k → ℂ, IsRealValuation z ∧ eval z p ≠ 0 := by
  by_contra h
  push_neg at h
  apply hp
  apply funext_set (fun _ : GramVar k => Set.range ((↑) : ℝ → ℂ))
    (fun _ => Set.infinite_range_of_injective Complex.ofReal_injective)
  intro z hz
  simpa [h z hz]

private def realPartOfValuation {k : ℕ} (z : GramVar k → ℂ)
    (hz : IsRealValuation z) (v : GramVar k) : ℝ :=
  Classical.choose (hz v (Set.mem_univ v))

private lemma ofReal_realPartOfValuation {k : ℕ} (z : GramVar k → ℂ)
    (hz : IsRealValuation z) (v : GramVar k) :
    (realPartOfValuation z hz v : ℂ) = z v :=
  Classical.choose_spec (hz v (Set.mem_univ v))

def matrixEntryOfRealValuation {k : ℕ} (z : GramVar k → ℂ)
    (hz : IsRealValuation z) (i j : Fin k) : ℂ :=
    (realPartOfValuation z hz (false, i, j) : ℂ) +
      Complex.I * (realPartOfValuation z hz (true, i, j) : ℂ)

def matrixOfRealValuation {k : ℕ} (z : GramVar k → ℂ)
    (hz : IsRealValuation z) : Matrix (Fin k) (Fin k) ℂ :=
  Matrix.of (matrixEntryOfRealValuation z hz)

/-- Entrywise formula for `LᴴL`, avoiding any dependence on matrix notation. -/
def gramOf {k : ℕ} (L : Matrix (Fin k) (Fin k) ℂ) :
    Matrix (Fin k) (Fin k) ℂ :=
  fun i j => ∑ r : Fin k, star (L r i) * L r j

lemma gramOf_eq_conjTranspose_mul {k : ℕ}
    (L : Matrix (Fin k) (Fin k) ℂ) :
    gramOf L = L.conjTranspose * L := by
  ext i j
  simp [gramOf, Matrix.mul_apply, conjTranspose_apply]

lemma eval_lPoly_realValuation {k : ℕ} (z : GramVar k → ℂ)
    (hz : IsRealValuation z) (i j : Fin k) :
    eval z (lPoly i j) =
      matrixEntryOfRealValuation z hz i j := by
  rw [show eval z (lPoly i j) =
      z (false, i, j) + Complex.I * z (true, i, j) by
    simp [lPoly]]
  rw [← ofReal_realPartOfValuation z hz (false, i, j),
    ← ofReal_realPartOfValuation z hz (true, i, j)]
  rfl

lemma eval_lBarPoly_realValuation {k : ℕ} (z : GramVar k → ℂ)
    (hz : IsRealValuation z) (i j : Fin k) :
    eval z (lBarPoly i j) =
      star (matrixEntryOfRealValuation z hz i j) := by
  rw [show eval z (lBarPoly i j) =
      z (false, i, j) - Complex.I * z (true, i, j) by
    simp [lBarPoly]]
  rw [← ofReal_realPartOfValuation z hz (false, i, j),
    ← ofReal_realPartOfValuation z hz (true, i, j)]
  unfold matrixEntryOfRealValuation
  rw [sub_eq_add_neg]
  change _ = conj
    ((realPartOfValuation z hz (false, i, j) : ℂ) +
      Complex.I * (realPartOfValuation z hz (true, i, j) : ℂ))
  simp

lemma eval_gramEntry_realValuation {k : ℕ} (z : GramVar k → ℂ)
    (hz : IsRealValuation z) (i j : Fin k) :
    eval z (gramEntry (i, j)) =
      ∑ r : Fin k,
        star (matrixEntryOfRealValuation z hz r i) *
          matrixEntryOfRealValuation z hz r j := by
  rw [gramEntry, map_sum]
  apply Finset.sum_congr rfl
  intro r _
  rw [map_mul, eval_lPoly_realValuation, eval_lBarPoly_realValuation]

lemma eval_gramPull_realValuation {k : ℕ} (z : GramVar k → ℂ)
    (hz : IsRealValuation z) (p : MvPolynomial (MatVar k) ℂ) :
    eval z (gramPull p) =
      eval (fun ij =>
        ∑ r : Fin k,
          star (matrixEntryOfRealValuation z hz r ij.1) *
            matrixEntryOfRealValuation z hz r ij.2) p := by
  rw [gramPull]
  change aeval z (bind₁ gramEntry p) = _
  rw [aeval_bind₁]
  apply congrArg (fun f => eval f p)
  funext ij
  exact eval_gramEntry_realValuation z hz ij.1 ij.2

lemma eval_lDetPoly_realValuation {k : ℕ} (z : GramVar k → ℂ)
    (hz : IsRealValuation z) :
    eval z (lDetPoly (k := k)) =
      (matrixOfRealValuation (k := k) z hz).det := by
  unfold lDetPoly
  rw [(eval z).map_det]
  apply congrArg Matrix.det
  ext i j
  simpa [matrixOfRealValuation] using eval_lPoly_realValuation z hz i j

/-- Algebraic positive-Hermitian density: every nonzero polynomial in the
entries of a square complex matrix is nonzero at some positive-definite
Hermitian matrix.

This is the kernel lemma replacing the informal Zariski-density assertion in
s=55.
-/
theorem exists_posDef_eval_ne_zero {k : ℕ}
    (p : MvPolynomial (MatVar k) ℂ) (hp : p ≠ 0) :
    ∃ K : Matrix (Fin k) (Fin k) ℂ,
      K.PosDef ∧ eval (fun ij => K ij.1 ij.2) p ≠ 0 := by
  have hgp : gramPull p ≠ 0 := (gramPull_injective (k := k)).ne hp
  have hprod : gramPull p * lDetPoly (k := k) ≠ 0 :=
    mul_ne_zero hgp lDetPoly_ne_zero
  obtain ⟨z, hz, hzeval⟩ := exists_real_eval_ne_zero
    (gramPull p * lDetPoly (k := k)) hprod
  let L := matrixOfRealValuation z hz
  have hsplit :
      eval z (gramPull p) * eval z (lDetPoly (k := k)) ≠ 0 := by
    simpa [map_mul] using hzeval
  have hgram : eval z (gramPull p) ≠ 0 :=
    fun h => hsplit (by simp [h])
  have hdetEval : eval z (lDetPoly (k := k)) ≠ 0 :=
    fun h => hsplit (by simp [h])
  have hdet : L.det ≠ 0 := by
    rw [eval_lDetPoly_realValuation z hz] at hdetEval
    exact hdetEval
  have hL : IsUnit L :=
    (Matrix.isUnit_iff_isUnit_det L).mpr (isUnit_iff_ne_zero.mpr hdet)
  refine ⟨gramOf L, ?_, ?_⟩
  · rw [gramOf_eq_conjTranspose_mul]
    simpa [star_eq_conjTranspose, Matrix.mul_assoc] using
      (hL.posDef_star_left_conjugate_iff (x := (1 : Matrix (Fin k) (Fin k) ℂ))).2
        Matrix.PosDef.one
  · rw [eval_gramPull_realValuation z hz] at hgram
    simpa [L, gramOf, matrixOfRealValuation] using hgram

/-- Missing local lemma 3: finitely many nonzero matrix polynomials can be
made simultaneously nonzero at one positive-definite Hermitian matrix. -/
theorem exists_posDef_avoiding_finset {k : ℕ}
    (P : Finset (MvPolynomial (MatVar k) ℂ))
    (hP : ∀ p ∈ P, p ≠ 0) :
    ∃ K : Matrix (Fin k) (Fin k) ℂ,
      K.PosDef ∧ ∀ p ∈ P, eval (fun ij => K ij.1 ij.2) p ≠ 0 := by
  classical
  let q : MvPolynomial (MatVar k) ℂ := ∏ p ∈ P, p
  have hq : q ≠ 0 := by
    simp only [q]
    exact Finset.prod_ne_zero_iff.mpr hP
  obtain ⟨K, hK, hKq⟩ := exists_posDef_eval_ne_zero q hq
  refine ⟨K, hK, ?_⟩
  have hprod :
      (∏ p ∈ P, eval (fun ij => K ij.1 ij.2) p) ≠ 0 := by
    simpa [q, map_prod] using hKq
  exact Finset.prod_ne_zero_iff.mp hprod

/-- Finite-family form used by s=55 after choosing one polynomial minor for
each required mixed rank and one polynomial for each same-side pairing. -/
theorem finite_posHermitian_genericity {k : ℕ} {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (p : ι → MvPolynomial (MatVar k) ℂ)
    (hp : ∀ i, p i ≠ 0) :
    ∃ K : Matrix (Fin k) (Fin k) ℂ,
      K.PosDef ∧
        ∀ i, eval (fun ij => K ij.1 ij.2) (p i) ≠ 0 := by
  classical
  let P : Finset (MvPolynomial (MatVar k) ℂ) := Finset.univ.image p
  have hP : ∀ q ∈ P, q ≠ 0 := by
    intro q hq
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hq
    exact hp i
  obtain ⟨K, hK, havoid⟩ := exists_posDef_avoiding_finset P hP
  refine ⟨K, hK, fun i => havoid (p i) ?_⟩
  exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩

theorem proof :
    ∀ (k n : ℕ) (p : Fin n → MvPolynomial (MatVar k) ℂ),
      (∀ i, p i ≠ 0) →
      ∃ K : Matrix (Fin k) (Fin k) ℂ,
        K.PosDef ∧
        ∀ i, eval (fun ij => K ij.1 ij.2) (p i) ≠ 0 := by
  intro k n p hp
  exact finite_posHermitian_genericity p hp

end

end Submissions.FinitePositiveHermitianGenericity.Genericity
