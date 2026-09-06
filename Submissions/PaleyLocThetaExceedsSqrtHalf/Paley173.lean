import Mathlib
import Commons.PaleyLocalizationTheta

/- Exact rational PSD certificate at p = 173 for a known numerical observation.
The search used floating-point LP and square roots only to find coefficients.
All decisive finite arithmetic and the PSD argument below are kernel checked. -/
namespace Submissions.PaleyLocThetaExceedsSqrtHalf.Paley173

open scoped BigOperators
namespace NextDiagonalPSD

lemma pair_bound (a u v : ℝ) :
    0 ≤ |a| * (u ^ 2 + v ^ 2) + 2 * a * u * v := by
  by_cases h : 0 ≤ a
  · rw [abs_of_nonneg h]
    nlinarith [mul_nonneg h (sq_nonneg (u + v))]
  · rw [abs_of_neg (lt_of_not_ge h)]
    nlinarith [mul_nonneg (neg_nonneg.mpr (le_of_not_ge h)) (sq_nonneg (u - v))]

lemma sum_bound {ι : Type*} [Fintype ι] (K : Matrix ι ι ℝ)
    (hK : ∀ i j, K i j = K j i) (x : ι → ℝ) :
    0 ≤ (∑ i, (∑ j, |K i j|) * x i ^ 2) + ∑ i, ∑ j, K i j * x i * x j := by
  have h := Finset.sum_nonneg (s := Finset.univ) (fun i _ =>
    Finset.sum_nonneg (s := Finset.univ) (fun j _ => pair_bound (K i j) (x i) (x j)))
  have swap : (∑ i, ∑ j, |K i j| * x j ^ 2) =
      ∑ i, ∑ j, |K i j| * x i ^ 2 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [hK j i]
  simp_rw [mul_add, Finset.sum_add_distrib] at h
  simp_rw [show ∀ i j, 2 * K i j * x i * x j = 2 * (K i j * x i * x j) by intros; ring,
    ← Finset.mul_sum] at h
  rw [swap] at h
  simp_rw [← Finset.sum_mul] at h
  linarith

theorem diagonal_dominant {ι : Type*} [Fintype ι] [DecidableEq ι]
    (R : Matrix ι ι ℝ) (hR : ∀ i j, R i j = R j i)
    (hd : ∀ i, ∑ j ∈ Finset.univ.erase i, |R i j| ≤ R i i) :
    Matrix.PosSemidef R := by
  let K : Matrix ι ι ℝ := fun i j => if i = j then 0 else R i j
  have hK : ∀ i j, K i j = K j i := by
    intro i j
    simp only [K]
    split_ifs with h h' h'
    · rfl
    · exact False.elim (h' h.symm)
    · exact False.elim (h h'.symm)
    · exact hR i j
  have row (i : ι) : (∑ j, |K i j|) = ∑ j ∈ Finset.univ.erase i, |R i j| := by
    simp only [K, apply_ite abs, abs_zero]
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i)]
    simp only [ite_true, add_zero]
    apply Finset.sum_congr rfl
    intro j hj
    rw [if_neg (Ne.symm (Finset.ne_of_mem_erase hj))]
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · ext i j
    simpa [Matrix.conjTranspose] using hR j i
  · intro x
    have bound := sum_bound K hK x
    have diag : 0 ≤ ∑ i, (R i i - ∑ j, |K i j|) * x i ^ 2 := by
      apply Finset.sum_nonneg
      intro i _
      apply mul_nonneg
      · rw [row]
        exact sub_nonneg.mpr (hd i)
      · exact sq_nonneg _
    have split (i : ι) : (∑ j, R i j * x i * x j) =
        R i i * x i ^ 2 + ∑ j, K i j * x i * x j := by
      rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i)]
      rw [← Finset.sum_erase_add Finset.univ (fun j => K i j * x i * x j) (Finset.mem_univ i)]
      have he : (∑ j ∈ Finset.univ.erase i, R i j * x i * x j) =
          ∑ j ∈ Finset.univ.erase i, K i j * x i * x j := by
        apply Finset.sum_congr rfl
        intro j hj
        simp [K, Ne.symm (Finset.ne_of_mem_erase hj)]
      rw [he]
      simp [K]
      ring
    change 0 ≤ ∑ i, x i * ∑ j, R i j * x j
    simp_rw [Finset.mul_sum]
    simp_rw [show ∀ (i j : ι), x i * (R i j * x j) = R i j * x i * x j by intros; ring]
    simp_rw [split, Finset.sum_add_distrib]
    simp_rw [sub_mul, Finset.sum_sub_distrib] at diag
    linarith

theorem integer_diagonal_dominant {ι : Type*} [Fintype ι] [DecidableEq ι]
    (R : Matrix ι ι ℤ) (hR : ∀ i j, R i j = R j i)
    (hd : ∀ i, ∑ j ∈ Finset.univ.erase i, |R i j| ≤ R i i) :
    Matrix.PosSemidef (fun i j => (R i j : ℝ)) := by
  apply diagonal_dominant
  · intro i j
    exact_mod_cast hR i j
  · intro i
    exact_mod_cast hd i

end NextDiagonalPSD



open scoped BigOperators
namespace NextCirculantRows

theorem row_abs_sum {ι : Type*} [Fintype ι] [DecidableEq ι] [AddGroup ι]
    (r : ι → ℤ) (i : ι) :
    (∑ j ∈ Finset.univ.erase i, |Matrix.circulant r i j|) =
      ∑ j ∈ Finset.univ.erase 0, |r j| := by
  have ht : (∑ j, |Matrix.circulant r i j|) = ∑ j, |r j| := by
    exact Fintype.sum_equiv (Equiv.subLeft i) _ _ (fun j => rfl)
  have hi := Finset.sum_erase_add Finset.univ
    (fun j => |Matrix.circulant r i j|) (Finset.mem_univ i)
  have hz := Finset.sum_erase_add Finset.univ (fun j => |r j|) (Finset.mem_univ 0)
  simp only [Matrix.circulant_apply, sub_self] at hi
  simp only [Matrix.circulant_apply] at ht
  rw [ht] at hi
  simp only [Matrix.circulant_apply]
  linarith

theorem row_dominance {ι : Type*} [Fintype ι] [DecidableEq ι] [AddGroup ι]
    (r : ι → ℤ)
    (h : (∑ j ∈ Finset.univ.erase 0, |r j|) ≤ r 0) :
    ∀ i, (∑ j ∈ Finset.univ.erase i, |Matrix.circulant r i j|) ≤
      Matrix.circulant r i i := by
  intro i
  rw [row_abs_sum]
  simpa only [Matrix.circulant_apply, sub_self] using h

end NextCirculantRows



namespace NextThetaBounds
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]

lemma two_entry_le {M : Matrix V V ℝ} (hM : M.PosSemidef) (i j : V) :
    2 * M i j ≤ M i i + M j j := by
  by_cases hij : i = j
  · subst j; linarith
  have h := hM.2 (Finsupp.single i 1 - Finsupp.single j 1)
  have hs : M j i = M i j := by
    simpa [Matrix.conjTranspose_apply] using congrArg (fun N : Matrix V V ℝ => N i j) hM.1.eq
  simp [Finsupp.sum_sub_index, Finsupp.sum_add_index, sub_mul, mul_sub,
    hij, Ne.symm hij, hs] at h
  linarith

lemma sum_entries_le_card_trace {M : Matrix V V ℝ} (hM : M.PosSemidef) :
    (∑ i, ∑ j, M i j) ≤ (Fintype.card V : ℝ) * M.trace := by
  have h := Finset.sum_le_sum (s := (Finset.univ : Finset V))
    (fun i _ => Finset.sum_le_sum (s := (Finset.univ : Finset V))
      (fun j _ => two_entry_le hM i j))
  simp only [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul] at h
  simp only [Matrix.trace, Matrix.diag_apply]
  linarith

lemma feasible_bddAbove (adj : V → V → Prop) :
    BddAbove (Commons.thetaCliqueFeasible adj) := by
  refine ⟨(Fintype.card V : ℝ), ?_⟩
  rintro s ⟨M, hM, htr, _, rfl⟩
  simpa [htr] using sum_entries_le_card_trace hM

end NextThetaBounds


set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Matrix
abbrev V := Fin 86
def coeff : Array ℤ := #[100000000, 0, 22730233, 0, 0, 9426435, 15651272, 19628782, 0, 0, 2527918, 0, 7544527, 0, 0, 42127082, 32754249, 20428821, 23185974, 5156191, 8082737, 0, 42179520, 0, 13041181, 0, 0, 0, -10734591, 0, 917945, 48368481, 0, 40112376, 0, 0, 0, 35547136, 24848268, 11883927, 0, 0, 0, 0, 0, 0, 0, 11883927, 24848268, 35547136, 0, 0, 0, 40112376, 0, 48368481, 917945, 0, -10734591, 0, 0, 0, 13041181, 0, 42179520, 0, 8082737, 5156191, 23185974, 20428821, 32754249, 42127082, 0, 0, 7544527, 0, 2527918, 0, 0, 19628782, 15651272, 9426435, 0, 0, 22730233, 0]
def gramCoeffs : Array ℤ := #[65142112, -4684975, 9427499, 1870385, -4865219, 4440345, 8799440, 10089784, -917649, -5380264, 822045, -3598606, 3717360, -976109, -3771023, 20564970, 12052700, 9028306, 10490776, 3146124, 2926807, -851645, 21088062, -1161283, 4513245, -2248855, -2322146, -2954972, -5907336, -2898604, -927232, 20954517, -6326230, 13968675, -3461408, -3731329, -1362378, 15587128, 10169028, 4113942, -9222243, 1793768, -664932, -2718319, -664932, 1793768, -9222243, 4113942, 10169028, 15587128, -1362378, -3731329, -3461408, 13968675, -6326230, 20954517, -927232, -2898604, -5907336, -2954972, -2322146, -2248855, 4513245, -1161283, 21088062, -851645, 2926807, 3146124, 10490776, 9028306, 12052700, 20564970, -3771023, -976109, 3717360, -3598606, 822045, -5380264, -917649, 10089784, 8799440, 4440345, -4865219, 1870385, 9427499, -4684975]
def fv (i : V) : ℤ := 100000000 * coeff[i.val]!
def bv (i : V) : ℤ := gramCoeffs[i.val]!
def F : Matrix V V ℤ := Matrix.circulant fv
def B : Matrix V V ℤ := Matrix.circulant bv
def R : Matrix V V ℤ := F - B * B.transpose
def rv : V → ℤ := fv - Matrix.circulant bv *ᵥ (fun i => bv (-i))
theorem r_circ : R = Matrix.circulant rv := by
  unfold R F B rv
  rw [Matrix.transpose_circulant, Matrix.circulant_mul, Matrix.circulant_sub]
theorem coeff_symm : ∀ i j : V, F i j = F j i := by
  change ∀ i j : V, fv (i - j) = fv (j - i)
  decide +kernel
theorem coeff_diag : ∀ i : V, F i i = 10000000000000000 := by
  intro i
  simp [F, Matrix.circulant_apply, fv, coeff]
theorem residual_dd_zero : (∑ j ∈ Finset.univ.erase (0 : V), |rv j|) ≤ rv 0 := by
  decide +kernel
def vertexData : Array Nat := #[1, 4, 16, 64, 83, 159, 117, 122, 142, 49, 23, 92, 22, 88, 6, 24, 96, 38, 152, 89, 10, 40, 160, 121, 138, 33, 132, 9, 36, 144, 57, 55, 47, 15, 60, 67, 95, 34, 136, 25, 100, 54, 43, 172, 169, 157, 109, 90, 14, 56, 51, 31, 124, 150, 81, 151, 85, 167, 149, 77, 135, 21, 84, 163, 133, 13, 52, 35, 140, 41, 164, 137, 29, 116, 118, 126, 158, 113, 106, 78, 139, 37, 148, 73, 119, 130]
def rootData : Array Nat := #[0, 1, 0, 0, 2, 0, 51, 0, 0, 3, 23, 0, 0, 79, 35, 19, 4, 0, 0, 0, 0, 59, 56, 14, 71, 5, 0, 0, 0, 78, 0, 66, 0, 44, 42, 30, 6, 27, 62, 0, 46, 53, 0, 40, 0, 0, 0, 77, 0, 7, 0, 33, 15, 0, 20, 48, 70, 24, 0, 0, 38, 0, 0, 0, 8, 0, 0, 76, 0, 0, 0, 0, 0, 65, 0, 0, 0, 58, 50, 0, 0, 9, 0, 16, 55, 36, 0, 0, 61, 75, 69, 0, 28, 0, 0, 21, 31, 0, 0, 0, 10, 0, 0, 0, 0, 0, 25, 0, 0, 52, 0, 0, 0, 74, 0, 0, 17, 64, 34, 43, 0, 11, 45, 0, 41, 0, 68, 0, 0, 0, 86, 0, 85, 47, 0, 57, 84, 39, 22, 73, 60, 0, 83, 0, 12, 0, 0, 0, 54, 29, 82, 18, 49, 0, 0, 0, 0, 26, 37, 32, 81, 0, 0, 63, 67, 0, 0, 72, 0, 13, 0, 0, 80]
def vertex (i : V) : ZMod 173 := (vertexData[i.val]! : Nat)
theorem vertex_sq : ∀ i : V, Commons.IsNonzeroSq (vertex i) := by decide +kernel
theorem vertex_inj : Function.Injective vertex := by decide +kernel
theorem vertex_surj : ∀ x : ZMod 173, Commons.IsNonzeroSq x → ∃ i : V, vertex i = x := by
  decide +kernel
theorem support_data : ∀ i j : V, i = j ∨ F i j = 0 ∨
    (vertex i - vertex j ≠ 0 ∧ vertex i - vertex j =
      (rootData[(vertex i - vertex j).val]! : ZMod 173) *
      (rootData[(vertex i - vertex j).val]! : ZMod 173)) := by
  simp only [F, Matrix.circulant_apply]
  decide +kernel
theorem support : ∀ i j : V, i = j ∨ F i j = 0 ∨
    Commons.IsNonzeroSq (vertex i - vertex j) := by
  intro i j
  rcases support_data i j with h | h | ⟨hn, hs⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr ⟨hn, _, hs⟩)
theorem rowsum : ∀ i : V, ∑ j : V, F i j = 93081692800000000 := by decide +kernel




def FR : Matrix V V ℝ := fun i j => (F i j : ℝ)
def BR : Matrix V V ℝ := fun i j => (B i j : ℝ)
def RR : Matrix V V ℝ := fun i j => (R i j : ℝ)

lemma rr_identity : RR = FR - BR * BR.transpose := by
  ext i j
  simp [RR, FR, BR, R, Matrix.mul_apply, Matrix.transpose_apply]

lemma rr_symm : ∀ i j, RR i j = RR j i := by
  intro i j
  simp only [RR, R, Matrix.sub_apply, Matrix.mul_apply, Matrix.transpose_apply, coeff_symm i j]
  congr 2
  exact Finset.sum_congr rfl fun k _ => mul_comm _ _

lemma rr_dd (hdd : ∀ i : V, (∑ j ∈ Finset.univ.erase i, |R i j|) ≤ R i i) :
    ∀ i, ∑ j ∈ Finset.univ.erase i, |RR i j| ≤ RR i i := by
  intro i
  simp only [RR]
  exact_mod_cast hdd i

lemma F_psd : FR.PosSemidef := by
  have hd : ∀ i : V, ∑ j ∈ Finset.univ.erase i, |R i j| ≤ R i i := by
    simpa only [r_circ] using NextCirculantRows.row_dominance rv residual_dd_zero
  have hp : RR.PosSemidef := NextDiagonalPSD.diagonal_dominant RR rr_symm (rr_dd hd)
  have hg : (BR * BR.transpose).PosSemidef := by
    simpa using Matrix.posSemidef_self_mul_conjTranspose BR
  have he : RR + BR * BR.transpose = FR := by
    rw [rr_identity]
    exact sub_add_cancel _ _
  rw [← he]
  exact hp.add hg

noncomputable def vertEquiv : V ≃ Commons.PaleyLocV 173 :=
  Equiv.ofBijective (fun i => ⟨vertex i, vertex_sq i⟩) ⟨
    fun i j h => vertex_inj (congrArg Subtype.val h),
    fun x => by
      obtain ⟨i, hi⟩ := vertex_surj x.val x.property
      exact ⟨i, Subtype.ext hi⟩⟩

lemma vertEquiv_val (i : V) : (vertEquiv i).val = vertex i := rfl

lemma vertex_inv (x : Commons.PaleyLocV 173) : vertex (vertEquiv.symm x) = x.val := by
  exact congrArg Subtype.val (vertEquiv.apply_symm_apply x)

lemma paley_card : Fintype.card (Commons.PaleyLocV 173) = 86 := by
  rw [← Fintype.card_congr vertEquiv]
  rfl

noncomputable def X : Matrix (Commons.PaleyLocV 173) (Commons.PaleyLocV 173) ℝ :=
  fun u v => (1 / 860000000000000000 : ℝ) * FR (vertEquiv.symm u) (vertEquiv.symm v)

lemma X_psd (hF : FR.PosSemidef) : X.PosSemidef := by
  exact (hF.submatrix vertEquiv.symm).smul (by norm_num : (0 : ℝ) ≤ 1 / 860000000000000000)

lemma X_trace : X.trace = 1 := by
  simp [Matrix.trace, Matrix.diag_apply, X, FR, coeff_diag, paley_card]
  norm_num

lemma X_support : ∀ u v : Commons.PaleyLocV 173, u ≠ v →
    ¬ Commons.paleyLocAdj 173 u v → X u v = 0 := by
  intro u v hne hnot
  rcases support (vertEquiv.symm u) (vertEquiv.symm v) with h | h | h
  · exact False.elim (hne (vertEquiv.symm.injective h))
  · simp [X, FR, h]
  · exact False.elim (hnot (by simpa [Commons.paleyLocAdj, vertex_inv] using h))

lemma X_sum : (∑ u, ∑ v, X u v) = (930816928 : ℝ) / 100000000 := by
  have hrow : ∀ u : Commons.PaleyLocV 173,
      (∑ v, X u v) = (930816928 : ℝ) / 8600000000 := by
    intro u
    simp only [X, ← Finset.mul_sum]
    rw [vertEquiv.symm.sum_comp (fun j => FR (vertEquiv.symm u) j)]
    have hs : (∑ j : V, FR (vertEquiv.symm u) j) = 93081692800000000 := by
      simp only [FR]
      exact_mod_cast rowsum (vertEquiv.symm u)
    rw [hs]
    norm_num
  simp only [hrow, Finset.sum_const, Finset.card_univ, paley_card, nsmul_eq_mul]
  norm_num

lemma sqrt_lt_objective : Real.sqrt ((173 : ℝ) / 2) < (930816928 : ℝ) / 100000000 := by
  apply (Real.sqrt_lt' (by norm_num)).2
  norm_num

theorem proof : ∃ p : ℕ, ∃ hp : Nat.Prime p, p % 4 = 1 ∧
    Real.sqrt ((p : ℝ) / 2) < Commons.paleyLocTheta p hp.pos := by
  refine ⟨173, by norm_num, by norm_num, ?_⟩
  change Real.sqrt ((173 : ℝ) / 2) < Commons.thetaClique (Commons.paleyLocAdj 173)
  apply lt_of_lt_of_le sqrt_lt_objective
  exact le_csSup (NextThetaBounds.feasible_bddAbove _) ⟨X, X_psd F_psd,
    X_trace, X_support, X_sum.symm⟩


end Submissions.PaleyLocThetaExceedsSqrtHalf.Paley173

