import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Topology.Algebra.Star.Real
import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.Convex.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.LocallyConvex.WithSeminorms
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.Ring
import Mathlib.LinearAlgebra.Matrix.Basis
import Commons.PaleyLocalizationTheta
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic

namespace Submissions.PaleyLocThetaProduct.Separation

open Matrix

variable {V : Type*} [Fintype V]

theorem psd_trace_one_entry_abs_le_one {X : Matrix V V ℝ}
    (hX : X.PosSemidef) (htr : X.trace = 1) (i j : V) : |X i j| ≤ 1 := by
  classical
  have hd (k : V) : X k k ≤ 1 := by
    calc
      X k k ≤ ∑ a, X a a :=
        Finset.single_le_sum (f := fun a => X a a)
          (fun a _ => hX.diag_nonneg) (Finset.mem_univ k)
      _ = 1 := htr
  have hsym : X j i = X i j := by simpa using hX.isHermitian.apply i j
  have hp := hX.2 (Finsupp.single i (1 : ℝ) + Finsupp.single j 1)
  have hm := hX.2 (Finsupp.single i (1 : ℝ) + Finsupp.single j (-1))
  simp [Finsupp.sum_add_index, mul_add, add_mul, hsym, -Finsupp.single_neg] at hp hm
  exact abs_le.mpr ⟨by linarith [hd i, hd j], by linarith [hd i, hd j]⟩

theorem isClosed_psd : IsClosed {X : Matrix V V ℝ | X.PosSemidef} := by
  simp only [Matrix.posSemidef_iff_dotProduct_mulVec, Set.ofPred_and, Set.ofPred_forall]
  refine (isClosed_eq continuous_id.matrix_conjTranspose continuous_id).inter ?_
  exact isClosed_iInter fun x =>
    isClosed_le continuous_const
      (continuous_const.dotProduct (continuous_id.matrix_mulVec continuous_const))

theorem isClosed_psd_trace_one :
    IsClosed {X : Matrix V V ℝ | X.PosSemidef ∧ X.trace = 1} :=
  isClosed_psd.inter (isClosed_eq continuous_id.matrix_trace continuous_const)

theorem isCompact_psd_trace_one :
    IsCompact {X : Matrix V V ℝ | X.PosSemidef ∧ X.trace = 1} := by
  refine (isCompact_Icc.matrix :
      IsCompact ((Set.Icc (-1 : ℝ) 1).matrix : Set (Matrix V V ℝ))).of_isClosed_subset
    isClosed_psd_trace_one ?_
  intro X hX i j
  exact abs_le.mp (psd_trace_one_entry_abs_le_one hX.1 hX.2 i j)

theorem convex_psd_trace_one :
    Convex ℝ {X : Matrix V V ℝ | X.PosSemidef ∧ X.trace = 1} := by
  intro X hX Y hY a b ha hb hab
  refine ⟨(hX.1.smul ha).add (hY.1.smul hb), ?_⟩
  simpa [Matrix.trace_add, Matrix.trace_smul, hX.2, hY.2] using hab

theorem nonempty_psd_trace_one [Nonempty V] :
    Set.Nonempty {X : Matrix V V ℝ | X.PosSemidef ∧ X.trace = 1} := by
  classical
  let v : V := Classical.arbitrary V
  refine ⟨Matrix.diagonal (Pi.single v (1 : ℝ)), ?_, ?_⟩
  · apply Matrix.PosSemidef.diagonal
    intro i
    simp only [Pi.single_apply]
    split_ifs <;> norm_num
  · simp

end Submissions.PaleyLocThetaProduct.Separation

namespace Submissions.PaleyLocThetaProduct

/-- A point above a compact convex density image has a strict separator with positive
vertical coefficient.  This is the only separation step needed for approximate theta duality. -/
theorem separate_density_image {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {K : Set (E × ℝ)} {t : ℝ}
    (hKcompact : IsCompact K) (hKconv : Convex ℝ K)
    (hone : ((0 : E), (1 : ℝ)) ∈ K) (ht : 1 < t)
    (htK : ((0 : E), t) ∉ K) :
    ∃ f : (E × ℝ) →L[ℝ] ℝ, 0 < f (0, 1) ∧
      ∀ x ∈ K, f x < f (0, 1) * t := by
  obtain ⟨f, u, hfK, hfu⟩ :=
    geometric_hahn_banach_closed_point hKconv hKcompact.isClosed htK
  have hscale : f ((0 : E), t) = f (0, 1) * t := by
    have hpair : ((0 : E), t) = t • ((0 : E), (1 : ℝ)) := by simp
    rw [hpair, map_smul]
    simp [mul_comm]
  have hstrict : f (0, 1) < f (0, 1) * t :=
    (hfK _ hone).trans (hfu.trans_eq hscale)
  have hpos : 0 < f (0, 1) := by
    by_contra h
    have hnonpos : f (0, 1) ≤ 0 := le_of_not_gt h
    have hmul := mul_nonpos_of_nonpos_of_nonneg hnonpos (sub_nonneg.mpr ht.le)
    nlinarith
  exact ⟨f, hpos, fun x hx => (hfK x hx).trans (hfu.trans_eq hscale)⟩

end Submissions.PaleyLocThetaProduct

namespace Submissions.PaleyLocThetaProduct.Separation

open Matrix

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem linearMap_eq_sum_single (g : Matrix V V ℝ →ₗ[ℝ] ℝ) (X : Matrix V V ℝ) :
    g X = ∑ i, ∑ j, X i j * g (Matrix.single i j 1) := by
  calc
    g X = ∑ i, ∑ j, g (Matrix.single i j (X i j)) := by
      conv_lhs => rw [Matrix.matrix_eq_sum_single X]
      simp only [map_sum]
    _ = ∑ i, ∑ j, X i j * g (Matrix.single i j 1) := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      have h : Matrix.single i j (X i j) = (X i j) • Matrix.single i j (1 : ℝ) := by
        simp
      rw [h, map_smul]
      rfl

/-- Convert a separating linear functional on the forbidden coordinates into an upper
certificate. Symmetrizing its coefficients preserves its value on density matrices. -/
theorem exists_upper_certificate
    (adj : V → V → Prop) (hsymm : Symmetric adj)
    (g : Matrix V V ℝ →ₗ[ℝ] ℝ) (μ t : ℝ) (hμ : 0 < μ)
    (hzero : ∀ i j, i = j ∨ adj i j → g (Matrix.single i j 1) = 0)
    (hbound : ∀ X : Matrix V V ℝ, X.PosSemidef → X.trace = 1 →
      (∑ i, ∑ j, X i j) + g X / μ < t) :
    ∃ A : Matrix V V ℝ, A.IsHermitian ∧
      (∀ i, A i i = 1) ∧ (∀ i j, adj i j → A i j = 1) ∧
      (t • (1 : Matrix V V ℝ) - A).PosSemidef := by
  let C : Matrix V V ℝ := fun i j => g (Matrix.single i j 1)
  let A : Matrix V V ℝ := fun i j => 1 + (C i j + C j i) / (2 * μ)
  have hA : A.IsHermitian := by
    apply Matrix.IsHermitian.ext
    intro i j
    simp only [A, star_trivial]
    ring
  have hdiag : ∀ i, A i i = 1 := by
    intro i
    simp [A, C, hzero i i (Or.inl rfl)]
  have hedge : ∀ i j, adj i j → A i j = 1 := by
    intro i j hij
    simp [A, C, hzero i j (Or.inr hij), hzero j i (Or.inr (hsymm hij))]
  have hpair : ∀ X : Matrix V V ℝ, X.IsHermitian →
      (∑ i, ∑ j, A i j * X i j) = (∑ i, ∑ j, X i j) + g X / μ := by
    intro X hX
    have hXsym : ∀ i j, X j i = X i j := by
      intro i j
      simpa only [star_trivial] using hX.apply i j
    have hc : (∑ i, ∑ j, C i j * X i j) = g X := by
      rw [linearMap_eq_sum_single g X]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      exact mul_comm _ _
    have hct : (∑ i, ∑ j, C j i * X i j) = g X := by
      rw [Finset.sum_comm]
      convert hc using 1
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      rw [hXsym]
    calc
      (∑ i, ∑ j, A i j * X i j) =
          ∑ i, ∑ j, (X i j + (C i j * X i j + C j i * X i j) / (2 * μ)) := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        dsimp only [A]
        ring
      _ = (∑ i, ∑ j, X i j) +
          ((∑ i, ∑ j, C i j * X i j) + (∑ i, ∑ j, C j i * X i j)) / (2 * μ) := by
        simp only [Finset.sum_add_distrib, ← Finset.sum_div]
      _ = (∑ i, ∑ j, X i j) + g X / μ := by
        rw [hc, hct]
        ring
  refine ⟨A, hA, hdiag, hedge, ?_⟩
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    ((Matrix.isHermitian_one.smul (show IsSelfAdjoint t from by
      simp only [isSelfAdjoint_iff, star_trivial])).sub hA)
  intro x
  by_cases hx : x = 0
  · simp [hx]
  let q : ℝ := x ⬝ᵥ x
  have hq : 0 < q := by
    simpa only [q, star_trivial] using (Matrix.dotProduct_star_self_pos_iff.mpr hx)
  let X : Matrix V V ℝ := q⁻¹ • Matrix.vecMulVec x x
  have hX : X.PosSemidef := by
    simpa only [X, star_trivial] using
      (Matrix.posSemidef_vecMulVec_self_star x).smul (inv_nonneg.mpr hq.le)
  have htrace : X.trace = 1 := by
    simp [X, Matrix.trace_smul, Matrix.trace_vecMulVec, q, hq.ne']
  have hlt : (∑ i, ∑ j, A i j * X i j) < t := by
    rw [hpair X hX.isHermitian]
    exact hbound X hX htrace
  have hscale : (∑ i, ∑ j, A i j * X i j) = (x ⬝ᵥ (A *ᵥ x)) / q := by
    simp only [X, Matrix.smul_apply, smul_eq_mul, Matrix.vecMulVec_apply,
      dotProduct, mulVec, Finset.mul_sum, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hscale] at hlt
  have hquadratic := (div_lt_iff₀ hq).mp hlt
  simp only [star_trivial, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
    dotProduct_sub, dotProduct_smul, smul_eq_mul]
  change 0 ≤ t * q - x ⬝ᵥ (A *ᵥ x)
  linarith

end Submissions.PaleyLocThetaProduct.Separation

/- This file will be concatenated with CompactPSD, Separation and DualExtraction
for compilation. No admitted theorem is imported. -/
namespace Submissions.PaleyLocThetaProduct.Separation

open Matrix Commons
variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def objective : Matrix V V ℝ →ₗ[ℝ] ℝ where
  toFun X := ∑ i, ∑ j, X i j
  map_add' X Y := by simp [Finset.sum_add_distrib]
  map_smul' a X := by simp [Finset.mul_sum]

noncomputable def offMask (adj : V → V → Prop) : Matrix V V ℝ →ₗ[ℝ] Matrix V V ℝ := by
  classical
  exact {
    toFun := fun X => Matrix.of (fun i j => if i ≠ j ∧ ¬ adj i j then X i j else 0)
    map_add' := by
      intro X Y
      ext i j
      change (if i ≠ j ∧ ¬ adj i j then X i j + Y i j else 0) =
        (if i ≠ j ∧ ¬ adj i j then X i j else 0) +
        (if i ≠ j ∧ ¬ adj i j then Y i j else 0)
      split_ifs <;> simp
    map_smul' := by
      intro a X
      ext i j
      change (if i ≠ j ∧ ¬ adj i j then a * X i j else 0) =
        a * (if i ≠ j ∧ ¬ adj i j then X i j else 0)
      split_ifs <;> simp }

lemma offMask_apply (adj : V → V → Prop) [DecidableRel adj] (X : Matrix V V ℝ) (i j : V) :
    offMask adj X i j = if i ≠ j ∧ ¬ adj i j then X i j else 0 := by
  classical
  by_cases h : i ≠ j ∧ ¬ adj i j <;> simp [offMask, h]

lemma feasible_bddAbove (adj : V → V → Prop) : BddAbove (thetaCliqueFeasible adj) := by
  refine ⟨(Fintype.card V : ℝ) ^ 2, ?_⟩
  rintro s ⟨X, hX, htr, hz, rfl⟩
  calc
    (∑ i, ∑ j, X i j) ≤ ∑ _i : V, ∑ _j : V, (1 : ℝ) := by
      gcongr with i _ j _
      exact (le_abs_self _).trans (psd_trace_one_entry_abs_le_one hX htr i j)
    _ = (Fintype.card V : ℝ) ^ 2 := by simp; ring

lemma one_feasible [Nonempty V] (adj : V → V → Prop) :
    (1 : ℝ) ∈ thetaCliqueFeasible adj := by
  classical
  let n : ℝ := Fintype.card V
  have hn : n ≠ 0 := by dsimp [n]; exact_mod_cast Fintype.card_ne_zero
  refine ⟨n⁻¹ • (1 : Matrix V V ℝ), Matrix.PosSemidef.one.smul (by positivity), ?_, ?_, ?_⟩
  · simp [Matrix.trace_smul, Matrix.trace_one, n]
  · intro u v huv _
    simp [Matrix.smul_apply, Matrix.one_apply, huv]
  · simp [Matrix.smul_apply, Matrix.one_apply]
    exact (mul_inv_cancel₀ hn).symm

lemma theta_ge_one [Nonempty V] (adj : V → V → Prop) : 1 ≤ thetaClique adj :=
  le_csSup (feasible_bddAbove adj) (one_feasible adj)

/-- Arbitrarily close upper certificates exist. This is the required strong-duality
statement; it asserts no asymptotic estimate for their size. -/
theorem theta_approx_certificate [Nonempty V] (adj : V → V → Prop)
    (hsymm : Symmetric adj) {t : ℝ} (ht : thetaClique adj < t) :
    ∃ A : Matrix V V ℝ,
      A.IsHermitian ∧ (∀ i, A i i = 1) ∧ (∀ i j, adj i j → A i j = 1) ∧
      (t • (1 : Matrix V V ℝ) - A).PosSemidef := by
  classical
  letI : NormedAddCommGroup (Matrix V V ℝ) :=
    inferInstanceAs (NormedAddCommGroup (V → V → ℝ))
  letI : NormedSpace ℝ (Matrix V V ℝ) :=
    inferInstanceAs (NormedSpace ℝ (V → V → ℝ))
  let D : Set (Matrix V V ℝ) := {X | X.PosSemidef ∧ X.trace = 1}
  let L := ((offMask adj).prod (objective (V := V))).toContinuousLinearMap
  have hL (X : Matrix V V ℝ) : L X = (offMask adj X, ∑ i, ∑ j, X i j) := rfl
  let K := L '' D
  have hc : IsCompact K := isCompact_psd_trace_one.image L.continuous
  have hv : Convex ℝ K := convex_psd_trace_one.linear_image L.toLinearMap
  have hone : ((0 : Matrix V V ℝ), (1 : ℝ)) ∈ K := by
    let n : ℝ := Fintype.card V
    have hn : n ≠ 0 := by dsimp [n]; exact_mod_cast Fintype.card_ne_zero
    refine ⟨n⁻¹ • (1 : Matrix V V ℝ), ?_, ?_⟩
    · refine ⟨Matrix.PosSemidef.one.smul (by positivity), ?_⟩
      simp [Matrix.trace_smul, Matrix.trace_one, n]
    · rw [hL]
      apply Prod.ext
      · ext i j
        change offMask adj (n⁻¹ • (1 : Matrix V V ℝ)) i j = 0
        rw [offMask_apply]
        split_ifs with h
        · simp [Matrix.smul_apply, Matrix.one_apply, h.1]
        · rfl
      · change (∑ i, ∑ j, (n⁻¹ • (1 : Matrix V V ℝ)) i j) = 1
        simp [Matrix.smul_apply, Matrix.one_apply]
        simpa [n, mul_comm] using (inv_mul_cancel₀ hn)
  have hout : ((0 : Matrix V V ℝ), t) ∉ K := by
    rintro ⟨X, ⟨hX, htr⟩, hLX⟩
    rw [hL] at hLX
    have hzero : ∀ i j, i ≠ j → ¬ adj i j → X i j = 0 := by
      intro i j hij hadj
      have h := congrFun (congrFun (congrArg Prod.fst hLX) i) j
      simpa [offMask_apply, hij, hadj] using h
    have htX : (∑ i, ∑ j, X i j) = t := congrArg Prod.snd hLX
    have hf : t ∈ thetaCliqueFeasible adj := ⟨X, hX, htr, hzero, htX.symm⟩
    exact (not_le_of_gt ht) (le_csSup (feasible_bddAbove adj) hf)
  obtain ⟨f, hμ, hsep⟩ :=
    Submissions.PaleyLocThetaProduct.separate_density_image
      (E := Matrix V V ℝ) (K := K) (t := t) hc hv hone
      ((theta_ge_one adj).trans_lt ht) hout
  let g : Matrix V V ℝ →ₗ[ℝ] ℝ :=
    f.toLinearMap.comp ((offMask adj).prod (0 : Matrix V V ℝ →ₗ[ℝ] ℝ))
  have hg (X : Matrix V V ℝ) : g X = f (offMask adj X, 0) := rfl
  refine exists_upper_certificate adj hsymm g (f (0, 1)) t hμ ?_ ?_
  · intro i j hij
    have hmask : offMask adj (Matrix.single i j (1 : ℝ)) = 0 := by
      ext a b
      simp only [offMask_apply, Matrix.single_apply, Matrix.zero_apply]
      split_ifs with hab hmatch
      · rcases hmatch with ⟨rfl, rfl⟩
        rcases hij with h | h
        · exact (hab.1 h).elim
        · exact (hab.2 h).elim
      · rfl
      · rfl
    rw [hg, hmask]
    exact map_zero f
  · intro X hX htr
    have h := hsep (L X) ⟨X, ⟨hX, htr⟩, rfl⟩
    have hsplit : f (L X) = g X + f (0, 1) * (∑ i, ∑ j, X i j) := by
      have he : L X = ((offMask adj X), 0) + (∑ i, ∑ j, X i j) • (0, 1) := by
        rw [hL]
        ext <;> simp
      rw [he, map_add, map_smul]
      rw [hg]
      change f (offMask adj X, 0) + (∑ i, ∑ j, X i j) * f (0, 1) =
        f (offMask adj X, 0) + f (0, 1) * (∑ i, ∑ j, X i j)
      ring
    rw [hsplit] at h
    have he : (∑ i, ∑ j, X i j) + g X / f (0, 1) =
        (g X + f (0, 1) * (∑ i, ∑ j, X i j)) / f (0, 1) := by
      field_simp [ne_of_gt hμ]
      <;> ring
    rw [he]
    exact (div_lt_iff₀ hμ).mpr (by simpa [mul_comm] using h)

end Submissions.PaleyLocThetaProduct.Separation

/- Product identity infrastructure. Weak-duality helpers adapted from
woshuajolk's artifact 5976674d-1f8c-45d6-8435-e90279139d3e (Jig #7, statement 9).
The full Paley asymptotic is not asserted here. -/
namespace Submissions.PaleyLocThetaProduct.Separation

open Matrix Commons

variable {V : Type*} [Fintype V] [DecidableEq V]

abbrev ones : Matrix V V ℝ := fun _ _ => 1

lemma symmetric_of_psd {X : Matrix V V ℝ} (hX : X.PosSemidef) (u v : V) :
    X u v = X v u := by
  have h := congrFun (congrFun hX.isHermitian u) v
  simpa [Matrix.conjTranspose_apply] using h.symm

lemma centered_psd [Nonempty V] {X : Matrix V V ℝ} (hX : X.PosSemidef)
    {r : ℝ} (hrow : ∀ u, ∑ v, X u v = r) :
    (X - (r / Fintype.card V) • ones).PosSemidef := by
  classical
  let n : ℝ := Fintype.card V
  have hn : n ≠ 0 := by dsimp [n]; exact_mod_cast Fintype.card_ne_zero
  have hcol : ∀ v, ∑ u, X u v = r := by
    intro v
    simp_rw [symmetric_of_psd hX _ v]
    exact hrow v
  have hXJ : X * ones = r • ones := by
    ext u v
    simpa [Matrix.mul_apply, ones] using hrow u
  have hJX : ones * X = r • ones := by
    ext u v
    simpa [Matrix.mul_apply, ones] using hcol v
  have hJJ : (ones : Matrix V V ℝ) * ones = n • ones := by
    ext u v
    simp [Matrix.mul_apply, ones, n]
  let P : Matrix V V ℝ := 1 - n⁻¹ • ones
  have hP : Pᴴ = P := by ext u v; simp [P, ones, Matrix.conjTranspose_apply, Matrix.one_apply, eq_comm]
  have heq : Pᴴ * X * P = X - (r / n) • ones := by
    rw [hP]
    dsimp [P]
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one,
      smul_mul_assoc, mul_smul_comm, hXJ, hJX, hJJ, smul_smul]
    ext u v
    simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, ones]
    field_simp
    <;> ring
  rw [← heq]
  exact hX.conjTranspose_mul_mul_same P

lemma uniform_to_complement_certificate [Nonempty V] {adj : V → V → Prop}
    {X : Matrix V V ℝ} {s : ℝ} (hs : 0 < s) (hX : X.PosSemidef)
    (hd : ∀ u, X u u = (Fintype.card V : ℝ)⁻¹)
    (hrow : ∀ u, ∑ v, X u v = s / Fintype.card V)
    (hz : ∀ u v, u ≠ v → ¬ adj u v → X u v = 0) :
    ∃ B : Matrix V V ℝ,
      (∀ u, B u u = 1) ∧
      (∀ u v, u ≠ v → ¬ adj u v → B u v = 1) ∧
      (((Fintype.card V : ℝ) / s) • (1 : Matrix V V ℝ) - B).PosSemidef := by
  classical
  let n : ℝ := Fintype.card V
  have hn : n ≠ 0 := by dsimp [n]; exact_mod_cast Fintype.card_ne_zero
  refine ⟨ones - (n ^ 2 / s) • X + (n / s) • 1, ?_, ?_, ?_⟩
  · intro u
    simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
      ones, hd, Matrix.one_apply_eq]
    change 1 - n ^ 2 / s * n⁻¹ + n / s * 1 = 1
    field_simp
    <;> ring
  · intro u v huv hadj
    simp [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply,
      ones, hz u v huv hadj, huv]
  · have hc := (centered_psd hX hrow).smul (show 0 ≤ n ^ 2 / s by positivity)
    convert hc using 1
    ext u v
    simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
    dsimp [ones]
    change n / s * (1 : Matrix V V ℝ) u v -
      (1 - n ^ 2 / s * X u v + n / s * (1 : Matrix V V ℝ) u v) =
      n ^ 2 / s * (X u v - (s / n / n) * 1)
    field_simp
    <;> ring

end Submissions.PaleyLocThetaProduct.Separation

namespace Submissions.PaleyLocThetaProduct.Separation

open Matrix Commons

/-- The Frobenius pairing of two positive semidefinite real matrices is nonnegative. -/
theorem trace_mul_nonneg {V : Type*} [Fintype V] [DecidableEq V]
    {M X : Matrix V V ℝ} (hM : M.PosSemidef) (hX : X.PosSemidef) :
    0 ≤ (M * X).trace := by
  classical
  have hH : M.IsHermitian := hM.isHermitian
  set U : Matrix V V ℝ := (Matrix.IsHermitian.eigenvectorUnitary hH : Matrix V V ℝ) with hU
  set D : Matrix V V ℝ := Matrix.diagonal (RCLike.ofReal ∘ Matrix.IsHermitian.eigenvalues hH)
    with hD
  have hMe : M = U * D * star U := by
    conv_lhs => rw [Matrix.IsHermitian.spectral_theorem hH]
    rw [Unitary.conjStarAlgAut_apply]
  have hY : ((star U) * X * U).PosSemidef := by
    have h := Matrix.PosSemidef.conjTranspose_mul_mul_same hX U
    rwa [← Matrix.star_eq_conjTranspose] at h
  have htr : (M * X).trace = (D * ((star U) * X * U)).trace := by
    rw [hMe, Matrix.trace_mul_comm]
    have e1 : X * (U * D * star U) = (X * U * D) * star U := by simp [Matrix.mul_assoc]
    rw [e1, Matrix.trace_mul_comm]
    have e2 : star U * (X * U * D) = (star U * X * U) * D := by simp [Matrix.mul_assoc]
    rw [e2, Matrix.trace_mul_comm]
  rw [htr]
  have hdiag : (D * ((star U) * X * U)).trace
      = ∑ i, Matrix.IsHermitian.eigenvalues hH i * ((star U) * X * U) i i := by
    simp [Matrix.trace, Matrix.mul_apply, hD, Matrix.diagonal_apply, Finset.sum_ite_eq]
  rw [hdiag]
  refine Finset.sum_nonneg fun i _ => mul_nonneg ?_ (Matrix.PosSemidef.diag_nonneg hY)
  exact Matrix.PosSemidef.eigenvalues_nonneg hM i

section
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Weak duality: an upper certificate bounds every feasible value. -/
theorem feasible_le {adj : V → V → Prop} {A : Matrix V V ℝ} {t : ℝ}
    (hd : ∀ u, A u u = 1) (he : ∀ u v, adj u v → A u v = 1)
    (hpsd : (t • (1 : Matrix V V ℝ) - A).PosSemidef) :
    ∀ s ∈ thetaCliqueFeasible adj, s ≤ t := by
  rintro s ⟨X, hX, htr, hzero, rfl⟩
  have hkey : 0 ≤ ((t • (1 : Matrix V V ℝ) - A) * X).trace := trace_mul_nonneg hpsd hX
  have hsym : ∀ u v : V, X u v = X v u := by
    intro u v
    have h := congrFun (congrFun hX.isHermitian u) v
    simpa [Matrix.conjTranspose_apply] using h.symm
  have hpt : ∀ u v : V, (t • (1 : Matrix V V ℝ) - A) u v * X v u
      = t * (if u = v then X u u else 0) - X u v := by
    intro u v
    simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
    by_cases h : u = v
    · subst h
      rw [hd u]
      simp
      ring
    · by_cases hadj : adj u v
      · rw [he u v hadj, ← hsym u v]
        simp only [if_neg h]
        ring
      · rw [← hsym u v, hzero u v h hadj]
        simp only [if_neg h]
        ring
  have hetr : ((t • (1 : Matrix V V ℝ) - A) * X).trace
      = ∑ u : V, ∑ v : V, (t • (1 : Matrix V V ℝ) - A) u v * X v u := by
    simp [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]
  have hrow : ∀ u : V, ∑ v : V, (t • (1 : Matrix V V ℝ) - A) u v * X v u
      = t * X u u - ∑ v : V, X u v := by
    intro u
    rw [Finset.sum_congr rfl fun v _ => hpt u v, Finset.sum_sub_distrib]
    congr 1
    rw [← Finset.mul_sum]
    simp
  have htr' : ∑ u : V, X u u = 1 := by rw [← htr]; simp [Matrix.trace, Matrix.diag_apply]
  rw [hetr, Finset.sum_congr rfl fun u _ => hrow u, Finset.sum_sub_distrib, ← Finset.mul_sum,
    htr'] at hkey
  linarith

end

/- Weak-duality helpers above adapted from woshuajolk's statement9 artifact
5976674d-1f8c-45d6-8435-e90279139d3e. Definitions retain the original theta SDP. -/
variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]

theorem theta_product_le_of_regularize (adj : V → V → Prop)
    (hreg : ∀ X : Matrix V V ℝ, X.PosSemidef → X.trace = 1 →
      (∀ i j, i ≠ j → ¬ adj i j → X i j = 0) →
      ∃ Y : Matrix V V ℝ, Y.PosSemidef ∧ Y.trace = 1 ∧
        (∀ i j, i ≠ j → ¬ adj i j → Y i j = 0) ∧
        (∀ i, Y i i = (Fintype.card V : ℝ)⁻¹) ∧
        (∀ i, ∑ j, Y i j = (∑ a, ∑ b, X a b) / Fintype.card V)) :
    thetaClique adj * thetaClique (fun i j => i ≠ j ∧ ¬ adj i j) ≤ Fintype.card V := by
  let co : V → V → Prop := fun i j => i ≠ j ∧ ¬ adj i j
  have hb : 0 < thetaClique co := lt_of_lt_of_le zero_lt_one (theta_ge_one co)
  have hn : (0 : ℝ) ≤ Fintype.card V := Nat.cast_nonneg _
  have ha : thetaClique adj ≤ (Fintype.card V : ℝ) / thetaClique co := by
    apply csSup_le ⟨1, one_feasible adj⟩
    rintro s ⟨X, hX, htr, hz, rfl⟩
    by_cases hs : (∑ a, ∑ b, X a b) ≤ 0
    · exact hs.trans (div_nonneg hn hb.le)
    have hspos : 0 < ∑ a, ∑ b, X a b := lt_of_not_ge hs
    obtain ⟨Y, hY, _, hYzero, hYdiag, hYrow⟩ := hreg X hX htr hz
    obtain ⟨B, hBd, hBe, hB⟩ :=
      uniform_to_complement_certificate hspos hY hYdiag hYrow hYzero
    have hco : thetaClique co ≤ (Fintype.card V : ℝ) / (∑ a, ∑ b, X a b) :=
      Real.sSup_le (feasible_le (adj := co) hBd (fun i j hij => hBe i j hij.1 hij.2) hB)
        (div_nonneg hn hspos.le)
    apply (le_div_iff₀ hb).mpr
    have h := (le_div_iff₀ hspos).mp hco
    nlinarith
  exact (le_div_iff₀ hb).mp ha

end Submissions.PaleyLocThetaProduct.Separation

/- The certificate-to-feasible-point construction adapts `thetaClique_ge` from
woshuajolk's Jig #7 artifact b3456f5e-e74d-403f-95de-16f405ee39b6.
This is standard prior art. For checking, concatenate after the proved compactness
and approximate-duality helpers; no admitted statement is imported. -/
namespace Submissions.PaleyLocThetaProduct.Separation

open Matrix Commons

variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]

theorem theta_ge_of_complement_certificate (adj : V → V → Prop)
    (Y : Matrix V V ℝ) (t : ℝ) (ht : 0 < t)
    (hdiag : ∀ i, Y i i = 1)
    (hnonadj : ∀ i j, i ≠ j → ¬ adj i j → Y i j = 1)
    (hpsd : (t • (1 : Matrix V V ℝ) - Y).PosSemidef) :
    (Fintype.card V : ℝ) / t ≤ thetaClique adj := by
  classical
  let n : ℝ := Fintype.card V
  have hn : 0 < n := by dsimp [n]; exact_mod_cast Fintype.card_pos
  let J : Matrix V V ℝ := Matrix.of fun _ _ => 1
  have hJ : J.PosSemidef := by
    simpa [J, Matrix.vecMulVec] using
      Matrix.posSemidef_vecMulVec_self_star (fun _ : V => (1 : ℝ))
  let M : Matrix V V ℝ := (t • (1 : Matrix V V ℝ) - Y) + J
  have hM : M.PosSemidef := hpsd.add hJ
  let X : Matrix V V ℝ := (1 / (t * n)) • M
  have hX : X.PosSemidef := hM.smul (show 0 ≤ 1 / (t * n) by positivity)
  have htrY : Y.trace = n := by simp [Matrix.trace, hdiag, n]
  have htrJ : J.trace = n := by simp [Matrix.trace, Matrix.diag_apply, J, n]
  have htrM : M.trace = t * n := by
    simp only [M, Matrix.trace_add, Matrix.trace_sub, Matrix.trace_smul,
      Matrix.trace_one, htrY, htrJ, smul_eq_mul]
    change t * n - n + n = t * n
    ring
  have htrX : X.trace = 1 := by
    simp only [X, Matrix.trace_smul, smul_eq_mul, htrM]
    field_simp
  have hz : ∀ i j, i ≠ j → ¬ adj i j → X i j = 0 := by
    intro i j hij hadj
    simp [X, M, J, Matrix.smul_apply, Matrix.add_apply, Matrix.sub_apply,
      Matrix.one_apply_ne hij, hnonadj i j hij hadj]
  have hsum : 0 ≤ ∑ i, ∑ j, (t • (1 : Matrix V V ℝ) - Y) i j := by
    simpa [Matrix.mulVec, dotProduct] using
      hpsd.dotProduct_mulVec_nonneg (fun _ : V => (1 : ℝ))
  have hsumM : n ^ 2 ≤ ∑ i, ∑ j, M i j := by
    have hJsum : (∑ i, ∑ j, J i j) = n ^ 2 := by simp [J, n, sq]
    simp only [M, Matrix.add_apply, Finset.sum_add_distrib, hJsum]
    linarith
  have hobj : n / t ≤ ∑ i, ∑ j, X i j := by
    have hscaled := mul_le_mul_of_nonneg_left hsumM
      (show 0 ≤ 1 / (t * n) by positivity)
    have heq : 1 / (t * n) * n ^ 2 = n / t := by field_simp
    rw [heq] at hscaled
    simpa [X, Matrix.smul_apply, Finset.mul_sum] using hscaled
  exact hobj.trans (le_csSup (feasible_bddAbove adj) ⟨X, hX, htrX, hz, rfl⟩)

/-- The generic lower half of the theta product inequality. -/
theorem theta_product_lower (adj : V → V → Prop) (hsymm : Symmetric adj) :
    (Fintype.card V : ℝ) ≤
      thetaClique adj * thetaClique (fun i j => i ≠ j ∧ ¬ adj i j) := by
  classical
  let cadj : V → V → Prop := fun i j => i ≠ j ∧ ¬ adj i j
  let c : ℝ := thetaClique cadj
  have hc : 0 < c := lt_of_lt_of_le zero_lt_one (theta_ge_one cadj)
  refine le_of_forall_pos_le_add fun ε hε => ?_
  let t : ℝ := thetaClique adj + ε / c
  have ht : thetaClique adj < t := by
    dsimp only [t]
    exact lt_add_of_pos_right _ (div_pos hε hc)
  have htpos : 0 < t := (lt_of_lt_of_le zero_lt_one (theta_ge_one adj)).trans ht
  obtain ⟨Y, _, hdiag, hedge, hpsd⟩ := theta_approx_certificate adj hsymm ht
  have hnonadj : ∀ i j, i ≠ j → ¬ cadj i j → Y i j = 1 := by
    intro i j hij hnot
    apply hedge i j
    by_contra h
    exact hnot ⟨hij, h⟩
  have hlow := theta_ge_of_complement_certificate cadj Y t htpos hdiag hnonadj hpsd
  have hnle : (Fintype.card V : ℝ) ≤ c * t := (div_le_iff₀ htpos).mp hlow
  calc
    (Fintype.card V : ℝ) ≤ c * t := hnle
    _ = thetaClique adj * thetaClique (fun i j => i ≠ j ∧ ¬ adj i j) + ε := by
      change c * (thetaClique adj + ε / c) = thetaClique adj * c + ε
      field_simp

end Submissions.PaleyLocThetaProduct.Separation

namespace Submissions.PaleyLocThetaProduct.SquareAverage

open Matrix Commons

variable {p : ℕ} [Fact (Nat.Prime p)]

lemma sq_mul {s t : ZMod p} (hs : IsNonzeroSq s) (ht : IsNonzeroSq t) :
    IsNonzeroSq (s * t) := by
  obtain ⟨hs0, a, rfl⟩ := hs
  obtain ⟨ht0, b, rfl⟩ := ht
  exact ⟨mul_ne_zero hs0 ht0, a * b, by ring⟩

lemma sq_inv {s : ZMod p} (hs : IsNonzeroSq s) : IsNonzeroSq s⁻¹ := by
  obtain ⟨hs0, a, rfl⟩ := hs
  have ha : a ≠ 0 := by intro h; exact hs0 (by rw [h]; ring)
  exact ⟨inv_ne_zero hs0, a⁻¹, by field_simp⟩

variable [NeZero p]

/-- the multiplicative action of a vertex on a vertex -/
def act (w u : PaleyLocV p) : PaleyLocV p := ⟨(w : ZMod p) * (u : ZMod p), sq_mul w.2 u.2⟩

def vinv (w : PaleyLocV p) : PaleyLocV p := ⟨((w : ZMod p))⁻¹, sq_inv w.2⟩

@[simp] lemma act_coe (w u : PaleyLocV p) : ((act w u : PaleyLocV p) : ZMod p)
    = (w : ZMod p) * (u : ZMod p) := rfl

@[simp] lemma vinv_coe (w : PaleyLocV p) : ((vinv w : PaleyLocV p) : ZMod p)
    = ((w : ZMod p))⁻¹ := rfl

/-- the action of a fixed `w` is a permutation of the vertex set -/
def actEquiv (w : PaleyLocV p) : PaleyLocV p ≃ PaleyLocV p where
  toFun := act w
  invFun := act (vinv w)
  left_inv u := by
    apply Subtype.ext
    have hw : (w : ZMod p) ≠ 0 := w.2.1
    simp [act, vinv]
    field_simp
  right_inv u := by
    apply Subtype.ext
    have hw : (w : ZMod p) ≠ 0 := w.2.1
    simp [act, vinv]
    field_simp

lemma act_injective (w : PaleyLocV p) : Function.Injective (act w) :=
  (actEquiv w).injective

lemma act_adj (w u v : PaleyLocV p) :
    paleyLocAdj p (act w u) (act w v) ↔ paleyLocAdj p u v := by
  have hw : (w : ZMod p) ≠ 0 := w.2.1
  constructor
  · intro h
    have he : ((act w u : PaleyLocV p) : ZMod p) - ((act w v : PaleyLocV p) : ZMod p)
        = (w : ZMod p) * ((u : ZMod p) - (v : ZMod p)) := by simp [act]; ring
    have h2 : IsNonzeroSq ((w : ZMod p) * ((u : ZMod p) - (v : ZMod p))) := by rwa [← he]
    have h3 := sq_mul (sq_inv w.2) h2
    have h4 : ((w : ZMod p))⁻¹ * ((w : ZMod p) * ((u : ZMod p) - (v : ZMod p))) = (u : ZMod p) - (v : ZMod p) := by
      field_simp
    rwa [h4] at h3
  · intro h
    have he : ((act w u : PaleyLocV p) : ZMod p) - ((act w v : PaleyLocV p) : ZMod p)
        = (w : ZMod p) * ((u : ZMod p) - (v : ZMod p)) := by simp [act]; ring
    show IsNonzeroSq _
    rw [he]
    exact sq_mul w.2 h


/- The action helpers above are adapted from woshuajolk, Jig artifact
ccd0ab95-3712-4390-8ca0-bab1ca47c341. This strengthens its averaging output
with the uniform diagonal and row sums required for theta product duality. -/
lemma act_comm (w u : PaleyLocV p) : act w u = act u w := by
  apply Subtype.ext
  exact mul_comm _ _

theorem regularize (X : Matrix (PaleyLocV p) (PaleyLocV p) ℝ)
    (hX : X.PosSemidef) (htr : X.trace = 1)
    (hz : ∀ u v : PaleyLocV p, u ≠ v → ¬ paleyLocAdj p u v → X u v = 0) :
    ∃ Y : Matrix (PaleyLocV p) (PaleyLocV p) ℝ,
      Y.PosSemidef ∧ Y.trace = 1 ∧
      (∀ u v : PaleyLocV p, u ≠ v → ¬ paleyLocAdj p u v → Y u v = 0) ∧
      (∀ u, Y u u = (Fintype.card (PaleyLocV p) : ℝ)⁻¹) ∧
      (∀ u, ∑ v, Y u v = (∑ a, ∑ b, X a b) / Fintype.card (PaleyLocV p)) := by
  classical
  have hone : IsNonzeroSq (1 : ZMod p) := ⟨one_ne_zero, ⟨1, by ring⟩⟩
  haveI : Nonempty (PaleyLocV p) := ⟨⟨1, hone⟩⟩
  let n : ℝ := Fintype.card (PaleyLocV p)
  have hn : n ≠ 0 := by dsimp [n]; exact_mod_cast Fintype.card_ne_zero
  let Y := n⁻¹ • ∑ w : PaleyLocV p, X.submatrix (act w) (act w)
  have hval (u v : PaleyLocV p) : Y u v = n⁻¹ * ∑ w, X (act w u) (act w v) := by
    simp [Y, Matrix.smul_apply, Matrix.sum_apply, Matrix.submatrix_apply]
  have hdiag (u : PaleyLocV p) : Y u u = n⁻¹ := by
    rw [hval]
    have he : ∑ w, X (act w u) (act w u) = X.trace := by
      simp_rw [act_comm _ u]
      exact Fintype.sum_equiv (actEquiv u) _ _ (fun w => rfl)
    rw [he, htr, mul_one]
  refine ⟨Y, (Matrix.posSemidef_sum _ (fun w _ => hX.submatrix (act w))).smul
    (by positivity), ?_, ?_, hdiag, ?_⟩
  · change (∑ u, Y u u) = 1
    simp_rw [hdiag]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    exact mul_inv_cancel₀ hn
  · intro u v huv hadj
    rw [hval]
    have he (w : PaleyLocV p) : X (act w u) (act w v) = 0 :=
      hz _ _ (fun h => huv ((actEquiv w).injective h))
        (fun h => hadj ((act_adj w u v).mp h))
    simp_rw [he]
    simp
  · intro u
    simp_rw [hval]
    rw [← Finset.mul_sum, Finset.sum_comm]
    have hinner (w : PaleyLocV p) :
        ∑ v, X (act w u) (act w v) = ∑ v, X (act w u) v :=
      Fintype.sum_equiv (actEquiv w) _ _ (fun v => rfl)
    simp_rw [hinner, act_comm _ u]
    have he : (∑ w : PaleyLocV p, ∑ v, X (act u w) v) = ∑ a, ∑ b, X a b :=
      Fintype.sum_equiv (actEquiv u) _ _ (fun w => rfl)
    rw [he]
    rw [div_eq_mul_inv, mul_comm]

end Submissions.PaleyLocThetaProduct.SquareAverage

namespace Submissions.PaleyLocThetaProduct.Arithmetic
open Finset
variable {p : ℕ} [Fact (Nat.Prime p)] [NeZero p]
/- Vertex-count helpers adapted from woshuajolk's artifact
b3456f5e-e74d-403f-95de-16f405ee39b6. The count is prior art, not a new bound. -/
lemma card_sq (hp2 : p ≠ 2) :
    2 * Fintype.card {x : ZMod p // x ≠ 0 ∧ IsSquare x} + 1 = p := by
  classical
  have hchar : ringChar (ZMod p) ≠ 2 := by rw [ZMod.ringChar_zmod_n]; exact hp2
  set χ := quadraticChar (ZMod p) with hχ
  set S := (univ : Finset (ZMod p)).filter (fun x => x ≠ 0 ∧ IsSquare x) with hS
  set N := (univ : Finset (ZMod p)).filter (fun x => x ≠ 0 ∧ ¬ IsSquare x) with hN
  have hpt : ∀ a : ZMod p,
      χ a = (if a ∈ S then (1:ℤ) else 0) - (if a ∈ N then (1:ℤ) else 0) := by
    intro a
    by_cases ha : a = 0
    · subst ha; simp [hS, hN, hχ]
    · by_cases hsq : IsSquare a
      · have h1 : χ a = 1 := (quadraticChar_one_iff_isSquare ha).mpr hsq
        simp [hS, hN, ha, hsq, h1]
      · have h1 : χ a = -1 := quadraticChar_neg_one_iff_not_isSquare.mpr hsq
        simp [hS, hN, ha, hsq, h1]
  have h0 : ∑ a : ZMod p, χ a = 0 := quadraticChar_sum_zero hchar
  rw [Finset.sum_congr rfl (fun a _ => hpt a), Finset.sum_sub_distrib] at h0
  simp only [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul, mul_one] at h0
  have hcards : S.card = N.card := by exact_mod_cast sub_eq_zero.mp h0
  have hSe : S = (univ.erase (0 : ZMod p)).filter (fun x => IsSquare x) := by
    ext x; simp [hS, Finset.mem_erase]
  have hNe : N = (univ.erase (0 : ZMod p)).filter (fun x => ¬ IsSquare x) := by
    ext x; simp [hN, Finset.mem_erase]
  have hcardp : Fintype.card (ZMod p) = p := ZMod.card p
  have hp1 : 1 ≤ p := (Fact.out (p := Nat.Prime p)).one_lt.le.trans' (by norm_num)
  have hunion : S.card + N.card = p - 1 := by
    rw [hSe, hNe, Finset.card_filter_add_card_filter_not,
      Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, hcardp]
  have hsub : Fintype.card {x : ZMod p // x ≠ 0 ∧ IsSquare x} = S.card := by
    rw [hS, Fintype.card_subtype]
  rw [hsub]
  omega


lemma card_paleyLocV (hp2 : p ≠ 2) :
    2 * Fintype.card (Commons.PaleyLocV p) + 1 = p := by
  have : Fintype.card (Commons.PaleyLocV p)
      = Fintype.card {x : ZMod p // x ≠ 0 ∧ IsSquare x} :=
    Fintype.card_congr (Equiv.subtypeEquivRight (fun _ => Iff.rfl))
  rw [this]
  exact card_sq hp2


end Submissions.PaleyLocThetaProduct.Arithmetic

namespace Submissions.PaleyLocThetaProduct.Product
open Commons Separation

noncomputable def coTheta (p : ℕ) (hp : 0 < p) : ℝ :=
  haveI : NeZero p := NeZero.of_pos hp
  thetaClique (fun u v : PaleyLocV p => u ≠ v ∧ ¬ paleyLocAdj p u v)

/-- Lovasz's known vertex-transitive product identity specialized to Paley localization.
This proves Jig #7 statement11, not the asymptotic statement1. -/
theorem proof : ∀ p : ℕ, ∀ hp : Nat.Prime p, p % 4 = 1 →
    paleyLocTheta p hp.pos * coTheta p hp.pos = ((p : ℝ) - 1) / 2 := by
  intro p hp hp4
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  haveI : NeZero p := NeZero.of_pos hp.pos
  have hone : IsNonzeroSq (1 : ZMod p) := ⟨one_ne_zero, ⟨1, by ring⟩⟩
  haveI : Nonempty (PaleyLocV p) := ⟨⟨1, hone⟩⟩
  have hneg : IsNonzeroSq (-1 : ZMod p) := by
    refine ⟨neg_ne_zero.mpr one_ne_zero, ?_⟩
    change IsSquare (-1 : ZMod p)
    rw [ZMod.exists_sq_eq_neg_one_iff]
    omega
  have hsymm : Symmetric (paleyLocAdj p) := by
    intro u v h
    have hm := SquareAverage.sq_mul hneg h
    have he : (-1 : ZMod p) * ((u : ZMod p) - v) = (v : ZMod p) - u := by ring
    rw [he] at hm
    exact hm
  have hc : (Fintype.card (PaleyLocV p) : ℝ) = ((p : ℝ) - 1) / 2 := by
    have h := Arithmetic.card_paleyLocV (p := p) (by omega : p ≠ 2)
    have hr : 2 * (Fintype.card (PaleyLocV p) : ℝ) + 1 = (p : ℝ) := by exact_mod_cast h
    linarith
  change thetaClique (paleyLocAdj p) *
    thetaClique (fun u v : PaleyLocV p => u ≠ v ∧ ¬ paleyLocAdj p u v) = _
  rw [← hc]
  apply le_antisymm
  · exact theta_product_le_of_regularize (paleyLocAdj p) SquareAverage.regularize
  · exact theta_product_lower (paleyLocAdj p) hsymm

end Submissions.PaleyLocThetaProduct.Product
