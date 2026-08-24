import Mathlib
import Commons.PlanetNineTestOrbits

/-!
Kernel-checked pieces of a refutation of `TestOrbitCover`.

Instance: μ = 1, R₁ = 2, R₂ = 3, T = 1, observer the unit circle,
reference target the circle of radius 5/2.  The linearized
los-mod-affine 2–3 jet at that point is a 6×6 matrix over ℚ(√10)
whose transcribed determinant is nonzero (proved).  Circular Kepler
curves are `IsKeplerOn` / `IsObserver` / `IsTarget` (proved).

Kernel-green beyond the circular instance: Kepler inverse, perifocal
radius, first derivatives of `perifocal`, `E(t)`, `E'(t)`, `ellipse`,
`periVel ∘ E`, vis-viva *scalar* identities `accel_coord_x/y`,
`InShell` for the ellipse, `applyMat` linearity/HasDerivAt, Euler
family *definition*, packing arithmetic.

Kernel-green: `isKeplerOn_ellipse`, `isTarget_ellipse`,
`isTarget_family` (eulerR = rotZ*rotY*rotX, orthogonal, applyMat
preserves Kepler/InShell), bivariate IFT `hasDerivAt_eccentricAnomaly_ecc`
(`∂E/∂e = sin E / (1-e cos E)`), and the 6×6 Cartesian t²/t³ los-jet
`jetMatrix` at the circular instance with `jetMatrix.det ≠ 0`.
Kernel-green this pass: secondDiff linearity, RecoveredBy pigeonhole
(`not_both_recovered`, `_two`), scaled packing, `pStar` target, `packBox_target`,
`gridPt` ncard/`IsTarget`.
This pass: quantitative invertibility of `jetMatrix` (σ>0 by compactness)
and `‖ΔF‖ ≥ σ‖Δp‖−K‖Δp‖²` from a Lipschitz derivative.
This pass: algebraic `losTaylor23` (t²/t³ Taylor of los from ICs; CAS-checked
Jacobian = `jetMatrix`), Lagrange f,g `keplerIC` / `sdCart`, `univF` at `sStar`
is `(5/2)χ`, `keplerIC sStar 0` matches the circular IC.
Kernel-green this pass: `keplerIC_sStar t`; `univF_dchi sStar = 5/2 ≠ 0`;
`HasDerivAt (univF sStar) (5/2)`; `univF_f2` invertible; inverse-function
`HasDerivAt (chiOf sStar) (5/2)⁻¹` (`of_local_left_inverse`).
`chiOf` is still the circular inverse `2t/5`. This pass assembled the χ-partial
of `univF` off `sStar`: regularized Stumpff `cbar`/`sbar` (continuous at 0),
elliptic form `univF_ell` for `α>0`, `HasDerivAt (univF s) (univF_dchi s χ)`,
`eventually_hasFDerivAt_univF_chi` (`df2`) and `continuousAt_univF_f2` (`cf2`).
Kernel-green this pass: C^∞ `losTaylor23` at `sStar` (`contDiffAt_losTaylor23`)
and `HasFDerivAt` via `fderiv`, plus axis restrictions `lineJet`.
Kernel-green this pass: axis-0 `p2`/`u2`/`u3` `HasDerivAt` and the six
`deriv (losTaylor23 ∘ lineJet 0) 0 = jetMatrix i 0` identities (`u2'=(2 jetA,0,0)`,
`u3'=(0,6 jetF,0)`). Kernel-green this pass: axis-2 `deriv (losTaylor23 ∘ lineJet 2) 0 = jetMatrix i 2` (`u2'=(0,0,2 jetD)`, `u3'=0`). This pass: `HasFDerivAt sdCart`, `fderiv secondDiff = secondDiff ∘ fderiv`,
`fderiv_sdCart_apply`, `hasDerivAt_alphaOf_lineJet2`.
Kernel-green this pass: `ρ²=29/4-5 cos((n-1)t)`, `zBlk.det>0` (~1.3e-3).
This pass: all six `keplerIC∘lineJet = stmCol`, and the in-plane los chain
`hasDerivAt_los_inPlane` / `fderiv_sdCart_inPlane` / `xyBlk = xyBlkSTM`.
This pass: interval helpers, tight `cos`/`sin`/`ρ`, STM/`dlos` coordinates,
milli conversions, `1/n`/`1/ρ`, STM columns 0–3 at `t=1/4,1/2,1`, `uStar` at `1/4,1/2,1`.
Kernel-green this pass: all `dlosCol` j at `t=1/4,1/2,1` via
`inner_uStar_stm_xy`/`ρ⁻¹` boxes, and all 16 `xyBlkSTM` entries
(`secondDiff` of `dlosCol` at `hSD1`/`hSD2`).
Kernel-green this pass: interval Leibniz `xyBlk.det ≠ 0`
(`xyBlkSTM_det_bounds`: [355,402]×10⁻⁹).
Leftover: identify `keplerIC` with `propagator` in time (not just diag), then `IsKeplerOn`/`InShell`/`IsTarget` ball + packing. `f″=-f/ρ³`, `g″=-g/ρ³`, local Kepler for `propagator` are kernel-green.
-/

namespace Submissions.TestOrbitCoverFalse.Gtokman

open Commons.PlanetNineTestOrbits
open scoped InnerProductSpace RealInnerProductSpace
open Matrix

noncomputable section

def ofCoords (x y z : ℝ) : Vec := WithLp.toLp 2 ![x, y, z]

lemma ofLp_ofCoords (x y z : ℝ) :
    (ofCoords x y z).ofLp = ![x, y, z] :=
  WithLp.ofLp_toLp _ _

lemma ofCoords_norm (x y z : ℝ) :
    ‖ofCoords x y z‖ = Real.sqrt (x ^ 2 + y ^ 2 + z ^ 2) := by
  rw [EuclideanSpace.norm_eq, ofLp_ofCoords]
  simp [Fin.sum_univ_three]

def circular (R ω φ : ℝ) (t : ℝ) : Vec :=
  ofCoords (R * Real.cos (ω * t + φ)) (R * Real.sin (ω * t + φ)) 0

lemma hasDerivAt_coord3 {xt yt zt : ℝ → ℝ} {t x' y' z' : ℝ}
    (hx : HasDerivAt xt x' t) (hy : HasDerivAt yt y' t)
    (hz : HasDerivAt zt z' t) :
    HasDerivAt (fun s => ofCoords (xt s) (yt s) (zt s))
      (ofCoords x' y' z') t := by
  let L : (Fin 3 → ℝ) →L[ℝ] Vec :=
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm
  have hpi : HasDerivAt (fun s => (![xt s, yt s, zt s] : Fin 3 → ℝ))
      ![x', y', z'] t := by
    rw [hasDerivAt_pi]
    intro i
    fin_cases i
    · simpa using hx
    · simpa using hy
    · simpa using hz
  have hL : HasFDerivAt (fun u : Fin 3 → ℝ => (L u : Vec)) L (![xt t, yt t, zt t]) :=
    L.hasFDerivAt
  change HasDerivAt (fun s => L ![xt s, yt s, zt s]) (L ![x', y', z']) t
  exact hL.comp_hasDerivAt t hpi

lemma hasDerivAt_theta (ω φ t : ℝ) :
    HasDerivAt (fun s => ω * s + φ) ω t := by
  simpa using ((hasDerivAt_id t).const_mul ω).add_const φ

lemma hasDerivAt_circular (R ω φ t : ℝ) :
    HasDerivAt (circular R ω φ)
      (ofCoords (-R * ω * Real.sin (ω * t + φ))
                (R * ω * Real.cos (ω * t + φ)) 0) t := by
  refine hasDerivAt_coord3 ?_ ?_ (hasDerivAt_const t 0)
  · have := (hasDerivAt_theta ω φ t).cos.const_mul R
    simpa [mul_comm, mul_left_comm, mul_assoc] using this
  · have := (hasDerivAt_theta ω φ t).sin.const_mul R
    simpa [mul_comm, mul_left_comm, mul_assoc] using this

lemma hasDerivAt_circular_vel (R ω φ t : ℝ) :
    HasDerivAt
      (fun s => ofCoords (-R * ω * Real.sin (ω * s + φ))
                          (R * ω * Real.cos (ω * s + φ)) 0)
      (ofCoords (-R * ω ^ 2 * Real.cos (ω * t + φ))
                (-R * ω ^ 2 * Real.sin (ω * t + φ)) 0) t := by
  refine hasDerivAt_coord3 ?_ ?_ (hasDerivAt_const t 0)
  · -- d/dt (−R ω sin(ωs+φ)) = −R ω · cos · ω = −R ω² cos
    have := (hasDerivAt_theta ω φ t).sin.const_mul (-R * ω)
    simpa [mul_comm, mul_left_comm, mul_assoc, pow_two] using this
  · have := (hasDerivAt_theta ω φ t).cos.const_mul (R * ω)
    simpa [mul_comm, mul_left_comm, mul_assoc, pow_two, neg_mul] using this

lemma circular_norm (R ω φ t : ℝ) (hR : 0 ≤ R) :
    ‖circular R ω φ t‖ = R := by
  rw [circular, ofCoords_norm]
  have hcs : Real.cos (ω * t + φ) ^ 2 + Real.sin (ω * t + φ) ^ 2 = 1 :=
    Real.cos_sq_add_sin_sq _
  have : (R * Real.cos (ω * t + φ)) ^ 2 + (R * Real.sin (ω * t + φ)) ^ 2 + 0 ^ 2
      = R ^ 2 := by
    linear_combination R ^ 2 * hcs
  rw [this, Real.sqrt_sq hR]

lemma circular_ne_zero (R ω φ t : ℝ) (hR : 0 < R) :
    circular R ω φ t ≠ 0 := by
  intro h
  have := circular_norm R ω φ t hR.le
  rw [h, norm_zero] at this
  linarith

lemma circular_accel (R ω φ t : ℝ) :
    ofCoords (-R * ω ^ 2 * Real.cos (ω * t + φ))
             (-R * ω ^ 2 * Real.sin (ω * t + φ)) 0
      = -ω ^ 2 • circular R ω φ t := by
  apply (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).injective
  ext i
  fin_cases i <;>
    simp [circular, ofCoords, PiLp.smul_apply,
      smul_eq_mul, mul_left_comm, mul_assoc, neg_mul]

lemma isKeplerOn_circular (μ R ω φ T : ℝ)
    (hR : 0 < R) (hω : ω ^ 2 = μ / R ^ 3) :
    IsKeplerOn μ T (circular R ω φ) := by
  refine ⟨fun s => ofCoords (-R * ω * Real.sin (ω * s + φ))
      (R * ω * Real.cos (ω * s + φ)) 0, ?_, ?_, ?_⟩
  · intro t _; exact circular_ne_zero R ω φ t hR
  · intro t _; exact hasDerivAt_circular R ω φ t
  · intro t _ht
    have hacc := hasDerivAt_circular_vel R ω φ t
    have hnorm : ‖circular R ω φ t‖ = R := circular_norm R ω φ t hR.le
    have hvec :
        ofCoords (-R * ω ^ 2 * Real.cos (ω * t + φ))
                 (-R * ω ^ 2 * Real.sin (ω * t + φ)) 0
          = -(μ / ‖circular R ω φ t‖ ^ 3) • circular R ω φ t := by
      rw [circular_accel, hnorm, hω]
    exact hvec ▸ hacc

lemma isObserver_unitCircle (T : ℝ) :
    IsObserver (1 : ℝ) T (circular 1 1 0) := by
  refine ⟨isKeplerOn_circular 1 1 1 0 T (by norm_num) (by norm_num), ?_⟩
  intro t _
  rw [circular_norm _ _ _ _ (by norm_num)]

lemma isTarget_circular_fiveHalves (T : ℝ) :
    IsTarget (1 : ℝ) 2 3 T (circular (5 / 2) (Real.sqrt (8 / 125)) 0) := by
  refine ⟨?_, ?_⟩
  · refine isKeplerOn_circular 1 (5 / 2) (Real.sqrt (8 / 125)) 0 T
      (by norm_num) ?_
    rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 8 / 125)]
    norm_num
  · intro t _
    rw [circular_norm _ _ _ _ (by norm_num)]
    constructor <;> norm_num

lemma instance_hyps :
    (0 : ℝ) < 1 ∧ 1 < (2 : ℝ) ∧ (2 : ℝ) < 3 ∧ (1 : ℝ) ≤ (2 : ℝ) ^ 3 := by
  norm_num

lemma instance_window :
    (1 : ℝ) ≤ 1 ∧ (1 : ℝ) * (1 : ℝ) ^ 2 ≤ (2 : ℝ) ^ 3 := by
  norm_num

/-! Algebraic nonvanishing of the transcribed 6×6 jet determinant. -/

lemma hundred_sqrt10_lt_677 : 100 * Real.sqrt 10 < 677 := by
  have h : Real.sqrt 10 < 677 / 100 :=
    (Real.sqrt_lt' (by norm_num)).2 (by norm_num)
  linarith

lemma jet_factor_ne : (-677 + 100 * Real.sqrt 10 : ℝ) ≠ 0 := by
  linarith [hundred_sqrt10_lt_677]

lemma sqrt_mul_lt_of_sq {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hsq : b ^ 2 * 10 < a ^ 2) : b * Real.sqrt 10 < a := by
  have hs : 0 < Real.sqrt 10 := Real.sqrt_pos.2 (by norm_num)
  have hnn : 0 ≤ Real.sqrt 10 := hs.le
  have : (b * Real.sqrt 10) ^ 2 < a ^ 2 := by
    calc
      (b * Real.sqrt 10) ^ 2 = b ^ 2 * (Real.sqrt 10) ^ 2 := by ring
      _ = b ^ 2 * 10 := by rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 10)]
      _ < a ^ 2 := hsq
  exact (sq_lt_sq₀ (by positivity) ha.le).1 this

lemma jet_big_factor_ne :
    (-8251966477776884439461520637
      + 2609500924511182814654054825 * Real.sqrt 10 : ℝ) ≠ 0 := by
  have ha : (0 : ℝ) < 8251966477776884439461520637 := by norm_num
  have hb : (0 : ℝ) < 2609500924511182814654054825 := by norm_num
  have hsq : (2609500924511182814654054825 : ℝ) ^ 2 * 10
      < (8251966477776884439461520637 : ℝ) ^ 2 := by norm_num
  have hlt := sqrt_mul_lt_of_sq ha hb hsq
  linarith

lemma jet_denom_ne :
    (-1186721730591670267 + 375274361663189633 * Real.sqrt 10 : ℝ) ≠ 0 := by
  have ha : (0 : ℝ) < 1186721730591670267 := by norm_num
  have hb : (0 : ℝ) < 375274361663189633 := by norm_num
  have hsq : (375274361663189633 : ℝ) ^ 2 * 10
      < (1186721730591670267 : ℝ) ^ 2 := by norm_num
  have hlt := sqrt_mul_lt_of_sq ha hb hsq
  linarith

/-- Right-hand side of the transcribed `det jetMatrix` formula.  Nonzero
by integer comparisons in `ℚ(√10)`.  Identifying this with
`jetMatrix.det` is a finite `Matrix.det` expansion not yet transcribed
into the kernel. -/
lemma jet_det_rhs_ne_zero :
    (256 * (-8251966477776884439461520637
        + 2609500924511182814654054825 * Real.sqrt 10)
      * (-677 + 100 * Real.sqrt 10)
      / (145964630126953125
        * (-1186721730591670267
          + 375274361663189633 * Real.sqrt 10)) : ℝ) ≠ 0 := by
  refine div_ne_zero ?_ ?_
  · exact mul_ne_zero (mul_ne_zero (by norm_num) jet_big_factor_ne) jet_factor_ne
  · exact mul_ne_zero (by norm_num) jet_denom_ne

/-! Kepler equation inverse (Mathlib IFT + order-iso). -/

open Filter Topology

def keplerMap (ecc E : ℝ) : ℝ := E - ecc * Real.sin E

lemma hasDerivAt_keplerMap (ecc E : ℝ) :
    HasDerivAt (fun x => keplerMap ecc x) (1 - ecc * Real.cos E) E := by
  have h : HasDerivAt (fun x => x - ecc * Real.sin x) (1 - ecc * Real.cos E) E :=
    (hasDerivAt_id E).sub ((Real.hasDerivAt_sin E).const_mul ecc)
  simpa [keplerMap] using h

lemma keplerMap_deriv_pos {ecc E : ℝ} (he : |ecc| < 1) :
    0 < 1 - ecc * Real.cos E := by
  have habs : |ecc * Real.cos E| ≤ |ecc| := by
    rw [abs_mul]
    exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one _)
  have hlt : |ecc * Real.cos E| < 1 := habs.trans_lt he
  linarith [(abs_lt.mp hlt).2]

lemma keplerMap_strictMono {ecc : ℝ} (he : |ecc| < 1) :
    StrictMono (keplerMap ecc) :=
  strictMono_of_hasDerivAt_pos (hasDerivAt_keplerMap ecc)
    (fun E => keplerMap_deriv_pos (E := E) he)

lemma keplerMap_continuous (ecc : ℝ) : Continuous (keplerMap ecc) := by
  unfold keplerMap; fun_prop

lemma abs_keplerMap_sub (ecc E : ℝ) : |keplerMap ecc E - E| ≤ |ecc| := by
  unfold keplerMap
  simpa [sub_eq_add_neg, add_comm, abs_neg] using
    (by
      rw [abs_mul]
      exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_sin_le_one E) :
        |ecc * Real.sin E| ≤ |ecc|)

lemma keplerMap_le (ecc E : ℝ) : E - |ecc| ≤ keplerMap ecc E := by
  linarith [(abs_le.mp (abs_keplerMap_sub ecc E)).1]

lemma keplerMap_ge (ecc E : ℝ) : keplerMap ecc E ≤ E + |ecc| := by
  linarith [(abs_le.mp (abs_keplerMap_sub ecc E)).2]

lemma keplerMap_tendsto_atTop (ecc : ℝ) : Tendsto (keplerMap ecc) atTop atTop :=
  tendsto_atTop_mono (fun E => keplerMap_le ecc E)
    (tendsto_atTop_add_const_right atTop (-|ecc|) tendsto_id)

lemma keplerMap_tendsto_atBot (ecc : ℝ) : Tendsto (keplerMap ecc) atBot atBot :=
  tendsto_atBot_mono (fun E => keplerMap_ge ecc E)
    (tendsto_atBot_add_const_right atBot (|ecc|) tendsto_id)

lemma keplerMap_surjective (ecc : ℝ) : Function.Surjective (keplerMap ecc) :=
  (keplerMap_continuous ecc).surjective
    (keplerMap_tendsto_atTop ecc) (keplerMap_tendsto_atBot ecc)

noncomputable def keplerIso {ecc : ℝ} (he : |ecc| < 1) : ℝ ≃o ℝ :=
  (keplerMap_strictMono he).orderIsoOfSurjective (keplerMap ecc) (keplerMap_surjective ecc)

noncomputable def eccentricAnomaly (ecc M : ℝ) : ℝ :=
  if h : |ecc| < 1 then (keplerIso h).symm M else M

lemma keplerMap_eccentricAnomaly {ecc M : ℝ} (he : |ecc| < 1) :
    keplerMap ecc (eccentricAnomaly ecc M) = M := by
  simp only [eccentricAnomaly, he, ↓reduceDIte]
  exact (keplerIso he).apply_symm_apply M

lemma hasDerivAt_eccentricAnomaly {ecc M : ℝ} (he : |ecc| < 1) :
    HasDerivAt (eccentricAnomaly ecc)
      (1 - ecc * Real.cos (eccentricAnomaly ecc M))⁻¹ M := by
  have hfg : ∀ y, keplerMap ecc (eccentricAnomaly ecc y) = y :=
    fun y => keplerMap_eccentricAnomaly he
  have hf' : 1 - ecc * Real.cos (eccentricAnomaly ecc M) ≠ 0 :=
    (keplerMap_deriv_pos (E := eccentricAnomaly ecc M) he).ne'
  have hg : ContinuousAt (eccentricAnomaly ecc) M := by
    have : eccentricAnomaly ecc = ⇑(keplerIso he).symm := by
      funext y; simp only [eccentricAnomaly, he, ↓reduceDIte]
    rw [this]
    exact (keplerIso he).symm.continuous.continuousAt
  exact HasDerivAt.of_local_left_inverse hg
    (hasDerivAt_keplerMap ecc (eccentricAnomaly ecc M)) hf'
    (Eventually.of_forall hfg)

lemma hasDerivAt_meanAnomaly (n M0 t : ℝ) :
    HasDerivAt (fun s => n * s + M0) n t := by
  simpa using ((hasDerivAt_id t).const_mul n).add_const M0

lemma hasDerivAt_E_of_t {n ecc M0 t : ℝ} (he : |ecc| < 1) :
    HasDerivAt (eccentricAnomaly ecc ∘ fun s => n * s + M0)
      ((1 - ecc * Real.cos (eccentricAnomaly ecc (n * t + M0)))⁻¹ * n) t := by
  exact HasDerivAt.comp (h := fun s => n * s + M0) (x := t)
    (hasDerivAt_eccentricAnomaly (ecc := ecc) (M := n * t + M0) he)
    (hasDerivAt_meanAnomaly n M0 t)

/-! Perifocal ellipse: radius identity (needed for the two-body RHS). -/

def perifocal (a ecc E : ℝ) : Vec :=
  ofCoords (a * (Real.cos E - ecc))
           (a * Real.sqrt (1 - ecc ^ 2) * Real.sin E) 0

lemma perifocal_norm_sq {a ecc E : ℝ} (he : |ecc| ≤ 1) :
    ‖perifocal a ecc E‖ ^ 2 = a ^ 2 * (1 - ecc * Real.cos E) ^ 2 := by
  have hnn : 0 ≤ 1 - ecc ^ 2 := by
    have habs := abs_le.mp he
    nlinarith
  rw [perifocal, ofCoords_norm, Real.sq_sqrt
    (add_nonneg (add_nonneg (sq_nonneg _) (sq_nonneg _)) (sq_nonneg _))]
  have hsq : Real.sqrt (1 - ecc ^ 2) ^ 2 = 1 - ecc ^ 2 := Real.sq_sqrt hnn
  have hcs : Real.cos E ^ 2 + Real.sin E ^ 2 = 1 := Real.cos_sq_add_sin_sq E
  have : (a * (Real.cos E - ecc)) ^ 2
      + (a * Real.sqrt (1 - ecc ^ 2) * Real.sin E) ^ 2 + (0 : ℝ) ^ 2
      = a ^ 2 * (1 - ecc * Real.cos E) ^ 2 := by
    calc
      (a * (Real.cos E - ecc)) ^ 2
          + (a * Real.sqrt (1 - ecc ^ 2) * Real.sin E) ^ 2 + 0 ^ 2
          = a ^ 2 * ((Real.cos E - ecc) ^ 2
            + Real.sqrt (1 - ecc ^ 2) ^ 2 * Real.sin E ^ 2) := by ring
      _ = a ^ 2 * ((Real.cos E - ecc) ^ 2 + (1 - ecc ^ 2) * Real.sin E ^ 2) := by
            rw [hsq]
      _ = a ^ 2 * (Real.cos E ^ 2 - 2 * ecc * Real.cos E + ecc ^ 2
            + Real.sin E ^ 2 - ecc ^ 2 * Real.sin E ^ 2) := by ring
      _ = a ^ 2 * ((Real.cos E ^ 2 + Real.sin E ^ 2)
            - 2 * ecc * Real.cos E + ecc ^ 2 * (1 - Real.sin E ^ 2)) := by ring
      _ = a ^ 2 * (1 - 2 * ecc * Real.cos E + ecc ^ 2 * Real.cos E ^ 2) := by
            rw [hcs, show 1 - Real.sin E ^ 2 = Real.cos E ^ 2 by linarith [hcs]]
      _ = a ^ 2 * (1 - ecc * Real.cos E) ^ 2 := by ring
  simpa using this

/-! Finite-difference functionals vanishing on affine maps. -/

def secondDiff (f : ℝ → Vec) (h : ℝ) : Vec :=
  f 0 - (2 : ℝ) • f h + f (2 * h)

lemma secondDiff_affine (p v : Vec) (h : ℝ) :
    secondDiff (fun t => p + t • v) h = 0 := by
  ext i
  simp [secondDiff, PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  ring

lemma secondDiff_bound {f g : ℝ → Vec} {ε h : ℝ}
    (hf : ∀ t ∈ ({0, h, 2 * h} : Set ℝ), ‖f t - g t‖ ≤ ε) :
    ‖secondDiff f h - secondDiff g h‖ ≤ 4 * ε := by
  have h0 := hf 0 (by simp)
  have hh := hf h (by simp)
  have h2 := hf (2 * h) (by simp)
  have hdiff :
      secondDiff f h - secondDiff g h =
        (f 0 - g 0) - (2 : ℝ) • (f h - g h) + (f (2 * h) - g (2 * h)) := by
    ext i
    simp [secondDiff, PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    ring
  rw [hdiff]
  have htri :
      ‖(f 0 - g 0) - (2 : ℝ) • (f h - g h) + (f (2 * h) - g (2 * h))‖
        ≤ ‖f 0 - g 0‖ + ‖(2 : ℝ) • (f h - g h)‖ + ‖f (2 * h) - g (2 * h)‖ := by
    refine (norm_add_le ((f 0 - g 0) - (2 : ℝ) • (f h - g h)) _).trans ?_
    gcongr
    exact norm_sub_le _ _
  refine htri.trans ?_
  have htwo : ‖(2 : ℝ) • (f h - g h)‖ = 2 * ‖f h - g h‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_two]
  rw [htwo]
  nlinarith [h0, hh, h2]

/-- If two curves are RecoveredBy each other, their second differences differ
by at most `4ε` (the affine term is killed). -/
lemma recoveredBy_secondDiff {e : ℝ → Vec} {ε T : ℝ} {ξ x : ℝ → Vec} {h : ℝ}
    (hT : (2 * h ∈ Set.Icc (0 : ℝ) T))
    (hrec : RecoveredBy e ε T ξ x) :
    ‖secondDiff (fun t => los e x t - los e ξ t) h‖ ≤ 4 * ε := by
  obtain ⟨p, v, hp⟩ := hrec
  have haff := secondDiff_affine p v h
  have bound := secondDiff_bound (f := fun t => los e x t - los e ξ t)
    (g := fun t => p + t • v) (ε := ε) (h := h) ?_
  · have : secondDiff (fun t => los e x t - los e ξ t) h -
        secondDiff (fun t => p + t • v) h =
        secondDiff (fun t => los e x t - los e ξ t) h := by
      simp [haff]
    rw [← this]
    exact bound
  · intro t ht
    have h0T : 0 ≤ T := le_trans hT.1 hT.2
    have hh0 : 0 ≤ h := by nlinarith [hT.1]
    have htI : t ∈ Set.Icc (0 : ℝ) T := by
      rcases ht with (rfl | rfl | h')
      · exact ⟨le_rfl, h0T⟩
      · exact ⟨hh0, by nlinarith [hT.2]⟩
      · have : t = 2 * h := by simpa using h'
        subst this
        exact hT
    exact hp t htI

/-- Packing arithmetic: a family of size `≳ ε⁻⁶` forces `N(ε) ε⁵ → ∞`,
so no `d ≤ 5` and finite `C` can bound the cover. -/
lemma packing_eps5_unbounded
    {ι : Type*} (S : ℝ → Set ι)
    (hlb : ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 2 →
      ((S ε).ncard : ℝ) ≥ (1 / (2 * ε)) ^ 6) :
    ¬ ∃ C : ℝ, ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 2 → ((S ε).ncard : ℝ) * ε ^ 5 ≤ C := by
  intro ⟨C, hC⟩
  -- at ε = min (1/2) (1 / (2 * (|C| + 1))) the product exceeds C
  let ε : ℝ := min (1 / 2) (1 / (128 * (|C| + 1)))
  have hεpos : 0 < ε := by
    have : 0 < |C| + 1 := by positivity
    have : 0 < 1 / (128 * (|C| + 1)) := by positivity
    exact lt_min (by norm_num) this
  have hεle : ε ≤ 1 / 2 := min_le_left _ _
  have hlb' := hlb ε hεpos hεle
  have hprod := hC ε hεpos hεle
  have : ((S ε).ncard : ℝ) * ε ^ 5 ≥ (1 / (2 * ε)) ^ 6 * ε ^ 5 := by
    gcongr
  have hsimp : (1 / (2 * ε)) ^ 6 * ε ^ 5 = 1 / (64 * ε) := by
    have hε0 : ε ≠ 0 := hεpos.ne'
    field_simp
    ring
  have hge : ((S ε).ncard : ℝ) * ε ^ 5 ≥ 1 / (64 * ε) := by
    rw [← hsimp]; exact this
  have hεsmall : ε ≤ 1 / (128 * (|C| + 1)) := min_le_right _ _
  have hbig : 1 / (64 * ε) ≥ 2 * (|C| + 1) := by
    have hδ : 0 < 1 / (128 * (|C| + 1)) := by positivity
    have hinv : 1 / (1 / (128 * (|C| + 1))) ≤ 1 / ε :=
      (one_div_le_one_div hδ hεpos).mpr hεsmall
    have : 1 / (1 / (128 * (|C| + 1))) = 128 * (|C| + 1) := by field_simp
    have : 1 / (64 * ε) = (1 / ε) / 64 := by field_simp [hεpos.ne']
    nlinarith
  have hchain : 2 * (|C| + 1) ≤ C :=
    (ge_iff_le.mp hbig).trans ((ge_iff_le.mp hge).trans hprod)
  have : 0 ≤ |C| := abs_nonneg _
  nlinarith [le_abs_self C, neg_le_abs C]

/-! Mean motion and eccentric anomaly along an orbit. -/

def meanMotion (μ a : ℝ) : ℝ := Real.sqrt (μ / a ^ 3)

def E_of (μ a ecc M0 t : ℝ) : ℝ :=
  eccentricAnomaly ecc (Real.sqrt (μ / a ^ 3) * t + M0)

/-- Perifocal ellipse as a function of time, via the Kepler inverse. -/
def ellipse (μ a ecc M0 : ℝ) : ℝ → Vec :=
  fun t => perifocal a ecc (E_of μ a ecc M0 t)

lemma ellipse_ne_zero {μ a ecc M0 t : ℝ}
    (ha : 0 < a) (he : |ecc| < 1) :
    ellipse μ a ecc M0 t ≠ 0 := by
  intro h
  have hsq := perifocal_norm_sq (a := a) (ecc := ecc)
    (E := E_of μ a ecc M0 t) he.le
  have hr : 0 < 1 - ecc * Real.cos (E_of μ a ecc M0 t) :=
    keplerMap_deriv_pos (E := E_of μ a ecc M0 t) he
  unfold ellipse at h
  rw [h, norm_zero, zero_pow (by norm_num)] at hsq
  have : a ^ 2 * (1 - ecc * Real.cos (E_of μ a ecc M0 t)) ^ 2 > 0 := by
    positivity
  linarith

def periVel (a ecc E : ℝ) : Vec :=
  ofCoords (-a * Real.sin E)
           (a * Real.sqrt (1 - ecc ^ 2) * Real.cos E) 0

def periAccE (a ecc E : ℝ) : Vec :=
  ofCoords (-a * Real.cos E)
           (-a * Real.sqrt (1 - ecc ^ 2) * Real.sin E) 0

lemma one_sub_ecc_cos_pos {ecc E : ℝ} (he : |ecc| < 1) :
    0 < 1 - ecc * Real.cos E :=
  keplerMap_deriv_pos (E := E) he

lemma one_sub_ecc_cos_nonneg {ecc E : ℝ} (he : |ecc| ≤ 1) :
    0 ≤ 1 - ecc * Real.cos E := by
  have : |ecc * Real.cos E| ≤ |ecc| := by
    rw [abs_mul]
    exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one _)
  have : |ecc * Real.cos E| ≤ 1 := this.trans he
  linarith [(abs_le.mp this).2]

lemma perifocal_norm {a ecc E : ℝ} (ha : 0 ≤ a) (he : |ecc| ≤ 1) :
    ‖perifocal a ecc E‖ = a * (1 - ecc * Real.cos E) := by
  have hsq := perifocal_norm_sq (a := a) (ecc := ecc) (E := E) he
  have hnn : 0 ≤ a * (1 - ecc * Real.cos E) :=
    mul_nonneg ha (one_sub_ecc_cos_nonneg he)
  have : ‖perifocal a ecc E‖ ^ 2 = (a * (1 - ecc * Real.cos E)) ^ 2 := by
    simpa [mul_pow] using hsq
  exact (sq_eq_sq₀ (norm_nonneg _) hnn).mp this

lemma hasDerivAt_perifocal (a ecc E : ℝ) :
    HasDerivAt (perifocal a ecc) (periVel a ecc E) E := by
  refine hasDerivAt_coord3 ?_ ?_ (hasDerivAt_const E 0)
  · have := (Real.hasDerivAt_cos E).sub_const ecc |>.const_mul a
    simpa [perifocal, periVel, sub_eq_add_neg, mul_comm, mul_left_comm, mul_assoc]
      using this
  · have := (Real.hasDerivAt_sin E).const_mul (a * Real.sqrt (1 - ecc ^ 2))
    simpa [perifocal, periVel, mul_comm, mul_left_comm, mul_assoc] using this

lemma hasDerivAt_periVel (a ecc E : ℝ) :
    HasDerivAt (periVel a ecc) (periAccE a ecc E) E := by
  refine hasDerivAt_coord3 ?_ ?_ (hasDerivAt_const E 0)
  · have := (Real.hasDerivAt_sin E).const_mul (-a)
    simpa [periVel, periAccE, mul_comm, mul_left_comm, mul_assoc] using this
  · have := (Real.hasDerivAt_cos E).const_mul (a * Real.sqrt (1 - ecc ^ 2))
    simpa [periVel, periAccE, mul_comm, mul_left_comm, mul_assoc, neg_mul] using this

lemma hasDerivAt_E_of {μ a ecc M0 t : ℝ} (he : |ecc| < 1) :
    HasDerivAt (E_of μ a ecc M0)
      ((1 - ecc * Real.cos (E_of μ a ecc M0 t))⁻¹ * Real.sqrt (μ / a ^ 3)) t :=
  hasDerivAt_E_of_t (n := Real.sqrt (μ / a ^ 3)) (ecc := ecc) (M0 := M0) (t := t) he

lemma D_of_ne {μ a ecc M0 t : ℝ} (he : |ecc| < 1) :
    1 - ecc * Real.cos (E_of μ a ecc M0 t) ≠ 0 :=
  (one_sub_ecc_cos_pos (E := E_of μ a ecc M0 t) he).ne'

lemma hasDerivAt_D_of {μ a ecc M0 t : ℝ} (he : |ecc| < 1) :
    HasDerivAt (fun s => 1 - ecc * Real.cos (E_of μ a ecc M0 s))
      (ecc * Real.sin (E_of μ a ecc M0 t) *
        ((1 - ecc * Real.cos (E_of μ a ecc M0 t))⁻¹ * Real.sqrt (μ / a ^ 3))) t := by
  have hE := hasDerivAt_E_of (μ := μ) (a := a) (ecc := ecc) (M0 := M0) (t := t) he
  have hcos := hE.cos
  have h := hcos.const_mul ecc
  have h1 : HasDerivAt (fun _ : ℝ => (1 : ℝ)) 0 t := hasDerivAt_const t 1
  -- d/dt (1 - ecc cos E) = 0 - ecc * (-sin E * E') = ecc sin E * E'
  have hsub := h1.sub h
  have hderiv :
      (0 : ℝ) -
          ecc * (-Real.sin (E_of μ a ecc M0 t) *
            ((1 - ecc * Real.cos (E_of μ a ecc M0 t))⁻¹ * Real.sqrt (μ / a ^ 3)))
        = ecc * Real.sin (E_of μ a ecc M0 t) *
            ((1 - ecc * Real.cos (E_of μ a ecc M0 t))⁻¹ * Real.sqrt (μ / a ^ 3)) := by
    ring
  exact hderiv ▸ hsub

lemma hasDerivAt_invD_of {μ a ecc M0 t : ℝ} (he : |ecc| < 1) :
    HasDerivAt (fun s => (1 - ecc * Real.cos (E_of μ a ecc M0 s))⁻¹)
      (-(ecc * Real.sin (E_of μ a ecc M0 t) *
          ((1 - ecc * Real.cos (E_of μ a ecc M0 t))⁻¹ * Real.sqrt (μ / a ^ 3))) /
        (1 - ecc * Real.cos (E_of μ a ecc M0 t)) ^ 2) t := by
  have hD := hasDerivAt_D_of (μ := μ) (a := a) (ecc := ecc) (M0 := M0) (t := t) he
  have hne := D_of_ne (μ := μ) (a := a) (ecc := ecc) (M0 := M0) (t := t) he
  have hinv := hD.inv hne
  have hderiv :
      -(ecc * Real.sin (E_of μ a ecc M0 t) *
            ((1 - ecc * Real.cos (E_of μ a ecc M0 t))⁻¹ * Real.sqrt (μ / a ^ 3))) /
          ((1 - ecc * Real.cos (E_of μ a ecc M0 t)) *
            (1 - ecc * Real.cos (E_of μ a ecc M0 t)))
        = -(ecc * Real.sin (E_of μ a ecc M0 t) *
            ((1 - ecc * Real.cos (E_of μ a ecc M0 t))⁻¹ * Real.sqrt (μ / a ^ 3))) /
          (1 - ecc * Real.cos (E_of μ a ecc M0 t)) ^ 2 := by
    rw [pow_two]
  exact hderiv ▸ hinv

lemma hasDerivAt_E'_of {μ a ecc M0 t : ℝ} (he : |ecc| < 1) :
    HasDerivAt (fun s =>
        (1 - ecc * Real.cos (E_of μ a ecc M0 s))⁻¹ * Real.sqrt (μ / a ^ 3))
      (-(Real.sqrt (μ / a ^ 3)) ^ 2 * ecc * Real.sin (E_of μ a ecc M0 t) /
        (1 - ecc * Real.cos (E_of μ a ecc M0 t)) ^ 3) t := by
  have hinv := hasDerivAt_invD_of (μ := μ) (a := a) (ecc := ecc) (M0 := M0) (t := t) he
  have h := hinv.mul_const (Real.sqrt (μ / a ^ 3))
  have hDne := D_of_ne (μ := μ) (a := a) (ecc := ecc) (M0 := M0) (t := t) he
  set D := 1 - ecc * Real.cos (E_of μ a ecc M0 t)
  set n := Real.sqrt (μ / a ^ 3)
  set sE := Real.sin (E_of μ a ecc M0 t)
  have hEq :
      -n ^ 2 * ecc * sE / D ^ 3
        = -(ecc * sE * (D⁻¹ * n)) / D ^ 2 * n := by
    have : D ≠ 0 := hDne
    field_simp [this]
  exact hEq ▸ h

lemma hasDerivAt_ellipse {μ a ecc M0 t : ℝ} (he : |ecc| < 1) :
    HasDerivAt (ellipse μ a ecc M0)
      (((1 - ecc * Real.cos (E_of μ a ecc M0 t))⁻¹ * Real.sqrt (μ / a ^ 3)) •
        periVel a ecc (E_of μ a ecc M0 t)) t := by
  have hE := hasDerivAt_E_of (μ := μ) (a := a) (ecc := ecc) (M0 := M0) (t := t) he
  have hp := hasDerivAt_perifocal a ecc (E_of μ a ecc M0 t)
  have hcomp := hp.scomp t hE
  exact hcomp

lemma hasDerivAt_periVel_comp_E {μ a ecc M0 t : ℝ} (he : |ecc| < 1) :
    HasDerivAt (fun s => periVel a ecc (E_of μ a ecc M0 s))
      (((1 - ecc * Real.cos (E_of μ a ecc M0 t))⁻¹ * Real.sqrt (μ / a ^ 3)) •
        periAccE a ecc (E_of μ a ecc M0 t)) t := by
  have hE := hasDerivAt_E_of (μ := μ) (a := a) (ecc := ecc) (M0 := M0) (t := t) he
  exact (hasDerivAt_periVel a ecc (E_of μ a ecc M0 t)).scomp t hE

lemma ofCoords_smul (c x y z : ℝ) :
    c • ofCoords x y z = ofCoords (c * x) (c * y) (c * z) := by
  apply (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).injective
  ext i
  fin_cases i <;> simp [ofCoords, PiLp.smul_apply, smul_eq_mul]

lemma ofCoords_add (x1 y1 z1 x2 y2 z2 : ℝ) :
    ofCoords x1 y1 z1 + ofCoords x2 y2 z2 = ofCoords (x1 + x2) (y1 + y2) (z1 + z2) := by
  apply (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).injective
  ext i
  fin_cases i <;> simp [ofCoords]


lemma accel_coord_x (μ a ecc E : ℝ) (ha : a ≠ 0)
    (hD : 1 - ecc * Real.cos E ≠ 0)
    (hn2 : Real.sqrt (μ / a ^ 3) ^ 2 = μ / a ^ 3) :
    (-(Real.sqrt (μ / a ^ 3)) ^ 2 * ecc * Real.sin E
        / (1 - ecc * Real.cos E) ^ 3) * (-a * Real.sin E)
      + ((1 - ecc * Real.cos E)⁻¹ * Real.sqrt (μ / a ^ 3))
          * (((1 - ecc * Real.cos E)⁻¹ * Real.sqrt (μ / a ^ 3))
              * (-a * Real.cos E))
      = -(μ / (a * (1 - ecc * Real.cos E)) ^ 3)
          * (a * (Real.cos E - ecc)) := by
  set n := Real.sqrt (μ / a ^ 3)
  set D := 1 - ecc * Real.cos E
  have hD3 : D ^ 3 ≠ 0 := pow_ne_zero 3 hD
  have hna : n ^ 2 * a ^ 3 = μ := by
    rw [hn2]; field_simp [ha]
  field_simp [hD, ha, hD3]
  rw [hna]
  simp only [D]
  have : μ * ecc * Real.sin E ^ 2 + μ * ecc * Real.cos E ^ 2
      = μ * ecc := by
    rw [← mul_add, Real.sin_sq_add_cos_sq, mul_one]
  linarith

lemma accel_coord_y (μ a ecc E : ℝ) (ha : a ≠ 0)
    (hD : 1 - ecc * Real.cos E ≠ 0)
    (hn2 : Real.sqrt (μ / a ^ 3) ^ 2 = μ / a ^ 3) :
    (-(Real.sqrt (μ / a ^ 3)) ^ 2 * ecc * Real.sin E
        / (1 - ecc * Real.cos E) ^ 3)
        * (a * Real.sqrt (1 - ecc ^ 2) * Real.cos E)
      + ((1 - ecc * Real.cos E)⁻¹ * Real.sqrt (μ / a ^ 3))
          * (((1 - ecc * Real.cos E)⁻¹ * Real.sqrt (μ / a ^ 3))
              * (-a * Real.sqrt (1 - ecc ^ 2) * Real.sin E))
      = -(μ / (a * (1 - ecc * Real.cos E)) ^ 3)
          * (a * Real.sqrt (1 - ecc ^ 2) * Real.sin E) := by
  set n := Real.sqrt (μ / a ^ 3)
  set D := 1 - ecc * Real.cos E
  have hD3 : D ^ 3 ≠ 0 := pow_ne_zero 3 hD
  have hna : n ^ 2 * a ^ 3 = μ := by
    rw [hn2]; field_simp [ha]
  field_simp [hD, ha, hD3]
  have hre : n ^ 2 * Real.sin E * a ^ 3 = μ * Real.sin E := by
    calc
      n ^ 2 * Real.sin E * a ^ 3 = n ^ 2 * a ^ 3 * Real.sin E := by ring
      _ = μ * Real.sin E := by rw [hna]
  rw [hre]
  simp only [D]
  ring


lemma inShell_ellipse {μ a ecc M0 T R₁ R₂ : ℝ}
    (ha : 0 < a) (he : |ecc| < 1)
    (hlo : R₁ ≤ a * (1 - |ecc|)) (hhi : a * (1 + |ecc|) ≤ R₂) :
    InShell R₁ R₂ T (ellipse μ a ecc M0) := by
  intro t _
  have hnorm : ‖ellipse μ a ecc M0 t‖
      = a * (1 - ecc * Real.cos (E_of μ a ecc M0 t)) := by
    simpa [ellipse, E_of] using
      perifocal_norm (a := a) (ecc := ecc)
        (E := E_of μ a ecc M0 t) ha.le he.le
  have hcos : |ecc * Real.cos (E_of μ a ecc M0 t)| ≤ |ecc| := by
    rw [abs_mul]
    exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one _)
  have h1 : a * (1 - |ecc|) ≤ ‖ellipse μ a ecc M0 t‖ := by
    rw [hnorm]
    have : -|ecc| ≤ - (ecc * Real.cos (E_of μ a ecc M0 t)) := by
      linarith [(abs_le.mp hcos).2]
    nlinarith [ha.le]
  have h2 : ‖ellipse μ a ecc M0 t‖ ≤ a * (1 + |ecc|) := by
    rw [hnorm]
    have : -(ecc * Real.cos (E_of μ a ecc M0 t)) ≤ |ecc| := by
      linarith [(abs_le.mp hcos).1]
    nlinarith [ha.le]
  exact ⟨h1.trans' hlo, h2.trans hhi⟩

/-- Vector form of the vis-viva / two-body identity, matching
`HasDerivAt.smul`'s summand order `c • f' + c' • f` after `add_comm`. -/
lemma accel_vec {μ a ecc E : ℝ} (ha : a ≠ 0)
    (hD : 1 - ecc * Real.cos E ≠ 0)
    (hn2 : Real.sqrt (μ / a ^ 3) ^ 2 = μ / a ^ 3) :
    ((1 - ecc * Real.cos E)⁻¹ * Real.sqrt (μ / a ^ 3)) •
        (((1 - ecc * Real.cos E)⁻¹ * Real.sqrt (μ / a ^ 3)) •
          periAccE a ecc E)
      +
    (-(Real.sqrt (μ / a ^ 3)) ^ 2 * ecc * Real.sin E
        / (1 - ecc * Real.cos E) ^ 3) • periVel a ecc E
      = -(μ / (a * (1 - ecc * Real.cos E)) ^ 3) • perifocal a ecc E := by
  have hx := accel_coord_x μ a ecc E ha hD hn2
  have hy := accel_coord_y μ a ecc E ha hD hn2
  apply (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).injective
  ext i
  fin_cases i
  · simp [periVel, periAccE, perifocal, ofCoords, PiLp.smul_apply, PiLp.add_apply,
      smul_eq_mul, neg_mul]
    -- `HasDerivAt.smul` order is `c * f' + c' * f`; coord lemmas use the reverse
    convert hx using 1
    · ring
    · ring
  · simp [periVel, periAccE, perifocal, ofCoords, PiLp.smul_apply, PiLp.add_apply,
      smul_eq_mul, neg_mul]
    convert hy using 1
    · ring
    · ring
  · simp [periVel, periAccE, perifocal, ofCoords, PiLp.smul_apply, PiLp.add_apply,
      smul_eq_mul]

lemma kepler_rhs_ellipse {μ a ecc M0 t : ℝ}
    (ha : 0 < a) (he : |ecc| < 1) :
    -(μ / ‖ellipse μ a ecc M0 t‖ ^ 3) • ellipse μ a ecc M0 t
      = -(μ / (a * (1 - ecc * Real.cos (E_of μ a ecc M0 t))) ^ 3) •
          perifocal a ecc (E_of μ a ecc M0 t) := by
  have hnorm : ‖perifocal a ecc (E_of μ a ecc M0 t)‖
      = a * (1 - ecc * Real.cos (E_of μ a ecc M0 t)) :=
    perifocal_norm (a := a) (ecc := ecc)
      (E := E_of μ a ecc M0 t) ha.le he.le
  simp only [ellipse, hnorm]

lemma isKeplerOn_ellipse {μ a ecc M0 T : ℝ}
    (hμ : 0 ≤ μ) (ha : 0 < a) (he : |ecc| < 1) :
    IsKeplerOn μ T (ellipse μ a ecc M0) := by
  refine ⟨fun s =>
      ((1 - ecc * Real.cos (E_of μ a ecc M0 s))⁻¹ * Real.sqrt (μ / a ^ 3)) •
        periVel a ecc (E_of μ a ecc M0 s), ?_, ?_, ?_⟩
  · intro t _; exact ellipse_ne_zero ha he
  · intro t _; exact hasDerivAt_ellipse (μ := μ) (a := a) (ecc := ecc)
      (M0 := M0) (t := t) he
  · intro t _ht
    have hn2 : Real.sqrt (μ / a ^ 3) ^ 2 = μ / a ^ 3 :=
      Real.sq_sqrt (div_nonneg hμ (pow_nonneg ha.le 3))
    have hD := D_of_ne (μ := μ) (a := a) (ecc := ecc) (M0 := M0) (t := t) he
    have hc := hasDerivAt_E'_of (μ := μ) (a := a) (ecc := ecc) (M0 := M0) (t := t) he
    have hf := hasDerivAt_periVel_comp_E (μ := μ) (a := a) (ecc := ecc)
      (M0 := M0) (t := t) he
    have hsmul := hc.smul hf
    -- `hsmul` derivative is `c • f' + c' • f`, i.e. accel_vec's LHS.
    have hvec := accel_vec (μ := μ) (a := a) (ecc := ecc)
      (E := E_of μ a ecc M0 t) ha.ne' hD hn2
    have hrhs := kepler_rhs_ellipse (μ := μ) (a := a) (ecc := ecc)
      (M0 := M0) (t := t) ha he
    -- rewrite the Kepler target onto the vis-viva vector identity
    refine hrhs.symm ▸ ?_
    exact hvec ▸ hsmul

lemma isTarget_ellipse {μ a ecc M0 T R₁ R₂ : ℝ}
    (hμ : 0 ≤ μ) (ha : 0 < a) (he : |ecc| < 1)
    (hlo : R₁ ≤ a * (1 - |ecc|)) (hhi : a * (1 + |ecc|) ≤ R₂) :
    IsTarget μ R₁ R₂ T (ellipse μ a ecc M0) :=
  ⟨isKeplerOn_ellipse (T := T) hμ ha he,
    inShell_ellipse (T := T) ha he hlo hhi⟩

/-! Constant SO(3) action preserves Kepler. -/

def applyMat (M : Matrix (Fin 3) (Fin 3) ℝ) (v : Vec) : Vec :=
  WithLp.toLp 2 (M *ᵥ (WithLp.ofLp v))

lemma applyMat_smul (M : Matrix (Fin 3) (Fin 3) ℝ) (c : ℝ) (v : Vec) :
    applyMat M (c • v) = c • applyMat M v := by
  apply (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).injective
  simp [applyMat, Matrix.mulVec_smul]

lemma applyMat_add (M : Matrix (Fin 3) (Fin 3) ℝ) (u v : Vec) :
    applyMat M (u + v) = applyMat M u + applyMat M v := by
  apply (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).injective
  simp [applyMat, Matrix.mulVec_add]

lemma hasDerivAt_applyMat (M : Matrix (Fin 3) (Fin 3) ℝ)
    {x : ℝ → Vec} {x' : Vec} {t : ℝ} (hx : HasDerivAt x x' t) :
    HasDerivAt (fun s => applyMat M (x s)) (applyMat M x') t := by
  let L : Vec →L[ℝ] Vec :=
    { toFun := applyMat M
      map_add' := applyMat_add M
      map_smul' := by
        intro c v
        simpa using applyMat_smul M (c : ℝ) v
      cont := by
        -- continuous as composition of continuous maps
        have : Continuous (fun v : Vec => applyMat M v) := by
          unfold applyMat
          fun_prop
        exact this }
  exact L.hasFDerivAt.comp_hasDerivAt t hx

/-- 6-parameter family: (a, e, M0, yaw, pitch, roll). -/
def eulerR (α β γ : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  let cα := Real.cos α; let sα := Real.sin α
  let cβ := Real.cos β; let sβ := Real.sin β
  let cγ := Real.cos γ; let sγ := Real.sin γ
  !![cα * cβ, cα * sβ * sγ - sα * cγ, cα * sβ * cγ + sα * sγ;
     sα * cβ, sα * sβ * sγ + cα * cγ, sα * sβ * cγ - cα * sγ;
     -sβ,     cβ * sγ,                cβ * cγ]

def family (μ : ℝ) (p : Fin 6 → ℝ) : ℝ → Vec :=
  fun t => applyMat (eulerR (p 3) (p 4) (p 5))
    (ellipse μ (p 0) (p 1) (p 2) t)

/-- The circular-ish base point: a = 5/2, e = 0, M0 = 0, identity rotation. -/
def p0 : Fin 6 → ℝ := ![5 / 2, 0, 0, 0, 0, 0]

lemma eulerR_zero : eulerR 0 0 0 = 1 := by
  simp [eulerR, Matrix.one_fin_three]

lemma applyMat_one (v : Vec) : applyMat (1 : Matrix (Fin 3) (Fin 3) ℝ) v = v := by
  apply (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).injective
  simp [applyMat]

lemma family_p0 (μ t : ℝ) : family μ p0 t = ellipse μ (5 / 2) 0 0 t := by
  simp [family, p0, eulerR_zero, applyMat_one]

def rotX (γ : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![1, 0, 0;
     0, Real.cos γ, -Real.sin γ;
     0, Real.sin γ, Real.cos γ]

def rotY (β : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![Real.cos β, 0, Real.sin β;
     0, 1, 0;
     -Real.sin β, 0, Real.cos β]

def rotZ (α : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![Real.cos α, -Real.sin α, 0;
     Real.sin α, Real.cos α, 0;
     0, 0, 1]

private lemma matrix_eq_one_of_entries {A : Matrix (Fin 3) (Fin 3) ℝ}
    (h00 : A 0 0 = 1) (h01 : A 0 1 = 0) (h02 : A 0 2 = 0)
    (h10 : A 1 0 = 0) (h11 : A 1 1 = 1) (h12 : A 1 2 = 0)
    (h20 : A 2 0 = 0) (h21 : A 2 1 = 0) (h22 : A 2 2 = 1) :
    A = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [h00, h01, h02, h10, h11, h12, h20, h21, h22]

lemma rotX_mul_transpose (γ : ℝ) : (rotX γ)ᵀ * rotX γ = 1 := by
  have hcs : Real.cos γ ^ 2 + Real.sin γ ^ 2 = 1 := Real.cos_sq_add_sin_sq γ
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rotX, Matrix.mul_apply, Fin.sum_univ_three] <;> nlinarith [hcs]

lemma rotY_mul_transpose (β : ℝ) : (rotY β)ᵀ * rotY β = 1 := by
  have hcs : Real.cos β ^ 2 + Real.sin β ^ 2 = 1 := Real.cos_sq_add_sin_sq β
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rotY, Matrix.mul_apply, Fin.sum_univ_three] <;> nlinarith [hcs]

lemma rotZ_mul_transpose (α : ℝ) : (rotZ α)ᵀ * rotZ α = 1 := by
  have hcs : Real.cos α ^ 2 + Real.sin α ^ 2 = 1 := Real.cos_sq_add_sin_sq α
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rotZ, Matrix.mul_apply, Fin.sum_univ_three] <;> nlinarith [hcs]

lemma eulerR_eq_prod (α β γ : ℝ) :
    eulerR α β γ = rotZ α * rotY β * rotX γ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [eulerR, rotX, rotY, rotZ, Matrix.mul_apply, Fin.sum_univ_three] <;> ring

lemma mul_transpose_one_mul {n : Type*} [Fintype n] [DecidableEq n]
    {A B : Matrix n n ℝ} (hA : Aᵀ * A = 1) (hB : Bᵀ * B = 1) :
    (A * B)ᵀ * (A * B) = 1 := by
  calc
    (A * B)ᵀ * (A * B) = Bᵀ * Aᵀ * (A * B) := by rw [Matrix.transpose_mul]
    _ = Bᵀ * (Aᵀ * A * B) := by simp [Matrix.mul_assoc]
    _ = Bᵀ * (1 * B) := by rw [hA]
    _ = Bᵀ * B := by simp
    _ = 1 := hB

lemma eulerR_mul_transpose (α β γ : ℝ) :
    (eulerR α β γ)ᵀ * eulerR α β γ = 1 := by
  rw [eulerR_eq_prod, Matrix.mul_assoc]
  exact mul_transpose_one_mul (rotZ_mul_transpose α)
    (mul_transpose_one_mul (rotY_mul_transpose β) (rotX_mul_transpose γ))

lemma ofLp_applyMat (M : Matrix (Fin 3) (Fin 3) ℝ) (v : Vec) :
    (applyMat M v).ofLp = M *ᵥ v.ofLp :=
  WithLp.ofLp_toLp _ _

lemma applyMat_norm_of_mul_transpose
    {M : Matrix (Fin 3) (Fin 3) ℝ} (h : Mᵀ * M = 1) (v : Vec) :
    ‖applyMat M v‖ = ‖v‖ := by
  have hsq : ‖applyMat M v‖ ^ 2 = ‖v‖ ^ 2 := by
    have hs1 : 0 ≤ ∑ i : Fin 3, (applyMat M v).ofLp i ^ 2 :=
      Finset.sum_nonneg fun _ _ => sq_nonneg _
    have hs2 : 0 ≤ ∑ i : Fin 3, v.ofLp i ^ 2 :=
      Finset.sum_nonneg fun _ _ => sq_nonneg _
    have hn1 : ∑ i : Fin 3, ‖(applyMat M v).ofLp i‖ ^ 2
        = ∑ i : Fin 3, (applyMat M v).ofLp i ^ 2 := by
      simp [Real.norm_eq_abs, sq_abs]
    have hn2 : ∑ i : Fin 3, ‖v.ofLp i‖ ^ 2 = ∑ i : Fin 3, v.ofLp i ^ 2 := by
      simp [Real.norm_eq_abs, sq_abs]
    rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq, hn1, hn2,
      Real.sq_sqrt hs1, Real.sq_sqrt hs2, ofLp_applyMat]
    set x := v.ofLp
    have hdot : (M *ᵥ x) ⬝ᵥ (M *ᵥ x) = x ⬝ᵥ x := by
      rw [dotProduct_mulVec]
      have htr : (M *ᵥ x) ᵥ* M = Mᵀ *ᵥ (M *ᵥ x) :=
        (mulVec_transpose M (M *ᵥ x)).symm
      rw [htr, mulVec_mulVec, h, one_mulVec]
    simpa [dotProduct, pow_two] using hdot
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq

lemma applyMat_norm_euler (α β γ : ℝ) (v : Vec) :
    ‖applyMat (eulerR α β γ) v‖ = ‖v‖ :=
  applyMat_norm_of_mul_transpose (eulerR_mul_transpose α β γ) v

lemma applyMat_kepler {μ T : ℝ} {x : ℝ → Vec}
    (M : Matrix (Fin 3) (Fin 3) ℝ) (hO : ∀ v, ‖applyMat M v‖ = ‖v‖)
    (hx : IsKeplerOn μ T x) :
    IsKeplerOn μ T (fun t => applyMat M (x t)) := by
  obtain ⟨v, hnz, hd1, hd2⟩ := hx
  refine ⟨fun t => applyMat M (v t), ?_, ?_, ?_⟩
  · intro t ht h
    have : ‖x t‖ = 0 := by
      have hz : applyMat M (x t) = 0 := h
      rw [← hO (x t), hz, norm_zero]
    exact hnz t ht (norm_eq_zero.mp this)
  · intro t ht; exact hasDerivAt_applyMat M (hd1 t ht)
  · intro t ht
    have hder := hasDerivAt_applyMat M (hd2 t ht)
    have hvec :
        applyMat M (-(μ / ‖x t‖ ^ 3) • x t)
          = -(μ / ‖applyMat M (x t)‖ ^ 3) • applyMat M (x t) := by
      rw [applyMat_smul, hO]
    exact hvec ▸ hder

lemma inShell_applyMat {R₁ R₂ T : ℝ} {x : ℝ → Vec}
    (M : Matrix (Fin 3) (Fin 3) ℝ) (hO : ∀ v, ‖applyMat M v‖ = ‖v‖)
    (hx : InShell R₁ R₂ T x) :
    InShell R₁ R₂ T (fun t => applyMat M (x t)) := by
  intro t ht
  simpa [hO] using hx t ht

lemma isTarget_family {μ T R₁ R₂ : ℝ} {p : Fin 6 → ℝ}
    (hμ : 0 ≤ μ) (ha : 0 < p 0) (he : |p 1| < 1)
    (hlo : R₁ ≤ p 0 * (1 - |p 1|)) (hhi : p 0 * (1 + |p 1|) ≤ R₂) :
    IsTarget μ R₁ R₂ T (family μ p) := by
  have hx : IsTarget μ R₁ R₂ T (ellipse μ (p 0) (p 1) (p 2)) :=
    isTarget_ellipse (T := T) hμ ha he hlo hhi
  unfold family
  exact ⟨applyMat_kepler (M := eulerR (p 3) (p 4) (p 5))
      (applyMat_norm_euler (p 3) (p 4) (p 5)) hx.1,
    inShell_applyMat (M := eulerR (p 3) (p 4) (p 5))
      (applyMat_norm_euler (p 3) (p 4) (p 5)) hx.2⟩

/-- Partial IFT: `E` as a C¹ function of mean anomaly at fixed eccentricity. -/
lemma hasDerivAt_E_mean {ecc M : ℝ} (he : |ecc| < 1) :
    HasDerivAt (eccentricAnomaly ecc)
      (1 - ecc * Real.cos (eccentricAnomaly ecc M))⁻¹ M :=
  hasDerivAt_eccentricAnomaly he

/-! Bivariate Kepler inverse: `∂E/∂e` via the implicit function theorem. -/

def keplerF (e E : ℝ) : ℝ := E - e * Real.sin E

lemma hasDerivAt_keplerF_fst (e E : ℝ) :
    HasDerivAt (fun x => keplerF x E) (-Real.sin E) e := by
  change HasDerivAt ((fun _ : ℝ => E) - fun x => x * Real.sin E) (-Real.sin E) e
  have h0 := (hasDerivAt_const e E).sub ((hasDerivAt_id e).mul_const (Real.sin E))
  have hderiv : (0 - 1 * Real.sin E) = -Real.sin E := by ring
  exact hderiv ▸ h0

lemma hasFDerivAt_keplerF_fst (e E : ℝ) :
    HasFDerivAt (fun x => keplerF x E)
      (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (-Real.sin E)) e :=
  (hasDerivAt_keplerF_fst e E).hasFDerivAt

lemma hasFDerivAt_keplerF_snd (e E : ℝ) :
    HasFDerivAt (fun y => keplerF e y)
      (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (1 - e * Real.cos E)) E :=
  (hasDerivAt_keplerMap e E).hasFDerivAt

lemma continuous_smulRight_scalar :
    Continuous (fun c : ℝ => ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) c) :=
  (ContinuousLinearMap.smulRightL ℝ ℝ ℝ (1 : ℝ →L[ℝ] ℝ)).continuous

lemma continuousAt_keplerF_fderiv_fst (u : ℝ × ℝ) :
    ContinuousAt (fun v : ℝ × ℝ =>
      ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (-Real.sin v.2)) u :=
  (continuous_smulRight_scalar.comp
    (continuous_neg.comp (Real.continuous_sin.comp continuous_snd))).continuousAt

lemma continuousAt_keplerF_fderiv_snd (u : ℝ × ℝ) :
    ContinuousAt (fun v : ℝ × ℝ =>
      ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (1 - v.1 * Real.cos v.2)) u :=
  (continuous_smulRight_scalar.comp
    (continuous_const.sub
      (continuous_fst.mul (Real.continuous_cos.comp continuous_snd)))).continuousAt

lemma smulRight_id_isInvertible {c : ℝ} (hc : c ≠ 0) :
    (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) c).IsInvertible :=
  ContinuousLinearMap.IsInvertible.of_inverse
    (g := ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) c⁻¹)
    (by ext; simp; field_simp [hc])
    (by ext; simp; field_simp [hc])

lemma smulRight_id_inverse_apply {c : ℝ} (hc : c ≠ 0) (y : ℝ) :
    (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) c).inverse y = c⁻¹ * y := by
  have hf : ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) c ∘L
      ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) c⁻¹
      = ContinuousLinearMap.id ℝ ℝ := by
    ext; simp; field_simp [hc]
  have hg : ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) c⁻¹ ∘L
      ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) c
      = ContinuousLinearMap.id ℝ ℝ := by
    ext; simp; field_simp [hc]
  rw [ContinuousLinearMap.inverse_eq hf hg]
  simp [mul_comm]

/-- Implicit `∂E/∂e` at fixed mean anomaly. -/
lemma hasDerivAt_eccentricAnomaly_ecc {ecc M : ℝ} (he : |ecc| < 1) :
    HasDerivAt (fun e => eccentricAnomaly e M)
      (Real.sin (eccentricAnomaly ecc M)
        / (1 - ecc * Real.cos (eccentricAnomaly ecc M))) ecc := by
  set E0 := eccentricAnomaly ecc M
  set D := 1 - ecc * Real.cos E0
  have hD : D ≠ 0 := (keplerMap_deriv_pos (E := E0) he).ne'
  let f1 : ℝ → ℝ → ℝ →L[ℝ] ℝ :=
    fun _ y => ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (-Real.sin y)
  let f2 : ℝ → ℝ → ℝ →L[ℝ] ℝ :=
    fun x y => ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (1 - x * Real.cos y)
  have df1 : ∀ᶠ v : ℝ × ℝ in 𝓝 (ecc, E0),
      HasFDerivAt (fun x => keplerF x v.2) (f1 v.1 v.2) v.1 :=
    Eventually.of_forall fun v => hasFDerivAt_keplerF_fst v.1 v.2
  have df2 : ∀ᶠ v : ℝ × ℝ in 𝓝 (ecc, E0),
      HasFDerivAt (fun y => keplerF v.1 y) (f2 v.1 v.2) v.2 :=
    Eventually.of_forall fun v => hasFDerivAt_keplerF_snd v.1 v.2
  have cf1 : ContinuousAt (Function.uncurry f1) (ecc, E0) :=
    continuousAt_keplerF_fderiv_fst (ecc, E0)
  have cf2 : ContinuousAt (Function.uncurry f2) (ecc, E0) :=
    continuousAt_keplerF_fderiv_snd (ecc, E0)
  have if2 : (f2 ecc E0).IsInvertible := smulRight_id_isInvertible hD
  set ψ := implicitFunctionOfBivariate (f := keplerF) (f₁ := f1) (f₂ := f2)
    df1 df2 cf1 cf2 if2
  have hψ := hasStrictFDerivAt_implicitFunctionOfBivariate
    (f := keplerF) (f₁ := f1) (f₂ := f2) df1 df2 cf1 cf2 if2
  have hval :
      (-(f2 ecc E0).inverse ∘L f1 ecc E0) 1 = Real.sin E0 / D := by
    change (-(ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) D).inverse ∘L
      ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (-Real.sin E0)) 1
      = Real.sin E0 / D
    simp [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smulRight_apply,
      smul_eq_mul, mul_neg]
    rw [smulRight_id_inverse_apply hD]
    field_simp [hD]
  have hψderiv : HasDerivAt ψ (Real.sin E0 / D) ecc :=
    hval ▸ hψ.hasFDerivAt.hasDerivAt
  have hagree : ∀ᶠ e in 𝓝 ecc, ψ e = eccentricAnomaly e M := by
    have hψeq := eventually_apply_implicitFunctionOfBivariate
      (f := keplerF) (f₁ := f1) (f₂ := f2) df1 df2 cf1 cf2 if2
    have hnh : ∀ᶠ e : ℝ in 𝓝 ecc, |e| < 1 :=
      (continuous_abs.continuousAt (x := ecc)).preimage_mem_nhds (Iio_mem_nhds he)
    filter_upwards [hψeq, hnh] with e heq hlt
    have hM : keplerF ecc E0 = M := by
      simpa [keplerF, keplerMap, E0] using keplerMap_eccentricAnomaly he
    have hψM : keplerF e (ψ e) = M := heq.trans hM
    have hEM : keplerMap e (eccentricAnomaly e M) = M :=
      keplerMap_eccentricAnomaly hlt
    have : keplerMap e (ψ e) = keplerMap e (eccentricAnomaly e M) := by
      simpa [keplerMap, keplerF] using hψM.trans hEM.symm
    exact (keplerMap_strictMono hlt).injective this
  have hEq : (fun e => eccentricAnomaly e M) =ᶠ[𝓝 ecc] ψ :=
    hagree.mono fun _ h => h.symm
  exact hψderiv.congr_of_eventuallyEq hEq

/-! The 6×6 t²/t³ line-of-sight jet against Cartesian ICs.

At the circular instance the target is `r(0)=(5/2,0,0)`,
`v(0)=(0,√10/5,0)` (Kepler with `μ=1`).  Higher time derivatives of
`r` are algebraic in `(r,v)` via `r''=-(μ/‖r‖³)•r`.  The observer is
the unit circle.  Rows of `jetMatrix` are the t² and t³ Taylor
coefficients of `los` (x,y,z); columns are `∂/∂(x,y,z,vx,vy,vz)`.
The matrix is permutation-equivalent to three 2×2 blocks, so its
determinant is their product. -/

def jetA : ℝ := 56 / 135 - 16 * Real.sqrt 10 / 135
def jetB : ℝ := 4 / 9 - 4 * Real.sqrt 10 / 45
def jetC : ℝ := -934 / 1125 + 8 * Real.sqrt 10 / 45
def jetD : ℝ := -1402 / 3375 + 8 * Real.sqrt 10 / 135
def jetE : ℝ := -3338 / 3375 + 4304 * Real.sqrt 10 / 16875
def jetF : ℝ := -3194 / 3375 + 20944 * Real.sqrt 10 / 84375
def jetG : ℝ := -102 / 125 + 8 * Real.sqrt 10 / 45
def jetH : ℝ := -1354 / 3375 + 8 * Real.sqrt 10 / 135

/-- Linearized t²/t³ los-jet vs Cartesian ICs at the circular instance. -/
def jetMatrix : Matrix (Fin 6) (Fin 6) ℝ :=
  !![jetA, 0, 0, 0, jetB, 0;
     0, jetC, 0, jetB, 0, 0;
     0, 0, jetD, 0, 0, 0;
     0, jetE, 0, jetA, 0, 0;
     jetF, 0, 0, 0, jetG, 0;
     0, 0, 0, 0, 0, jetH]

/-- Reorder to the three 2×2 blocks
`(z,vz)`, `(x,vy)`, `(y,vx)`.  Same permutation on rows and columns. -/
def jetReorder : Fin 6 ≃ Fin 6 where
  toFun i := ![ (2 : Fin 6), 5, 0, 4, 1, 3 ] i
  invFun j := ![ (2 : Fin 6), 4, 0, 5, 3, 1 ] j
  left_inv i := by fin_cases i <;> simp
  right_inv j := by fin_cases j <;> simp

lemma jetMatrix_submatrix_00 :
    (jetMatrix.submatrix jetReorder jetReorder) 0 0 = jetD := by
  simp [jetMatrix, jetReorder]

lemma jetMatrix_submatrix_11 :
    (jetMatrix.submatrix jetReorder jetReorder) 1 1 = jetH := by
  simp [jetMatrix, jetReorder]

lemma sqrt10_sq : Real.sqrt 10 ^ 2 = 10 :=
  Real.sq_sqrt (by norm_num)

lemma jet_block_AG :
    jetA * jetG - jetB * jetF = 8 * (971 - 253 * Real.sqrt 10) / 84375 := by
  unfold jetA jetB jetF jetG
  field_simp
  ring_nf
  simp [pow_two]
  ring

lemma jet_block_CA :
    jetC * jetA - jetB * jetE = 8 * (2111 - 553 * Real.sqrt 10) / 151875 := by
  unfold jetA jetB jetC jetE
  field_simp
  ring_nf
  simp [pow_two]
  ring

lemma jetD_eq : jetD = 2 * (-701 + 100 * Real.sqrt 10) / 3375 := by
  unfold jetD
  field_simp
  ring

lemma jetH_eq : jetH = 2 * (-677 + 100 * Real.sqrt 10) / 3375 := by
  unfold jetH
  field_simp
  ring

lemma jet_block_AG_ne : 971 - 253 * Real.sqrt 10 ≠ 0 := by
  have ha : (0 : ℝ) < 971 := by norm_num
  have hb : (0 : ℝ) < 253 := by norm_num
  have hsq : (253 : ℝ) ^ 2 * 10 < (971 : ℝ) ^ 2 := by norm_num
  have hlt := sqrt_mul_lt_of_sq ha hb hsq
  linarith

lemma jet_block_CA_ne : 2111 - 553 * Real.sqrt 10 ≠ 0 := by
  have ha : (0 : ℝ) < 2111 := by norm_num
  have hb : (0 : ℝ) < 553 := by norm_num
  have hsq : (553 : ℝ) ^ 2 * 10 < (2111 : ℝ) ^ 2 := by norm_num
  have hlt := sqrt_mul_lt_of_sq ha hb hsq
  linarith

lemma jetD_ne : jetD ≠ 0 := by
  rw [jetD_eq]
  refine div_ne_zero (mul_ne_zero (by norm_num) ?_) (by norm_num)
  have ha : (0 : ℝ) < 701 := by norm_num
  have hb : (0 : ℝ) < 100 := by norm_num
  have hsq : (100 : ℝ) ^ 2 * 10 < (701 : ℝ) ^ 2 := by norm_num
  have hlt := sqrt_mul_lt_of_sq ha hb hsq
  linarith

lemma jetH_ne : jetH ≠ 0 := by
  rw [jetH_eq]
  exact div_ne_zero (mul_ne_zero (by norm_num) jet_factor_ne) (by norm_num)

lemma jet_simple_factor_ne :
    (3457543340567 - 1090652821342 * Real.sqrt 10 : ℝ) ≠ 0 := by
  have ha : (0 : ℝ) < 3457543340567 := by norm_num
  have hb : (0 : ℝ) < 1090652821342 := by norm_num
  have hsq : (1090652821342 : ℝ) ^ 2 * 10
      < (3457543340567 : ℝ) ^ 2 := by norm_num
  have hlt := sqrt_mul_lt_of_sq ha hb hsq
  linarith

/-- Product of the three 2×2 block determinants. -/
lemma jet_block_prod :
    jetD * jetH * (jetA * jetG - jetB * jetF) * (jetC * jetA - jetB * jetE)
      = 256 * (3457543340567 - 1090652821342 * Real.sqrt 10)
        / 145964630126953125 := by
  rw [jetD_eq, jetH_eq, jet_block_AG, jet_block_CA]
  field_simp
  ring_nf
  have hs2 : Real.sqrt 10 ^ 2 = 10 := sqrt10_sq
  have hs3 : Real.sqrt 10 ^ 3 = 10 * Real.sqrt 10 := by
    rw [pow_succ, hs2]
  have hs4 : Real.sqrt 10 ^ 4 = 100 := by
    rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, hs2]; norm_num
  simp [hs2, hs3, hs4]
  ring

def jetBlk2 : Matrix (Fin 2) (Fin 2) ℝ :=
  !![jetD, 0; 0, jetH]

def jetBlk4a : Matrix (Fin 2) (Fin 2) ℝ :=
  !![jetA, jetB; jetF, jetG]

def jetBlk4b : Matrix (Fin 2) (Fin 2) ℝ :=
  !![jetC, jetB; jetE, jetA]

def jetBlk4sum : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℝ :=
  Matrix.fromBlocks jetBlk4a 0 0 jetBlk4b

def jetBlk4 : Matrix (Fin 4) (Fin 4) ℝ :=
  Matrix.reindex finSumFinEquiv finSumFinEquiv jetBlk4sum

def jetBlk6 : Matrix (Fin 2 ⊕ Fin 4) (Fin 2 ⊕ Fin 4) ℝ :=
  Matrix.fromBlocks jetBlk2 0 0 jetBlk4

lemma jetBlk2_det : jetBlk2.det = jetD * jetH := by
  simp [jetBlk2, Matrix.det_fin_two]

lemma jetBlk4a_det : jetBlk4a.det = jetA * jetG - jetB * jetF := by
  simp [jetBlk4a, Matrix.det_fin_two]

lemma jetBlk4b_det : jetBlk4b.det = jetC * jetA - jetB * jetE := by
  simp [jetBlk4b, Matrix.det_fin_two]

lemma jetBlk4_det :
    jetBlk4.det = (jetA * jetG - jetB * jetF) * (jetC * jetA - jetB * jetE) := by
  rw [jetBlk4, Matrix.det_reindex_self, jetBlk4sum, Matrix.det_fromBlocks_zero₁₂,
    jetBlk4a_det, jetBlk4b_det]

lemma jetBlk6_det :
    jetBlk6.det
      = jetD * jetH * (jetA * jetG - jetB * jetF)
        * (jetC * jetA - jetB * jetE) := by
  rw [jetBlk6, Matrix.det_fromBlocks_zero₁₂, jetBlk2_det, jetBlk4_det]
  ring

def jetReordered : Matrix (Fin 6) (Fin 6) ℝ :=
  !![jetD, 0, 0, 0, 0, 0;
     0, jetH, 0, 0, 0, 0;
     0, 0, jetA, jetB, 0, 0;
     0, 0, jetF, jetG, 0, 0;
     0, 0, 0, 0, jetC, jetB;
     0, 0, 0, 0, jetE, jetA]

lemma jetMatrix_submatrix_eq_reordered :
    jetMatrix.submatrix jetReorder jetReorder = jetReordered := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [jetMatrix, jetReorder, jetReordered]

lemma fin6_cast0 : (0 : Fin 6) = Fin.castAdd 4 (0 : Fin 2) := rfl
lemma fin6_cast1 : (1 : Fin 6) = Fin.castAdd 4 (1 : Fin 2) := rfl
lemma fin6_nat2 : (2 : Fin 6) = Fin.natAdd 2 (0 : Fin 4) := rfl
lemma fin6_nat3 : (3 : Fin 6) = Fin.natAdd 2 (1 : Fin 4) := rfl
lemma fin6_nat4 : (4 : Fin 6) = Fin.natAdd 2 (2 : Fin 4) := rfl
lemma fin6_nat5 : (5 : Fin 6) = Fin.natAdd 2 (3 : Fin 4) := rfl

lemma fin4_cast0 : (0 : Fin 4) = Fin.castAdd 2 (0 : Fin 2) := rfl
lemma fin4_cast1 : (1 : Fin 4) = Fin.castAdd 2 (1 : Fin 2) := rfl
lemma fin4_nat2 : (2 : Fin 4) = Fin.natAdd 2 (0 : Fin 2) := rfl
lemma fin4_nat3 : (3 : Fin 4) = Fin.natAdd 2 (1 : Fin 2) := rfl

lemma symm6_0 : (finSumFinEquiv (m := 2) (n := 4)).symm (0 : Fin 6) = Sum.inl 0 := by
  rw [fin6_cast0, finSumFinEquiv_symm_apply_castAdd]
lemma symm6_1 : (finSumFinEquiv (m := 2) (n := 4)).symm (1 : Fin 6) = Sum.inl 1 := by
  rw [fin6_cast1, finSumFinEquiv_symm_apply_castAdd]
lemma symm6_2 : (finSumFinEquiv (m := 2) (n := 4)).symm (2 : Fin 6) = Sum.inr 0 := by
  rw [fin6_nat2, finSumFinEquiv_symm_apply_natAdd]
lemma symm6_3 : (finSumFinEquiv (m := 2) (n := 4)).symm (3 : Fin 6) = Sum.inr 1 := by
  rw [fin6_nat3, finSumFinEquiv_symm_apply_natAdd]
lemma symm6_4 : (finSumFinEquiv (m := 2) (n := 4)).symm (4 : Fin 6) = Sum.inr 2 := by
  rw [fin6_nat4, finSumFinEquiv_symm_apply_natAdd]
lemma symm6_5 : (finSumFinEquiv (m := 2) (n := 4)).symm (5 : Fin 6) = Sum.inr 3 := by
  rw [fin6_nat5, finSumFinEquiv_symm_apply_natAdd]

lemma symm4_0 : (finSumFinEquiv (m := 2) (n := 2)).symm (0 : Fin 4) = Sum.inl 0 := by
  rw [fin4_cast0, finSumFinEquiv_symm_apply_castAdd]
lemma symm4_1 : (finSumFinEquiv (m := 2) (n := 2)).symm (1 : Fin 4) = Sum.inl 1 := by
  rw [fin4_cast1, finSumFinEquiv_symm_apply_castAdd]
lemma symm4_2 : (finSumFinEquiv (m := 2) (n := 2)).symm (2 : Fin 4) = Sum.inr 0 := by
  rw [fin4_nat2, finSumFinEquiv_symm_apply_natAdd]
lemma symm4_3 : (finSumFinEquiv (m := 2) (n := 2)).symm (3 : Fin 4) = Sum.inr 1 := by
  rw [fin4_nat3, finSumFinEquiv_symm_apply_natAdd]

lemma jetReordered_eq_reindex :
    jetReordered = Matrix.reindex finSumFinEquiv finSumFinEquiv jetBlk6 := by
  ext i j
  rw [Matrix.reindex_apply, Matrix.submatrix_apply]
  fin_cases i <;> fin_cases j <;>
    simp [jetReordered, jetBlk6, jetBlk4, jetBlk4sum, jetBlk2, jetBlk4a, jetBlk4b,
      symm6_0, symm6_1, symm6_2, symm6_3, symm6_4, symm6_5,
      symm4_0, symm4_1, symm4_2, symm4_3,
      Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
      Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂,
      Matrix.reindex_apply, Matrix.submatrix_apply]

lemma jetReorder_eq_reindex :
    jetMatrix.submatrix jetReorder jetReorder
      = Matrix.reindex finSumFinEquiv finSumFinEquiv jetBlk6 := by
  rw [jetMatrix_submatrix_eq_reordered, jetReordered_eq_reindex]

lemma jetMatrix_det_eq_blocks :
    jetMatrix.det
      = jetD * jetH * (jetA * jetG - jetB * jetF)
        * (jetC * jetA - jetB * jetE) := by
  have h1 := Matrix.det_submatrix_equiv_self (A := jetMatrix) jetReorder
  have h2 : (jetMatrix.submatrix jetReorder jetReorder).det = jetBlk6.det := by
    rw [jetReorder_eq_reindex, Matrix.det_reindex_self]
  rw [← h1, h2, jetBlk6_det]

/-- In-kernel determinant of the Cartesian t²/t³ los-jet. -/
lemma jetMatrix_det :
    jetMatrix.det
      = 256 * (3457543340567 - 1090652821342 * Real.sqrt 10)
        / 145964630126953125 := by
  rw [jetMatrix_det_eq_blocks, jet_block_prod]

lemma jetMatrix_det_ne_zero : jetMatrix.det ≠ 0 := by
  rw [jetMatrix_det]
  refine div_ne_zero ?_ (by norm_num)
  exact mul_ne_zero (by norm_num) jet_simple_factor_ne

/-! Second-difference linearity and RecoveredBy packing. -/

lemma secondDiff_sub (f g : ℝ → Vec) (h : ℝ) :
    secondDiff (fun t => f t - g t) h = secondDiff f h - secondDiff g h := by
  ext i
  simp [secondDiff, PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  ring

lemma not_both_recovered
    {e : ℝ → Vec} {ε T h : ℝ} {ξ x y : ℝ → Vec}
    (hT : 2 * h ∈ Set.Icc (0 : ℝ) T)
    (hsep : 8 * ε < ‖secondDiff (fun t => los e x t - los e y t) h‖)
    (hx : RecoveredBy e ε T ξ x) (hy : RecoveredBy e ε T ξ y) : False := by
  have hx' := recoveredBy_secondDiff hT hx
  have hy' := recoveredBy_secondDiff hT hy
  have hlin :
      secondDiff (fun t => los e x t - los e y t) h =
        secondDiff (fun t => los e x t - los e ξ t) h
        - secondDiff (fun t => los e y t - los e ξ t) h := by
    ext i
    simp [secondDiff, PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    ring
  have : ‖secondDiff (fun t => los e x t - los e y t) h‖ ≤ 8 * ε := by
    rw [hlin]
    exact (norm_sub_le _ _).trans (by linarith [hx', hy'])
  linarith

lemma not_both_recovered_two
    {e : ℝ → Vec} {ε T h₁ h₂ : ℝ} {ξ x y : ℝ → Vec}
    (hT₁ : 2 * h₁ ∈ Set.Icc (0 : ℝ) T)
    (hT₂ : 2 * h₂ ∈ Set.Icc (0 : ℝ) T)
    (hsep : 16 * ε <
      ‖secondDiff (fun t => los e x t - los e y t) h₁‖ +
        ‖secondDiff (fun t => los e x t - los e y t) h₂‖)
    (hx : RecoveredBy e ε T ξ x) (hy : RecoveredBy e ε T ξ y) : False := by
  have hx1 := recoveredBy_secondDiff hT₁ hx
  have hy1 := recoveredBy_secondDiff hT₁ hy
  have hx2 := recoveredBy_secondDiff hT₂ hx
  have hy2 := recoveredBy_secondDiff hT₂ hy
  have hlin1 :
      secondDiff (fun t => los e x t - los e y t) h₁ =
        secondDiff (fun t => los e x t - los e ξ t) h₁
        - secondDiff (fun t => los e y t - los e ξ t) h₁ := by
    ext i
    simp [secondDiff, PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    ring
  have hlin2 :
      secondDiff (fun t => los e x t - los e y t) h₂ =
        secondDiff (fun t => los e x t - los e ξ t) h₂
        - secondDiff (fun t => los e y t - los e ξ t) h₂ := by
    ext i
    simp [secondDiff, PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    ring
  have b1 : ‖secondDiff (fun t => los e x t - los e y t) h₁‖ ≤ 8 * ε := by
    rw [hlin1]; exact (norm_sub_le _ _).trans (by linarith [hx1, hy1])
  have b2 : ‖secondDiff (fun t => los e x t - los e y t) h₂‖ ≤ 8 * ε := by
    rw [hlin2]; exact (norm_sub_le _ _).trans (by linarith [hx2, hy2])
  linarith

lemma packing_eps5_unbounded_scaled
    {ι : Type*} (S : ℝ → Set ι) {c : ℝ} (hc : 0 < c)
    (hlb : ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 2 →
      ((S ε).ncard : ℝ) ≥ (c / ε) ^ 6) :
    ¬ ∃ C : ℝ, ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 2 → ((S ε).ncard : ℝ) * ε ^ 5 ≤ C := by
  intro ⟨C, hC⟩
  let ε : ℝ := min (1 / 2) (c ^ 6 / (2 * (|C| + 1)))
  have hC1 : 0 < |C| + 1 := by positivity
  have hc6 : 0 < c ^ 6 := pow_pos hc 6
  have hεpos : 0 < ε := by
    have : 0 < c ^ 6 / (2 * (|C| + 1)) := by positivity
    exact lt_min (by norm_num) this
  have hεle : ε ≤ 1 / 2 := min_le_left _ _
  have hlb' := hlb ε hεpos hεle
  have hprod := hC ε hεpos hεle
  have hge0 : ((S ε).ncard : ℝ) * ε ^ 5 ≥ (c / ε) ^ 6 * ε ^ 5 := by gcongr
  have hsimp : (c / ε) ^ 6 * ε ^ 5 = c ^ 6 / ε := by
    field_simp [hεpos.ne']
  have hge : ((S ε).ncard : ℝ) * ε ^ 5 ≥ c ^ 6 / ε := by
    rw [← hsimp]; exact hge0
  have hεsmall : ε ≤ c ^ 6 / (2 * (|C| + 1)) := min_le_right _ _
  have hδ : 0 < c ^ 6 / (2 * (|C| + 1)) := by positivity
  have hineq : 2 * (|C| + 1) / c ^ 6 ≤ 1 / ε := by
    have := (one_div_le_one_div hδ hεpos).mpr hεsmall
    simpa [one_div_div] using this
  have hbig : 2 * (|C| + 1) ≤ c ^ 6 / ε := by
    have hc6n : c ^ 6 ≠ 0 := hc6.ne'
    have hεn : ε ≠ 0 := hεpos.ne'
    rw [div_le_div_iff₀ hc6 hεpos] at hineq
    -- hineq : 2(|C|+1) * ε ≤ c^6 * 1
    have : 2 * (|C| + 1) * ε ≤ c ^ 6 := by
      simpa [mul_one] using hineq
    rw [le_div_iff₀ hεpos]
    simpa [mul_comm] using this
  have hchain : 2 * (|C| + 1) ≤ C :=
    hbig.trans ((ge_iff_le.mp hge).trans hprod)
  nlinarith [le_abs_self C, abs_nonneg C, neg_le_abs C]

def pStar : Fin 6 → ℝ := ![5 / 2, (1 / 10 : ℝ), 0, 0, 0, 0]

lemma pStar_target (T : ℝ) :
    IsTarget (1 : ℝ) 2 3 T (family 1 pStar) :=
  isTarget_family (μ := 1) (T := T) (R₁ := 2) (R₂ := 3) (p := pStar)
    (by norm_num)
    (by norm_num [pStar])
    (by norm_num [pStar])
    (by norm_num [pStar])
    (by norm_num [pStar])

def hSD1 : ℝ := 1 / 4
def hSD2 : ℝ := 1 / 2

lemma hSD1_window : 2 * hSD1 ∈ Set.Icc (0 : ℝ) 1 := by
  unfold hSD1; norm_num

lemma hSD2_window : 2 * hSD2 ∈ Set.Icc (0 : ℝ) 1 := by
  unfold hSD2; norm_num

/-- Box radius around `pStar` that stays in the shell `[2, 3]`. -/
def packRadius : ℝ := 1 / 40

lemma packBox_target (T : ℝ) {p : Fin 6 → ℝ}
    (hp : ∀ i, |p i - pStar i| ≤ packRadius) :
    IsTarget (1 : ℝ) 2 3 T (family 1 p) := by
  have ha : 0 < p 0 := by
    have := hp 0
    have : |p 0 - 5 / 2| ≤ 1 / 40 := by simpa [pStar, packRadius] using this
    nlinarith [le_abs_self (p 0 - 5 / 2), neg_le_abs (p 0 - 5 / 2)]
  have he : |p 1| < 1 := by
    have := hp 1
    have : |p 1 - 1 / 10| ≤ 1 / 40 := by simpa [pStar, packRadius] using this
    have : |p 1| ≤ |p 1 - 1 / 10| + |(1 / 10 : ℝ)| := by simpa using abs_sub_le (p 1) (1 / 10 : ℝ) 0
    nlinarith
  have hlo : (2 : ℝ) ≤ p 0 * (1 - |p 1|) := by
    have h0 := hp 0
    have h1 := hp 1
    have ha' : |p 0 - 5 / 2| ≤ 1 / 40 := by simpa [pStar, packRadius] using h0
    have he' : |p 1 - 1 / 10| ≤ 1 / 40 := by simpa [pStar, packRadius] using h1
    have hp0 : 5 / 2 - 1 / 40 ≤ p 0 := by nlinarith [neg_le_abs (p 0 - 5 / 2)]
    have hp1 : |p 1| ≤ 1 / 10 + 1 / 40 := by
      have : |p 1| ≤ |p 1 - 1 / 10| + |(1 / 10 : ℝ)| := by simpa using abs_sub_le (p 1) (1 / 10 : ℝ) 0
      nlinarith [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 10)]
    have : (5 / 2 - 1 / 40) * (1 - (1 / 10 + 1 / 40)) ≤ p 0 * (1 - |p 1|) := by
      have hnn : 0 ≤ 1 - |p 1| := by nlinarith
      have hnn' : 0 ≤ 5 / 2 - 1 / 40 := by norm_num
      nlinarith [hp0]
    nlinarith
  have hhi : p 0 * (1 + |p 1|) ≤ 3 := by
    have h0 := hp 0
    have h1 := hp 1
    have ha' : |p 0 - 5 / 2| ≤ 1 / 40 := by simpa [pStar, packRadius] using h0
    have he' : |p 1 - 1 / 10| ≤ 1 / 40 := by simpa [pStar, packRadius] using h1
    have hp0 : p 0 ≤ 5 / 2 + 1 / 40 := by nlinarith [le_abs_self (p 0 - 5 / 2)]
    have hp1 : |p 1| ≤ 1 / 10 + 1 / 40 := by
      have : |p 1| ≤ |p 1 - 1 / 10| + |(1 / 10 : ℝ)| := by simpa using abs_sub_le (p 1) (1 / 10 : ℝ) 0
      nlinarith [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 10)]
    nlinarith
  exact isTarget_family (μ := 1) (T := T) (R₁ := 2) (R₂ := 3) (p := p)
    (by norm_num) ha he hlo hhi

/-- Integer lattice in the 6-parameter box. -/
def gridPt (n : ℕ) (δ : ℝ) (u : Fin 6 → Fin n) : Fin 6 → ℝ :=
  fun i => pStar i + δ * (((u i : ℕ) : ℝ) - ((n : ℝ) - 1) / 2)

lemma gridPt_mem_box {n : ℕ} {δ : ℝ} (hn : 0 < n)
    (hδ : 0 ≤ δ) (hbd : δ * ((n : ℝ) - 1) / 2 ≤ packRadius)
    (u : Fin 6 → Fin n) (i : Fin 6) :
    |gridPt n δ u i - pStar i| ≤ packRadius := by
  simp only [gridPt, add_sub_cancel_left, abs_mul]
  have habs : |δ| = δ := abs_of_nonneg hδ
  rw [habs]
  have hidx : |((u i : ℕ) : ℝ) - ((n : ℝ) - 1) / 2| ≤ ((n : ℝ) - 1) / 2 := by
    have hu : (u i : ℕ) < n := (u i).isLt
    have hu0 : (0 : ℝ) ≤ (u i : ℕ) := Nat.cast_nonneg _
    have hun : ((u i : ℕ) : ℝ) ≤ (n : ℝ) - 1 := by
      have : (u i : ℕ) ≤ n - 1 := Nat.le_pred_of_lt hu
      have hn1 : (1 : ℝ) ≤ n := Nat.one_le_cast.mpr (Nat.succ_le_of_lt hn)
      exact (Nat.cast_le.mpr this).trans_eq (by
        cases n with
        | zero => exact (lt_irrefl _ hn).elim
        | succ n =>
          simp [Nat.cast_succ])
    have hhalf : 0 ≤ ((n : ℝ) - 1) / 2 := by
      have : 1 ≤ (n : ℝ) := Nat.one_le_cast.mpr (Nat.succ_le_of_lt hn)
      linarith
    exact abs_sub_le_iff.2 ⟨by linarith, by linarith⟩
  have : δ * |((u i : ℕ) : ℝ) - ((n : ℝ) - 1) / 2| ≤ δ * (((n : ℝ) - 1) / 2) := by
    gcongr
  have : δ * (((n : ℝ) - 1) / 2) = δ * ((n : ℝ) - 1) / 2 := by ring
  nlinarith

lemma gridPt_target (T : ℝ) {n : ℕ} {δ : ℝ} (hn : 0 < n)
    (hδ : 0 ≤ δ) (hbd : δ * ((n : ℝ) - 1) / 2 ≤ packRadius)
    (u : Fin 6 → Fin n) :
    IsTarget (1 : ℝ) 2 3 T (family 1 (gridPt n δ u)) :=
  packBox_target T (gridPt_mem_box hn hδ hbd u)

lemma ncard_grid (n : ℕ) :
    (Set.univ : Set (Fin 6 → Fin n)).ncard = n ^ 6 := by
  rw [Set.ncard_univ, Nat.card_fun, Nat.card_fin, Nat.card_fin]

lemma gridPt_injective {n : ℕ} {δ : ℝ} (hδ : 0 < δ) {u v : Fin 6 → Fin n}
    (h : gridPt n δ u = gridPt n δ v) : u = v := by
  funext i
  have hcongr := congrArg (fun f : Fin 6 → ℝ => f i) h
  -- gridPt i = pStar i + δ * (↑↑(u i) - (↑n-1)/2)
  simp only [gridPt] at hcongr
  have : δ * (((u i : ℕ) : ℝ) - ((n : ℝ) - 1) / 2) =
      δ * (((v i : ℕ) : ℝ) - ((n : ℝ) - 1) / 2) := by linarith
  have hδ0 : δ ≠ 0 := hδ.ne'
  have : ((u i : ℕ) : ℝ) - ((n : ℝ) - 1) / 2 =
      ((v i : ℕ) : ℝ) - ((n : ℝ) - 1) / 2 := by
    apply mul_left_cancel₀ hδ0
    exact this
  have : ((u i : ℕ) : ℝ) = ((v i : ℕ) : ℝ) := by linarith
  exact Fin.ext (Nat.cast_injective this)

lemma exhaustive_ncard_ge_packing
    {μ R₁ R₂ T ε h : ℝ} {e : ℝ → Vec} {P S : Set (ℝ → Vec)}
    (hT : 2 * h ∈ Set.Icc (0 : ℝ) T)
    (hSfin : S.Finite)
    (hP : ∀ x ∈ P, IsTarget μ R₁ R₂ T x)
    (hsep : ∀ x ∈ P, ∀ y ∈ P, x ≠ y →
      8 * ε < ‖secondDiff (fun t => los e x t - los e y t) h‖)
    (hcov : IsExhaustiveCover μ R₁ R₂ T ε e S) :
    P.ncard ≤ S.ncard := by
  classical
  obtain ⟨_, hrec⟩ := hcov
  let f : (ℝ → Vec) → (ℝ → Vec) := fun x =>
    if hx : x ∈ P then Classical.choose (hrec x (hP x hx)) else x
  have hfmem : ∀ x ∈ P, f x ∈ S := by
    intro x hx
    simpa [f, dif_pos hx] using (Classical.choose_spec (hrec x (hP x hx))).1
  have hfrec : ∀ x ∈ P, RecoveredBy e ε T (f x) x := by
    intro x hx
    simpa [f, dif_pos hx] using (Classical.choose_spec (hrec x (hP x hx))).2
  refine Set.ncard_le_ncard_of_injOn f hfmem ?_ hSfin
  intro x hx y hy hxy
  by_contra hne
  exact not_both_recovered hT (hsep x hx y hy hne) (hfrec x hx) (hxy ▸ hfrec y hy)

/-! Cartesian IC chart at the circular instance.

`sStar` is `(r,v) = ((5/2,0,0),(0,√10/5,0))`.  The Euler-family chart
at `e=0` is degenerate in `(M0, yaw)`; this chart is not.  `jetMatrix`
is the t²/t³ los-jet in these coordinates. -/

def sStar : Fin 6 → ℝ := ![5 / 2, 0, 0, 0, Real.sqrt 10 / 5, 0]

def obs : ℝ → Vec := circular 1 1 0

lemma isObserver_obs (T : ℝ) : IsObserver (1 : ℝ) T obs :=
  isObserver_unitCircle T

def statePos (s : Fin 6 → ℝ) : Vec := ofCoords (s 0) (s 1) (s 2)

def stateVel (s : Fin 6 → ℝ) : Vec := ofCoords (s 3) (s 4) (s 5)

lemma sStar_pos : statePos sStar = ofCoords (5 / 2) 0 0 := by
  simp [statePos, sStar]

lemma sStar_vel : stateVel sStar = ofCoords 0 (Real.sqrt 10 / 5) 0 := by
  simp [stateVel, sStar]

/-- Pack two `Vec` second-differences as a 6-tuple (sup-normed). -/
def sdPairCoord (w₁ w₂ : Vec) : Fin 6 → ℝ :=
  ![w₁.ofLp 0, w₁.ofLp 1, w₁.ofLp 2, w₂.ofLp 0, w₂.ofLp 1, w₂.ofLp 2]

lemma coord_le_euclidean (w : Vec) (i : Fin 3) : |w.ofLp i| ≤ ‖w‖ := by
  have hEu : ‖w‖ = Real.sqrt (∑ j : Fin 3, ‖w.ofLp j‖ ^ 2) := by
    rw [EuclideanSpace.norm_eq]
  have hsq : ‖w.ofLp i‖ ^ 2 ≤ ∑ j : Fin 3, ‖w.ofLp j‖ ^ 2 :=
    Finset.single_le_sum (f := fun j : Fin 3 => ‖w.ofLp j‖ ^ 2)
      (fun _ _ => sq_nonneg _) (Finset.mem_univ i)
  have : ‖w.ofLp i‖ ≤ Real.sqrt (∑ j : Fin 3, ‖w.ofLp j‖ ^ 2) :=
    Real.le_sqrt_of_sq_le hsq
  simpa [Real.norm_eq_abs, hEu] using this

lemma sdPairCoord_norm_le (w₁ w₂ : Vec) :
    ‖sdPairCoord w₁ w₂‖ ≤ ‖w₁‖ + ‖w₂‖ := by
  refine (pi_norm_le_iff_of_nonneg (add_nonneg (norm_nonneg w₁) (norm_nonneg w₂))).2 ?_
  intro i
  fin_cases i <;> simp [sdPairCoord, Real.norm_eq_abs]
  · exact (coord_le_euclidean w₁ 0).trans (le_add_of_nonneg_right (norm_nonneg w₂))
  · exact (coord_le_euclidean w₁ 1).trans (le_add_of_nonneg_right (norm_nonneg w₂))
  · exact (coord_le_euclidean w₁ 2).trans (le_add_of_nonneg_right (norm_nonneg w₂))
  · exact (coord_le_euclidean w₂ 0).trans (le_add_of_nonneg_left (norm_nonneg w₁))
  · exact (coord_le_euclidean w₂ 1).trans (le_add_of_nonneg_left (norm_nonneg w₁))
  · exact (coord_le_euclidean w₂ 2).trans (le_add_of_nonneg_left (norm_nonneg w₁))

lemma jetMatrix_mulVec_eq_zero {v : Fin 6 → ℝ}
    (h : jetMatrix *ᵥ v = 0) : v = 0 :=
  Matrix.eq_zero_of_mulVec_eq_zero jetMatrix_det_ne_zero h

lemma jetMatrix_mulVec_injective :
    Function.Injective fun v : Fin 6 → ℝ => jetMatrix *ᵥ v := by
  intro v w hvw
  have : jetMatrix *ᵥ (v - w) = 0 := by
    simp [Matrix.mulVec_sub, hvw]
  exact sub_eq_zero.mp (jetMatrix_mulVec_eq_zero this)

/-- Finite-dimensional: injective `mulVec` is bounded below. -/
lemma exists_sigma_jet :
    ∃ σ : ℝ, 0 < σ ∧ ∀ v : Fin 6 → ℝ, σ * ‖v‖ ≤ ‖jetMatrix *ᵥ v‖ := by
  classical
  let S : Set (Fin 6 → ℝ) := Metric.sphere 0 1
  have hK : IsCompact S := isCompact_sphere (0 : Fin 6 → ℝ) 1
  have hne : (Metric.sphere (0 : Fin 6 → ℝ) 1).Nonempty :=
    NormedSpace.sphere_nonempty.mpr (by norm_num : (0 : ℝ) ≤ 1)
  have hcont : Continuous fun v : Fin 6 → ℝ => ‖jetMatrix *ᵥ v‖ := by
    fun_prop
  obtain ⟨v0, hv0S, hmin⟩ := hK.exists_isMinOn hne hcont.continuousOn
  have hv01 : ‖v0‖ = 1 := mem_sphere_zero_iff_norm.mp hv0S
  have hσpos : 0 < ‖jetMatrix *ᵥ v0‖ := by
    refine norm_pos_iff.mpr ?_
    intro hz
    have : v0 = 0 := jetMatrix_mulVec_eq_zero hz
    have : (0 : ℝ) = 1 := by rw [← hv01, this, norm_zero]
    exact (by norm_num : (0 : ℝ) ≠ 1) this
  refine ⟨‖jetMatrix *ᵥ v0‖, hσpos, ?_⟩
  intro v
  rcases eq_or_ne v 0 with hv | hv
  · simp [hv]
  · have hun : ‖(‖v‖)⁻¹ • v‖ = 1 := by
      rw [norm_smul, norm_inv, norm_norm]
      field_simp [norm_ne_zero_iff.mpr hv]
    have huS : (‖v‖)⁻¹ • v ∈ S := mem_sphere_zero_iff_norm.mpr hun
    have hmin' : ‖jetMatrix *ᵥ v0‖ ≤ ‖jetMatrix *ᵥ ((‖v‖)⁻¹ • v)‖ :=
      hmin huS
    have hsc : jetMatrix *ᵥ ((‖v‖)⁻¹ • v) = (‖v‖)⁻¹ • (jetMatrix *ᵥ v) :=
      Matrix.mulVec_smul _ _ _
    rw [hsc, norm_smul, norm_inv, norm_norm] at hmin'
    have hvpos : 0 < ‖v‖ := norm_pos_iff.mpr hv
    have : ‖jetMatrix *ᵥ v0‖ * ‖v‖ ≤ ‖jetMatrix *ᵥ v‖ := by
      have := mul_le_mul_of_nonneg_right hmin' hvpos.le
      field_simp [hvpos.ne'] at this
      exact this
    simpa [mul_comm] using this

/-- Invertible linearisation plus quadratic remainder ⇒ linear-minus-quadratic lower bound. -/
lemma remainder_lower_bound {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E → F} {x y : E} {A : E →L[ℝ] F} {σ K : ℝ}
    (hσ : ∀ v : E, σ * ‖v‖ ≤ ‖A v‖)
    (hrem : ‖f y - f x - A (y - x)‖ ≤ K * ‖y - x‖ ^ 2) :
    σ * ‖y - x‖ - K * ‖y - x‖ ^ 2 ≤ ‖f y - f x‖ := by
  have hA : σ * ‖y - x‖ ≤ ‖A (y - x)‖ := hσ (y - x)
  have htri : ‖A (y - x)‖ ≤ ‖f y - f x‖ + ‖f y - f x - A (y - x)‖ := by
    calc
      ‖A (y - x)‖
          = ‖(f y - f x) - (f y - f x - A (y - x))‖ := by
            simp
      _ ≤ ‖f y - f x‖ + ‖f y - f x - A (y - x)‖ := norm_sub_le _ _
  linarith

/-! Algebraic t^2/t^3 los-jet in Cartesian ICs.  Matches `jetMatrix` as the
Jacobian of Taylor coefficients (los''(0)/2, los'''(0)/6). -/

def vecDot (u v : Vec) : ℝ := ∑ i : Fin 3, u.ofLp i * v.ofLp i

def accelOf (s : Fin 6 → ℝ) : Vec :=
  -((‖statePos s‖) ^ 3)⁻¹ • statePos s

def jerkOf (s : Fin 6 → ℝ) : Vec :=
  -(‖statePos s‖ ^ 3)⁻¹ • stateVel s
    + ((3 * vecDot (statePos s) (stateVel s)) / (‖statePos s‖ ^ 5)) • statePos s

def eJet0 : Vec := ofCoords 1 0 0
def eJet1 : Vec := ofCoords 0 1 0
def eJet2 : Vec := ofCoords (-1) 0 0
def eJet3 : Vec := ofCoords 0 (-1) 0

def n0Of (s : Fin 6 → ℝ) : Vec := statePos s - eJet0
def n1Of (s : Fin 6 → ℝ) : Vec := stateVel s - eJet1
def n2Of (s : Fin 6 → ℝ) : Vec := accelOf s - eJet2
def n3Of (s : Fin 6 → ℝ) : Vec := jerkOf s - eJet3

def qOf (s : Fin 6 → ℝ) : ℝ := vecDot (n0Of s) (n0Of s)
def q1Of (s : Fin 6 → ℝ) : ℝ := 2 * vecDot (n0Of s) (n1Of s)
def q2Of (s : Fin 6 → ℝ) : ℝ :=
  2 * vecDot (n1Of s) (n1Of s) + 2 * vecDot (n0Of s) (n2Of s)
def q3Of (s : Fin 6 → ℝ) : ℝ :=
  6 * vecDot (n1Of s) (n2Of s) + 2 * vecDot (n0Of s) (n3Of s)

def pOf (s : Fin 6 → ℝ) : ℝ := (qOf s) ^ (-(1 / 2 : ℝ))
def p1Of (s : Fin 6 → ℝ) : ℝ :=
  -(1 / 2 : ℝ) * (qOf s) ^ (-(3 / 2 : ℝ)) * q1Of s
def p2Of (s : Fin 6 → ℝ) : ℝ :=
  (3 / 4 : ℝ) * (qOf s) ^ (-(5 / 2 : ℝ)) * (q1Of s) ^ 2
    - (1 / 2 : ℝ) * (qOf s) ^ (-(3 / 2 : ℝ)) * q2Of s
def p3Of (s : Fin 6 → ℝ) : ℝ :=
  -(15 / 8 : ℝ) * (qOf s) ^ (-(7 / 2 : ℝ)) * (q1Of s) ^ 3
    + (9 / 4 : ℝ) * (qOf s) ^ (-(5 / 2 : ℝ)) * q1Of s * q2Of s
    - (1 / 2 : ℝ) * (qOf s) ^ (-(3 / 2 : ℝ)) * q3Of s

def u2Of (s : Fin 6 → ℝ) : Vec :=
  pOf s • n2Of s + (2 : ℝ) • (p1Of s • n1Of s) + p2Of s • n0Of s

def u3Of (s : Fin 6 → ℝ) : Vec :=
  pOf s • n3Of s + (3 : ℝ) • (p1Of s • n2Of s)
    + (3 : ℝ) • (p2Of s • n1Of s) + p3Of s • n0Of s

/-- Taylor t^2, t^3 coefficients of los along the Kepler flow of `s`, at time 0. -/
def losTaylor23 (s : Fin 6 → ℝ) : Fin 6 → ℝ :=
  ![ (u2Of s).ofLp 0 / 2, (u2Of s).ofLp 1 / 2, (u2Of s).ofLp 2 / 2
   , (u3Of s).ofLp 0 / 6, (u3Of s).ofLp 1 / 6, (u3Of s).ofLp 2 / 6 ]

def stumpffC (z : ℝ) : ℝ :=
  if z = 0 then (1 / 2 : ℝ) else (1 - Real.cos (Real.sqrt z)) / z

def stumpffS (z : ℝ) : ℝ :=
  if z = 0 then (1 / 6 : ℝ)
  else (Real.sqrt z - Real.sin (Real.sqrt z)) / (z * Real.sqrt z)

def rnorm (s : Fin 6 → ℝ) : ℝ := ‖statePos s‖
def alphaOf (s : Fin 6 → ℝ) : ℝ := 2 / rnorm s - ‖stateVel s‖ ^ 2
def sigmaOf (s : Fin 6 → ℝ) : ℝ := vecDot (statePos s) (stateVel s)

def univF (s : Fin 6 → ℝ) (χ : ℝ) : ℝ :=
  let α := alphaOf s
  let z := α * χ ^ 2
  let r0 := rnorm s
  sigmaOf s * χ ^ 2 * stumpffC z + (1 - α * r0) * χ ^ 3 * stumpffS z + r0 * χ

def fg_f (s : Fin 6 → ℝ) (χ : ℝ) : ℝ :=
  1 - χ ^ 2 / rnorm s * stumpffC (alphaOf s * χ ^ 2)

def fg_g (s : Fin 6 → ℝ) (t χ : ℝ) : ℝ :=
  t - χ ^ 3 * stumpffS (alphaOf s * χ ^ 2)

lemma sStar_rnorm : ‖statePos sStar‖ = 5 / 2 := by
  rw [sStar_pos, ofCoords_norm]
  norm_num [Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 5 / 2)]

lemma sStar_inner_rv : vecDot (statePos sStar) (stateVel sStar) = (0 : ℝ) := by
  simp [vecDot, sStar_pos, sStar_vel, ofLp_ofCoords, Fin.sum_univ_three]

lemma sStar_vel_norm_sq : ‖stateVel sStar‖ ^ 2 = 2 / 5 := by
  rw [sStar_vel, ofCoords_norm]
  have hnn : (0 : ℝ) ≤ 0 ^ 2 + (Real.sqrt 10 / 5) ^ 2 + 0 ^ 2 := by positivity
  rw [Real.sq_sqrt hnn]
  field_simp
  rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 10)]
  norm_num

lemma rnorm_sStar : rnorm sStar = 5 / 2 := sStar_rnorm

lemma alphaOf_sStar : alphaOf sStar = 2 / 5 := by
  simp [alphaOf, rnorm_sStar, sStar_vel_norm_sq]
  norm_num

lemma sigmaOf_sStar : sigmaOf sStar = 0 := sStar_inner_rv

lemma univF_sStar (χ : ℝ) : univF sStar χ = (5 / 2) * χ := by
  simp [univF, alphaOf_sStar, sigmaOf_sStar, rnorm_sStar]

lemma stumpffC_pos {z : ℝ} (hz : 0 < z) :
    stumpffC z = (1 - Real.cos (Real.sqrt z)) / z := by
  simp [stumpffC, hz.ne']

lemma stumpffS_pos {z : ℝ} (hz : 0 < z) :
    stumpffS z = (Real.sqrt z - Real.sin (Real.sqrt z)) / (z * Real.sqrt z) := by
  simp [stumpffS, hz.ne']

lemma chi_sStar (t : ℝ) : univF sStar (2 * t / 5) = t := by
  rw [univF_sStar]; ring

/-! Universal Kepler equation `univF s χ = t`, solved for `χ` by the bivariate IFT. -/

def univF_dchi (s : Fin 6 → ℝ) (χ : ℝ) : ℝ :=
  rnorm s
    + sigmaOf s * χ * (1 - alphaOf s * χ ^ 2 * stumpffS (alphaOf s * χ ^ 2))
    + (1 - alphaOf s * rnorm s) * χ ^ 2 * stumpffC (alphaOf s * χ ^ 2)

lemma univF_dchi_sStar (χ : ℝ) : univF_dchi sStar χ = 5 / 2 := by
  simp [univF_dchi, rnorm_sStar, sigmaOf_sStar, alphaOf_sStar]

lemma rnorm_sStar_pos : 0 < rnorm sStar := by
  rw [rnorm_sStar]; norm_num

lemma stumpffC_zero : stumpffC 0 = 1 / 2 := by simp [stumpffC]

lemma stumpffS_zero : stumpffS 0 = 1 / 6 := by simp [stumpffS]

/-- Regularization of `(1 - cos u) / u²`. Continuous on all of `ℝ`. -/
def cbar (u : ℝ) : ℝ := (1 / 2) * Real.sinc (u / 2) ^ 2

lemma cbar_zero : cbar 0 = 1 / 2 := by simp [cbar]

lemma cbar_of_ne {u : ℝ} (hu : u ≠ 0) :
    cbar u = (1 - Real.cos u) / u ^ 2 := by
  have hu2 : u / 2 ≠ 0 := div_ne_zero hu (by norm_num)
  unfold cbar
  rw [Real.sinc_of_ne_zero hu2]
  have hcos : Real.cos u = 1 - 2 * Real.sin (u / 2) ^ 2 := by
    have := Real.cos_two_mul_eq_one_sub (u / 2)
    simpa [mul_div_cancel₀ u (by norm_num : (2 : ℝ) ≠ 0)] using this
  rw [hcos]
  field_simp [hu, hu2]
  ring

lemma cbar_neg (u : ℝ) : cbar (-u) = cbar u := by
  simp [cbar, neg_div, Real.sinc_neg]

lemma continuous_cbar : Continuous cbar := by
  unfold cbar
  fun_prop

/-- Regularization of `(u - sin u) / u³`. -/
def sbar (u : ℝ) : ℝ :=
  if u = 0 then (1 / 6 : ℝ) else (u - Real.sin u) / u ^ 3

lemma sbar_zero : sbar 0 = 1 / 6 := by simp [sbar]

lemma sbar_of_ne {u : ℝ} (hu : u ≠ 0) :
    sbar u = (u - Real.sin u) / u ^ 3 := by
  simp [sbar, hu]

lemma sbar_neg (u : ℝ) : sbar (-u) = sbar u := by
  rcases eq_or_ne u 0 with rfl | hu
  · simp [sbar]
  · have : -u ≠ 0 := neg_ne_zero.mpr hu
    rw [sbar_of_ne this, sbar_of_ne hu, Real.sin_neg]
    have : (-u - -Real.sin u) / (-u) ^ 3 = (u - Real.sin u) / u ^ 3 := by
      have hu3 : u ^ 3 ≠ 0 := pow_ne_zero 3 hu
      field_simp [hu, hu3]
      ring
    exact this

lemma tendsto_one_sub_cos_div_three_sq :
    Tendsto (fun u : ℝ => (1 - Real.cos u) / (3 * u ^ 2)) (𝓝[≠] (0 : ℝ)) (𝓝 (1 / 6)) := by
  have hcongr : (fun u : ℝ => (1 - Real.cos u) / (3 * u ^ 2)) =ᶠ[𝓝[≠] (0 : ℝ)]
      fun u => cbar u / 3 := by
    filter_upwards [self_mem_nhdsWithin] with u hu
    rw [cbar_of_ne hu]
    field_simp [hu]
  refine Tendsto.congr' hcongr.symm ?_
  have hc : Tendsto cbar (𝓝 (0 : ℝ)) (𝓝 (1 / 2)) := by
    simpa [cbar_zero] using continuous_cbar.tendsto (0 : ℝ)
  have : Tendsto (fun u : ℝ => cbar u / 3) (𝓝 (0 : ℝ)) (𝓝 (1 / 6)) := by
    convert hc.div_const 3 using 1
    norm_num
  exact this.mono_left nhdsWithin_le_nhds

lemma tendsto_sbar_nhdsGT :
    Tendsto (fun u : ℝ => (u - Real.sin u) / u ^ 3) (𝓝[>] (0 : ℝ)) (𝓝 (1 / 6)) := by
  have hab : (0 : ℝ) < 1 := by norm_num
  have hf : ∀ x ∈ Set.Ioo (0 : ℝ) 1,
      HasDerivAt (fun u => u - Real.sin u) (1 - Real.cos x) x := by
    intro x _; exact (hasDerivAt_id x).sub (Real.hasDerivAt_sin x)
  have hg : ∀ x ∈ Set.Ioo (0 : ℝ) 1,
      HasDerivAt (fun u : ℝ => u ^ 3) (3 * x ^ 2) x := by
    intro x _
    simpa [pow_succ, pow_two, mul_comm, mul_left_comm, mul_assoc] using hasDerivAt_pow 3 x
  have hg' : ∀ x ∈ Set.Ioo (0 : ℝ) 1, 3 * x ^ 2 ≠ 0 := by
    intro x hx; exact mul_ne_zero (by norm_num) (pow_ne_zero 2 (ne_of_gt hx.1))
  have hfa : Tendsto (fun u : ℝ => u - Real.sin u) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have : Tendsto (fun u : ℝ => u - Real.sin u) (𝓝 0) (𝓝 (0 - Real.sin 0)) :=
      (continuous_id.sub Real.continuous_sin).tendsto 0
    simpa using this.mono_left nhdsWithin_le_nhds
  have hga : Tendsto (fun u : ℝ => u ^ 3) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have : Tendsto (fun u : ℝ => u ^ 3) (𝓝 0) (𝓝 (0 ^ 3)) :=
      (continuous_pow 3).tendsto 0
    simpa using this.mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
  have hdiv : Tendsto (fun x : ℝ => (1 - Real.cos x) / (3 * x ^ 2))
      (𝓝[>] (0 : ℝ)) (𝓝 (1 / 6)) :=
    tendsto_one_sub_cos_div_three_sq.mono_left (nhdsGT_le_nhdsNE (0 : ℝ))
  exact HasDerivAt.lhopital_zero_right_on_Ioo hab hf hg hg' hfa hga hdiv

lemma tendsto_sbar_nhdsLT :
    Tendsto (fun u : ℝ => (u - Real.sin u) / u ^ 3) (𝓝[<] (0 : ℝ)) (𝓝 (1 / 6)) := by
  have hab : (-1 : ℝ) < 0 := by norm_num
  have hf : ∀ x ∈ Set.Ioo (-1 : ℝ) 0,
      HasDerivAt (fun u => u - Real.sin u) (1 - Real.cos x) x := by
    intro x _; exact (hasDerivAt_id x).sub (Real.hasDerivAt_sin x)
  have hg : ∀ x ∈ Set.Ioo (-1 : ℝ) 0,
      HasDerivAt (fun u : ℝ => u ^ 3) (3 * x ^ 2) x := by
    intro x _
    simpa [pow_succ, pow_two, mul_comm, mul_left_comm, mul_assoc] using hasDerivAt_pow 3 x
  have hg' : ∀ x ∈ Set.Ioo (-1 : ℝ) 0, 3 * x ^ 2 ≠ 0 := by
    intro x hx; exact mul_ne_zero (by norm_num) (pow_ne_zero 2 (ne_of_lt hx.2))
  have hfb : Tendsto (fun u : ℝ => u - Real.sin u) (𝓝[<] (0 : ℝ)) (𝓝 0) := by
    have : Tendsto (fun u : ℝ => u - Real.sin u) (𝓝 0) (𝓝 (0 - Real.sin 0)) :=
      (continuous_id.sub Real.continuous_sin).tendsto 0
    simpa using this.mono_left nhdsWithin_le_nhds
  have hgb : Tendsto (fun u : ℝ => u ^ 3) (𝓝[<] (0 : ℝ)) (𝓝 0) := by
    have : Tendsto (fun u : ℝ => u ^ 3) (𝓝 0) (𝓝 (0 ^ 3)) :=
      (continuous_pow 3).tendsto 0
    simpa using this.mono_left (nhdsWithin_le_nhds (s := Set.Iio (0 : ℝ)))
  have hdiv : Tendsto (fun x : ℝ => (1 - Real.cos x) / (3 * x ^ 2))
      (𝓝[<] (0 : ℝ)) (𝓝 (1 / 6)) :=
    tendsto_one_sub_cos_div_three_sq.mono_left (nhdsLT_le_nhdsNE (0 : ℝ))
  exact HasDerivAt.lhopital_zero_left_on_Ioo hab hf hg hg' hfb hgb hdiv

lemma continuous_sbar : Continuous sbar := by
  refine continuous_iff_continuousAt.mpr fun u => ?_
  rcases eq_or_ne u 0 with rfl | hu
  · rw [continuousAt_iff_continuous_left'_right']
    constructor
    · change Tendsto sbar (𝓝[<] (0 : ℝ)) (𝓝 (sbar 0))
      rw [sbar_zero]
      refine tendsto_sbar_nhdsLT.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with v hv
      exact (sbar_of_ne (ne_of_lt hv)).symm
    · change Tendsto sbar (𝓝[>] (0 : ℝ)) (𝓝 (sbar 0))
      rw [sbar_zero]
      refine tendsto_sbar_nhdsGT.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with v hv
      exact (sbar_of_ne (ne_of_gt hv)).symm
  · have hne : {v : ℝ | v ≠ 0} ∈ 𝓝 u := isOpen_compl_singleton.mem_nhds hu
    have hc : ContinuousAt (fun v : ℝ => (v - Real.sin v) / v ^ 3) u := by
      refine ContinuousAt.div ?_ ?_ (pow_ne_zero 3 hu)
      · exact (continuous_id.sub Real.continuous_sin).continuousAt
      · exact (continuous_pow 3).continuousAt
    have hfeq : (fun v : ℝ => (v - Real.sin v) / v ^ 3) =ᶠ[𝓝 u] sbar := by
      filter_upwards [hne] with v hv
      exact (sbar_of_ne hv).symm
    exact (continuousAt_congr hfeq).mp hc

lemma stumpffC_eq_cbar {z : ℝ} (hz : 0 ≤ z) :
    stumpffC z = cbar (Real.sqrt z) := by
  rcases eq_or_lt_of_le hz with h | hz
  · subst h; simp [stumpffC, cbar]
  · have hsq : Real.sqrt z ≠ 0 := (Real.sqrt_pos.2 hz).ne'
    rw [stumpffC_pos hz, cbar_of_ne hsq, Real.sq_sqrt hz.le]

lemma stumpffS_eq_sbar {z : ℝ} (hz : 0 ≤ z) :
    stumpffS z = sbar (Real.sqrt z) := by
  rcases eq_or_lt_of_le hz with h | hz
  · subst h; simp [stumpffS, sbar]
  · have hsq : Real.sqrt z ≠ 0 := (Real.sqrt_pos.2 hz).ne'
    rw [stumpffS_pos hz, sbar_of_ne hsq]
    have : z * Real.sqrt z = Real.sqrt z ^ 3 := by
      have := Real.sq_sqrt hz.le
      calc
        z * Real.sqrt z = Real.sqrt z ^ 2 * Real.sqrt z := by rw [this]
        _ = Real.sqrt z ^ 3 := by ring
    rw [this]

lemma sin_omega_abs (ω t : ℝ) :
    Real.sin (ω * |t|) * Real.sign t = Real.sin (ω * t) := by
  rcases lt_trichotomy t 0 with h | rfl | h
  · rw [abs_of_neg h, Real.sign_of_neg h]
    have : ω * -t = -(ω * t) := by ring
    rw [this, Real.sin_neg]; ring
  · simp
  · rw [abs_of_pos h, Real.sign_of_pos h, mul_one]

lemma sign_abs_eq (t : ℝ) : Real.sign t * |t| = t := by
  rcases lt_trichotomy t 0 with h | rfl | h
  · rw [Real.sign_of_neg h, abs_of_neg h]; ring
  · simp
  · rw [Real.sign_of_pos h, abs_of_pos h]; ring

lemma sqrt_alpha_chi {α χ : ℝ} (hα : 0 < α) :
    Real.sqrt (α * χ ^ 2) = Real.sqrt α * |χ| := by
  rw [Real.sqrt_mul hα.le, Real.sqrt_sq_eq_abs]

lemma chiSq_mul_stumpffC {α χ : ℝ} (hα : 0 < α) :
    χ ^ 2 * stumpffC (α * χ ^ 2) = (1 - Real.cos (Real.sqrt α * χ)) / α := by
  rcases eq_or_ne χ 0 with rfl | hχ
  · simp [stumpffC]
  · have hz : 0 < α * χ ^ 2 := mul_pos hα (sq_pos_of_ne_zero hχ)
    rw [stumpffC_pos hz]
    have hχ2 : χ ^ 2 ≠ 0 := pow_ne_zero 2 hχ
    have hα0 : α ≠ 0 := hα.ne'
    have hz0 : α * χ ^ 2 ≠ 0 := hz.ne'
    field_simp [hχ2, hα0, hz0]
    have hsqrt : Real.sqrt (χ ^ 2 * α) = Real.sqrt α * |χ| := by
      rw [mul_comm, sqrt_alpha_chi hα]
    rw [hsqrt, mul_comm (Real.sqrt α) |χ|]
    have habs : |χ| * Real.sqrt α = |χ * Real.sqrt α| := by
      rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
    rw [habs, Real.cos_abs]

lemma chiCube_mul_stumpffS {α χ : ℝ} (hα : 0 < α) :
    χ ^ 3 * stumpffS (α * χ ^ 2) =
      χ / α - Real.sin (Real.sqrt α * χ) / (α * Real.sqrt α) := by
  rcases eq_or_ne χ 0 with rfl | hχ
  · simp [stumpffS]
  · have hz : 0 < α * χ ^ 2 := mul_pos hα (sq_pos_of_ne_zero hχ)
    rw [stumpffS_pos hz]
    set ω := Real.sqrt α
    have hω0 : ω ≠ 0 := Real.sqrt_ne_zero'.2 hα
    have hωnn : 0 ≤ ω := Real.sqrt_nonneg _
    have hχ2 : χ ^ 2 ≠ 0 := pow_ne_zero 2 hχ
    have hα0 : α ≠ 0 := hα.ne'
    have habs : |χ| ≠ 0 := abs_ne_zero.mpr hχ
    have hz' : α * χ ^ 2 = ω ^ 2 * χ ^ 2 := by
      simp [ω, Real.sq_sqrt hα.le]
    have hsqrt : Real.sqrt (α * χ ^ 2) = |χ| * ω := by
      rw [sqrt_alpha_chi hα, mul_comm]
    have hden : α * χ ^ 2 * (|χ| * ω) ≠ 0 :=
      mul_ne_zero (mul_ne_zero hα0 hχ2) (mul_ne_zero habs hω0)
    have hstep :
        χ ^ 3 * ((|χ| * ω - Real.sin (|χ| * ω)) / (α * χ ^ 2 * (|χ| * ω)))
          = χ / α - χ * Real.sin (|χ| * ω) / (|χ| * ω * α) := by
      field_simp [hα0, hχ, habs, hω0, hden]
    have hsin :
        χ * Real.sin (|χ| * ω) / (|χ| * ω * α) =
          Real.sin (ω * χ) / (α * ω) := by
      have hden2 : |χ| * ω * α ≠ 0 := mul_ne_zero (mul_ne_zero habs hω0) hα0
      have hden3 : α * ω ≠ 0 := mul_ne_zero hα0 hω0
      rw [div_eq_div_iff hden2 hden3]
      have hs := sin_omega_abs ω χ
      calc
        χ * Real.sin (|χ| * ω) * (α * ω)
            = (Real.sign χ * |χ|) * Real.sin (ω * |χ|) * (α * ω) := by
              rw [sign_abs_eq χ, mul_comm (|χ|) ω]
        _ = (Real.sin (ω * |χ|) * Real.sign χ) * (|χ| * ω * α) := by ring
        _ = Real.sin (ω * χ) * (|χ| * ω * α) := by rw [hs]
    rw [hsqrt, hstep, hsin, mul_comm ω χ]

/-- Elliptic closed form of the universal Kepler function, valid for `α > 0`. -/
def univF_ell (α σ r χ : ℝ) : ℝ :=
  σ * (1 - Real.cos (Real.sqrt α * χ)) / α
    + (1 - α * r) * (χ / α - Real.sin (Real.sqrt α * χ) / (α * Real.sqrt α))
    + r * χ

lemma univF_eq_ell {s : Fin 6 → ℝ} {χ : ℝ} (hα : 0 < alphaOf s) :
    univF s χ = univF_ell (alphaOf s) (sigmaOf s) (rnorm s) χ := by
  unfold univF univF_ell
  have hf := chiSq_mul_stumpffC (χ := χ) hα
  have hg := chiCube_mul_stumpffS (χ := χ) hα
  calc
    sigmaOf s * χ ^ 2 * stumpffC (alphaOf s * χ ^ 2)
        + (1 - alphaOf s * rnorm s) * χ ^ 3 * stumpffS (alphaOf s * χ ^ 2)
        + rnorm s * χ
      = sigmaOf s * (χ ^ 2 * stumpffC (alphaOf s * χ ^ 2))
          + (1 - alphaOf s * rnorm s) * (χ ^ 3 * stumpffS (alphaOf s * χ ^ 2))
          + rnorm s * χ := by ring
    _ = sigmaOf s * ((1 - Real.cos (Real.sqrt (alphaOf s) * χ)) / alphaOf s)
          + (1 - alphaOf s * rnorm s) *
              (χ / alphaOf s - Real.sin (Real.sqrt (alphaOf s) * χ)
                / (alphaOf s * Real.sqrt (alphaOf s)))
          + rnorm s * χ := by rw [hf, hg]
    _ = sigmaOf s * (1 - Real.cos (Real.sqrt (alphaOf s) * χ)) / alphaOf s
          + (1 - alphaOf s * rnorm s) *
              (χ / alphaOf s - Real.sin (Real.sqrt (alphaOf s) * χ)
                / (alphaOf s * Real.sqrt (alphaOf s)))
          + rnorm s * χ := by ring

lemma univF_dchi_eq_ell {s : Fin 6 → ℝ} {χ : ℝ} (hα : 0 < alphaOf s) :
    univF_dchi s χ =
      sigmaOf s * Real.sin (Real.sqrt (alphaOf s) * χ) / Real.sqrt (alphaOf s)
        + (1 - alphaOf s * rnorm s)
            * (1 - Real.cos (Real.sqrt (alphaOf s) * χ)) / alphaOf s
        + rnorm s := by
  unfold univF_dchi
  have hα0 : alphaOf s ≠ 0 := hα.ne'
  have hω0 : Real.sqrt (alphaOf s) ≠ 0 := Real.sqrt_ne_zero'.2 hα
  have hc := chiSq_mul_stumpffC (χ := χ) hα
  have hs := chiCube_mul_stumpffS (χ := χ) hα
  have hlin :
      χ * (1 - alphaOf s * χ ^ 2 * stumpffS (alphaOf s * χ ^ 2))
        = Real.sin (Real.sqrt (alphaOf s) * χ) / Real.sqrt (alphaOf s) := by
    have : χ ^ 3 * stumpffS (alphaOf s * χ ^ 2) =
        χ / alphaOf s - Real.sin (Real.sqrt (alphaOf s) * χ)
          / (alphaOf s * Real.sqrt (alphaOf s)) := hs
    have : χ - alphaOf s * (χ ^ 3 * stumpffS (alphaOf s * χ ^ 2))
        = Real.sin (Real.sqrt (alphaOf s) * χ) / Real.sqrt (alphaOf s) := by
      rw [this]
      field_simp [hα0, hω0]
      ring
    convert this using 1
    ring
  calc
    rnorm s + sigmaOf s * χ * (1 - alphaOf s * χ ^ 2 * stumpffS (alphaOf s * χ ^ 2))
        + (1 - alphaOf s * rnorm s) * χ ^ 2 * stumpffC (alphaOf s * χ ^ 2)
      = rnorm s + sigmaOf s * (χ * (1 - alphaOf s * χ ^ 2 * stumpffS (alphaOf s * χ ^ 2)))
          + (1 - alphaOf s * rnorm s) * (χ ^ 2 * stumpffC (alphaOf s * χ ^ 2)) := by ring
    _ = rnorm s + sigmaOf s * (Real.sin (Real.sqrt (alphaOf s) * χ) / Real.sqrt (alphaOf s))
          + (1 - alphaOf s * rnorm s) *
              ((1 - Real.cos (Real.sqrt (alphaOf s) * χ)) / alphaOf s) := by
        rw [hlin, hc]
    _ = sigmaOf s * Real.sin (Real.sqrt (alphaOf s) * χ) / Real.sqrt (alphaOf s)
          + (1 - alphaOf s * rnorm s)
              * (1 - Real.cos (Real.sqrt (alphaOf s) * χ)) / alphaOf s
          + rnorm s := by ring

lemma hasDerivAt_univF_ell_chi {α σ r χ : ℝ} (hα : 0 < α) :
    HasDerivAt (univF_ell α σ r)
      (σ * Real.sin (Real.sqrt α * χ) / Real.sqrt α
        + (1 - α * r) * (1 - Real.cos (Real.sqrt α * χ)) / α
        + r) χ := by
  have hα0 : α ≠ 0 := hα.ne'
  have hω0 : Real.sqrt α ≠ 0 := Real.sqrt_ne_zero'.2 hα
  have hωu : HasDerivAt (fun u => Real.sqrt α * u) (Real.sqrt α) χ := by
    simpa using (hasDerivAt_id χ).const_mul (Real.sqrt α)
  have h1 : HasDerivAt (fun u => 1 - Real.cos (Real.sqrt α * u))
      (Real.sin (Real.sqrt α * χ) * Real.sqrt α) χ := by
    refine ((hasDerivAt_const χ (1 : ℝ)).sub hωu.cos).congr_deriv ?_
    ring
  have h1c : HasDerivAt (fun u => (1 - Real.cos (Real.sqrt α * u)) / α)
      (Real.sin (Real.sqrt α * χ) * Real.sqrt α / α) χ :=
    h1.div_const α
  have hσ : HasDerivAt
      (fun u => σ * ((1 - Real.cos (Real.sqrt α * u)) / α))
      (σ * (Real.sin (Real.sqrt α * χ) * Real.sqrt α / α)) χ :=
    h1c.const_mul σ
  have hidα : HasDerivAt (fun u => u / α) (1 / α) χ :=
    (hasDerivAt_id χ).div_const α
  have hsin : HasDerivAt (fun u => Real.sin (Real.sqrt α * u))
      (Real.cos (Real.sqrt α * χ) * Real.sqrt α) χ :=
    hωu.sin
  have hsinα : HasDerivAt
      (fun u => Real.sin (Real.sqrt α * u) / (α * Real.sqrt α))
      (Real.cos (Real.sqrt α * χ) / α) χ := by
    have := hsin.div_const (α * Real.sqrt α)
    refine this.congr_deriv ?_
    field_simp [hα0, hω0]
  have hmid : HasDerivAt
      (fun u => u / α - Real.sin (Real.sqrt α * u) / (α * Real.sqrt α))
      (1 / α - Real.cos (Real.sqrt α * χ) / α) χ :=
    hidα.sub hsinα
  have hmid' : HasDerivAt
      (fun u => u / α - Real.sin (Real.sqrt α * u) / (α * Real.sqrt α))
      ((1 - Real.cos (Real.sqrt α * χ)) / α) χ := by
    convert hmid using 1
    ring
  have hmidc : HasDerivAt
      (fun u => (1 - α * r) *
        (u / α - Real.sin (Real.sqrt α * u) / (α * Real.sqrt α)))
      ((1 - α * r) * ((1 - Real.cos (Real.sqrt α * χ)) / α)) χ :=
    hmid'.const_mul (1 - α * r)
  have hr : HasDerivAt (fun u => r * u) r χ := by
    simpa using (hasDerivAt_id χ).const_mul r
  have hsum := (hσ.add hmidc).add hr
  have hfun :
      (fun u =>
          σ * ((1 - Real.cos (Real.sqrt α * u)) / α)
            + (1 - α * r) *
                (u / α - Real.sin (Real.sqrt α * u) / (α * Real.sqrt α))
            + r * u)
        = univF_ell α σ r := by
    ext u
    simp [univF_ell, div_eq_mul_inv, mul_assoc]
  rw [← hfun]
  refine hsum.congr_deriv ?_
  have hsq : Real.sqrt α * Real.sqrt α = α := Real.mul_self_sqrt hα.le
  have hstep : σ * (Real.sin (Real.sqrt α * χ) * Real.sqrt α / α)
      = σ * Real.sin (Real.sqrt α * χ) / Real.sqrt α := by
    field_simp [hα0, hω0]
    simp [pow_two, hsq]
    ring
  rw [hstep]
  ring

lemma hasDerivAt_univF_of_alpha_pos {s : Fin 6 → ℝ} {χ : ℝ}
    (hα : 0 < alphaOf s) :
    HasDerivAt (univF s) (univF_dchi s χ) χ := by
  have h := hasDerivAt_univF_ell_chi (α := alphaOf s) (σ := sigmaOf s)
    (r := rnorm s) (χ := χ) hα
  have heq : univF s = univF_ell (alphaOf s) (sigmaOf s) (rnorm s) :=
    funext fun u => univF_eq_ell hα
  rw [heq, univF_dchi_eq_ell hα]
  exact h

lemma hasDerivAt_univF_sStar (χ : ℝ) :
    HasDerivAt (univF sStar) (5 / 2) χ := by
  have h := (hasDerivAt_id χ).const_mul (5 / 2)
  refine (h.congr_of_eventuallyEq (Eventually.of_forall univF_sStar)).congr_deriv ?_
  ring

def univF_f2 (s : Fin 6 → ℝ) (χ : ℝ) : ℝ →L[ℝ] ℝ :=
  ContinuousLinearMap.toSpanSingleton ℝ (univF_dchi s χ)

lemma hasFDerivAt_univF_chi_of_alpha_pos {s : Fin 6 → ℝ} {χ : ℝ}
    (hα : 0 < alphaOf s) :
    HasFDerivAt (univF s) (univF_f2 s χ) χ :=
  (hasDerivAt_univF_of_alpha_pos hα).hasFDerivAt


lemma univF_f2_sStar (χ : ℝ) :
    univF_f2 sStar χ = ContinuousLinearMap.toSpanSingleton ℝ (5 / 2) := by
  simp [univF_f2, univF_dchi_sStar]

lemma univF_f2_invertible (t : ℝ) :
    (univF_f2 sStar (2 * t / 5)).IsInvertible := by
  rw [univF_f2_sStar]
  exact ContinuousLinearMap.IsInvertible.of_inverse
    (g := ContinuousLinearMap.toSpanSingleton ℝ (2 / 5))
    (by ext; simp) (by ext; simp)

lemma hasFDerivAt_univF_chi_sStar (χ : ℝ) :
    HasFDerivAt (univF sStar) (univF_f2 sStar χ) χ := by
  rw [univF_f2, univF_dchi_sStar]
  exact (hasDerivAt_univF_sStar χ).hasFDerivAt

lemma continuous_statePos : Continuous statePos := by
  unfold statePos ofCoords
  fun_prop

lemma continuous_stateVel : Continuous stateVel := by
  unfold stateVel ofCoords
  fun_prop

lemma continuous_rnorm : Continuous rnorm := by
  unfold rnorm
  exact continuous_statePos.norm

lemma continuous_sigmaOf : Continuous sigmaOf := by
  unfold sigmaOf vecDot
  fun_prop

lemma rnorm_sStar_ne : rnorm sStar ≠ 0 := rnorm_sStar_pos.ne'

lemma continuousAt_alphaOf {s : Fin 6 → ℝ} (hs : rnorm s ≠ 0) :
    ContinuousAt alphaOf s := by
  unfold alphaOf
  have hr : ContinuousAt rnorm s := continuous_rnorm.continuousAt
  have hinv : ContinuousAt (fun t : ℝ => (2 : ℝ) / t) (rnorm s) :=
    continuousAt_const.div continuousAt_id hs
  have hvel : ContinuousAt (fun u => ‖stateVel u‖ ^ 2) s :=
    (continuous_stateVel.norm.pow 2).continuousAt
  exact (hinv.comp hr).sub hvel

lemma continuousAt_alphaOf_sStar : ContinuousAt alphaOf sStar :=
  continuousAt_alphaOf (s := sStar) rnorm_sStar_ne

lemma eventually_alphaOf_pos :
    ∀ᶠ s in 𝓝 sStar, 0 < alphaOf s := by
  have hpos : 0 < alphaOf sStar := by rw [alphaOf_sStar]; norm_num
  exact continuousAt_alphaOf_sStar.preimage_mem_nhds (Ioi_mem_nhds hpos)

lemma eventually_hasFDerivAt_univF_chi (χ0 : ℝ) :
    ∀ᶠ v : (Fin 6 → ℝ) × ℝ in 𝓝 (sStar, χ0),
      HasFDerivAt (fun y => univF v.1 y) (univF_f2 v.1 v.2) v.2 := by
  have hα : ∀ᶠ v : (Fin 6 → ℝ) × ℝ in 𝓝 (sStar, χ0), 0 < alphaOf v.1 := by
    have : Tendsto (fun v : (Fin 6 → ℝ) × ℝ => alphaOf v.1)
        (𝓝 (sStar, χ0)) (𝓝 (alphaOf sStar)) :=
      continuousAt_alphaOf_sStar.tendsto.comp (continuous_fst.tendsto (sStar, χ0))
    have hpos : 0 < alphaOf sStar := by rw [alphaOf_sStar]; norm_num
    exact this.eventually (Ioi_mem_nhds hpos)
  filter_upwards [hα] with v hv
  exact hasFDerivAt_univF_chi_of_alpha_pos hv

lemma continuousAt_univF_dchi (χ0 : ℝ) :
    ContinuousAt (fun v : (Fin 6 → ℝ) × ℝ => univF_dchi v.1 v.2)
      (sStar, χ0) := by
  have hα : ∀ᶠ v : (Fin 6 → ℝ) × ℝ in 𝓝 (sStar, χ0), 0 < alphaOf v.1 := by
    have : Tendsto (fun v : (Fin 6 → ℝ) × ℝ => alphaOf v.1)
        (𝓝 (sStar, χ0)) (𝓝 (alphaOf sStar)) :=
      continuousAt_alphaOf_sStar.tendsto.comp (continuous_fst.tendsto (sStar, χ0))
    have hpos : 0 < alphaOf sStar := by rw [alphaOf_sStar]; norm_num
    exact this.eventually (Ioi_mem_nhds hpos)
  have heq : (fun v : (Fin 6 → ℝ) × ℝ => univF_dchi v.1 v.2) =ᶠ[𝓝 (sStar, χ0)]
      fun v =>
        sigmaOf v.1 * (Real.sin (Real.sqrt (alphaOf v.1) * v.2)
            / Real.sqrt (alphaOf v.1))
          + (1 - alphaOf v.1 * rnorm v.1)
              * ((1 - Real.cos (Real.sqrt (alphaOf v.1) * v.2))
              / alphaOf v.1)
          + rnorm v.1 := by
    filter_upwards [hα] with v hv
    simpa [div_eq_mul_inv, mul_assoc] using univF_dchi_eq_ell hv
  refine (continuousAt_congr heq).mpr ?_
  have hσ : ContinuousAt (fun v : (Fin 6 → ℝ) × ℝ => sigmaOf v.1) (sStar, χ0) :=
    continuous_sigmaOf.continuousAt.tendsto.comp (continuous_fst.tendsto (sStar, χ0))
  have hαc : ContinuousAt (fun v : (Fin 6 → ℝ) × ℝ => alphaOf v.1) (sStar, χ0) :=
    continuousAt_alphaOf_sStar.tendsto.comp (continuous_fst.tendsto (sStar, χ0))
  have hr : ContinuousAt (fun v : (Fin 6 → ℝ) × ℝ => rnorm v.1) (sStar, χ0) :=
    continuous_rnorm.continuousAt.tendsto.comp (continuous_fst.tendsto (sStar, χ0))
  have hpos : 0 < alphaOf sStar := by rw [alphaOf_sStar]; norm_num
  have hω0 : Real.sqrt (alphaOf sStar) ≠ 0 := Real.sqrt_ne_zero'.2 hpos
  have hα0 : alphaOf sStar ≠ 0 := hpos.ne'
  have hsqrt : ContinuousAt (fun v : (Fin 6 → ℝ) × ℝ => Real.sqrt (alphaOf v.1))
      (sStar, χ0) :=
    Real.continuous_sqrt.continuousAt.comp hαc
  have hsin : ContinuousAt
      (fun v : (Fin 6 → ℝ) × ℝ => Real.sin (Real.sqrt (alphaOf v.1) * v.2))
      (sStar, χ0) :=
    Real.continuous_sin.continuousAt.comp (hsqrt.mul continuous_snd.continuousAt)
  have hcos : ContinuousAt
      (fun v : (Fin 6 → ℝ) × ℝ => Real.cos (Real.sqrt (alphaOf v.1) * v.2))
      (sStar, χ0) :=
    Real.continuous_cos.continuousAt.comp (hsqrt.mul continuous_snd.continuousAt)
  have hone : ContinuousAt (fun _ : (Fin 6 → ℝ) × ℝ => (1 : ℝ)) (sStar, χ0) :=
    continuousAt_const
  have hterm1 : ContinuousAt
      (fun v : (Fin 6 → ℝ) × ℝ =>
        sigmaOf v.1 * (Real.sin (Real.sqrt (alphaOf v.1) * v.2)
          / Real.sqrt (alphaOf v.1))) (sStar, χ0) :=
    hσ.mul (hsin.div hsqrt hω0)
  have hterm2 : ContinuousAt
      (fun v : (Fin 6 → ℝ) × ℝ =>
        (1 - alphaOf v.1 * rnorm v.1)
          * ((1 - Real.cos (Real.sqrt (alphaOf v.1) * v.2))
              / alphaOf v.1)) (sStar, χ0) :=
    (hone.sub (hαc.mul hr)).mul ((hone.sub hcos).div hαc hα0)
  exact (hterm1.add hterm2).add hr

lemma continuousAt_univF_f2 (χ0 : ℝ) :
    ContinuousAt (Function.uncurry univF_f2) (sStar, χ0) := by
  have h := continuousAt_univF_dchi χ0
  have hL : Continuous (fun c : ℝ =>
      ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) c) :=
    continuous_smulRight_scalar
  change ContinuousAt
      (fun v : (Fin 6 → ℝ) × ℝ =>
        ContinuousLinearMap.toSpanSingleton ℝ (univF_dchi v.1 v.2))
      (sStar, χ0)
  convert hL.continuousAt.comp h using 1
  ext v
  simp [ContinuousLinearMap.toSpanSingleton]


/-! Cartesian-state derivatives of `rnorm`, `sigmaOf`, `alphaOf`, and `univF`. -/

lemma statePos_add (s t : Fin 6 → ℝ) : statePos (s + t) = statePos s + statePos t := by
  apply (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).injective
  ext i; fin_cases i <;> simp [statePos, ofCoords, PiLp.add_apply]

lemma statePos_smul (c : ℝ) (s : Fin 6 → ℝ) : statePos (c • s) = c • statePos s := by
  apply (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).injective
  ext i; fin_cases i <;> simp [statePos, ofCoords, PiLp.smul_apply, smul_eq_mul]

lemma stateVel_add (s t : Fin 6 → ℝ) : stateVel (s + t) = stateVel s + stateVel t := by
  apply (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).injective
  ext i; fin_cases i <;> simp [stateVel, ofCoords, PiLp.add_apply]

lemma stateVel_smul (c : ℝ) (s : Fin 6 → ℝ) : stateVel (c • s) = c • stateVel s := by
  apply (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).injective
  ext i; fin_cases i <;> simp [stateVel, ofCoords, PiLp.smul_apply, smul_eq_mul]

def clmStatePos : (Fin 6 → ℝ) →L[ℝ] Vec :=
  { toLinearMap :=
    { toFun := statePos
      map_add' := statePos_add
      map_smul' := statePos_smul }
    cont := continuous_statePos }

def clmStateVel : (Fin 6 → ℝ) →L[ℝ] Vec :=
  { toLinearMap :=
    { toFun := stateVel
      map_add' := stateVel_add
      map_smul' := stateVel_smul }
    cont := continuous_stateVel }

lemma hasFDerivAt_statePos (s : Fin 6 → ℝ) : HasFDerivAt statePos clmStatePos s :=
  clmStatePos.hasFDerivAt

lemma hasFDerivAt_stateVel (s : Fin 6 → ℝ) : HasFDerivAt stateVel clmStateVel s :=
  clmStateVel.hasFDerivAt

lemma vecDot_eq_inner (u v : Vec) : vecDot u v = ⟪u, v⟫ := by
  rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm, dotProduct]
  simp [vecDot]

lemma contDiff_statePos : ContDiff ℝ ⊤ statePos := clmStatePos.contDiff

lemma contDiff_stateVel : ContDiff ℝ ⊤ stateVel := clmStateVel.contDiff

lemma contDiffAt_rnorm {s : Fin 6 → ℝ} (hs : rnorm s ≠ 0) :
    ContDiffAt ℝ ⊤ rnorm s := by
  have hsq : ContDiffAt ℝ ⊤ (fun u => ‖statePos u‖ ^ 2) s :=
    (contDiff_statePos.contDiffAt.norm_sq ℝ)
  have hne : ‖statePos s‖ ^ 2 ≠ 0 := pow_ne_zero 2 hs
  have hsqrt : ContDiffAt ℝ ⊤ (fun u => Real.sqrt (‖statePos u‖ ^ 2)) s :=
    hsq.sqrt hne
  refine hsqrt.congr_of_eventuallyEq ?_
  exact Eventually.of_forall fun u => (Real.sqrt_sq (norm_nonneg (statePos u))).symm

lemma contDiffAt_sigmaOf (s : Fin 6 → ℝ) : ContDiffAt ℝ ⊤ sigmaOf s := by
  have h : ContDiffAt ℝ ⊤ (fun u => ⟪statePos u, stateVel u⟫) s :=
    (contDiff_statePos.contDiffAt.inner (𝕜 := ℝ) contDiff_stateVel.contDiffAt)
  refine h.congr_of_eventuallyEq ?_
  exact Eventually.of_forall fun u => (vecDot_eq_inner _ _).symm

lemma contDiffAt_alphaOf' {s : Fin 6 → ℝ} (hs : rnorm s ≠ 0) :
    ContDiffAt ℝ ⊤ alphaOf s := by
  have hr := contDiffAt_rnorm hs
  have hinv : ContDiffAt ℝ ⊤ (fun y : ℝ => (2 : ℝ) / y) (rnorm s) :=
    contDiffAt_const.div contDiffAt_id hs
  have h2r := hinv.comp s hr
  have hvil : ContDiffAt ℝ ⊤ (fun u => ‖stateVel u‖ ^ 2) s :=
    (contDiff_stateVel.contDiffAt.norm_sq ℝ)
  exact (h2r.sub hvil).congr_of_eventuallyEq (Eventually.of_forall fun _ => rfl)

def asrOf (s : Fin 6 → ℝ) : ℝ × ℝ × ℝ := (alphaOf s, sigmaOf s, rnorm s)

lemma contDiffAt_asrOf {s : Fin 6 → ℝ} (hs : rnorm s ≠ 0) :
    ContDiffAt ℝ ⊤ asrOf s :=
  (contDiffAt_alphaOf' hs).prodMk ((contDiffAt_sigmaOf s).prodMk (contDiffAt_rnorm hs))

lemma contDiffAt_univF_ell3 {α σ r χ : ℝ} (hα : 0 < α) :
    ContDiffAt ℝ ⊤ (fun p : ℝ × ℝ × ℝ => univF_ell p.1 p.2.1 p.2.2 χ) (α, σ, r) := by
  have hfst : ContDiffAt ℝ ⊤ (fun p : ℝ × ℝ × ℝ => p.1) (α, σ, r) :=
    contDiff_fst.contDiffAt
  have hσ : ContDiffAt ℝ ⊤ (fun p : ℝ × ℝ × ℝ => p.2.1) (α, σ, r) :=
    (contDiff_fst.comp contDiff_snd).contDiffAt
  have hr : ContDiffAt ℝ ⊤ (fun p : ℝ × ℝ × ℝ => p.2.2) (α, σ, r) :=
    (contDiff_snd.comp contDiff_snd).contDiffAt
  have hsqrt : ContDiffAt ℝ ⊤ (fun p : ℝ × ℝ × ℝ => Real.sqrt p.1) (α, σ, r) :=
    (Real.contDiffAt_sqrt hα.ne').comp (α, σ, r) hfst
  have hωχ : ContDiffAt ℝ ⊤ (fun p : ℝ × ℝ × ℝ => Real.sqrt p.1 * χ) (α, σ, r) :=
    hsqrt.mul contDiffAt_const
  have hcos : ContDiffAt ℝ ⊤ (fun p : ℝ × ℝ × ℝ => Real.cos (Real.sqrt p.1 * χ))
      (α, σ, r) := hωχ.cos
  have hsin : ContDiffAt ℝ ⊤ (fun p : ℝ × ℝ × ℝ => Real.sin (Real.sqrt p.1 * χ))
      (α, σ, r) := hωχ.sin
  have hα0 : α ≠ 0 := hα.ne'
  have hω0 : Real.sqrt α ≠ 0 := Real.sqrt_ne_zero'.2 hα
  have hC : ContDiffAt ℝ ⊤
      (fun p : ℝ × ℝ × ℝ => (1 - Real.cos (Real.sqrt p.1 * χ)) / p.1) (α, σ, r) :=
    (contDiffAt_const.sub hcos).div hfst hα0
  have hS : ContDiffAt ℝ ⊤
      (fun p : ℝ × ℝ × ℝ =>
        χ / p.1 - Real.sin (Real.sqrt p.1 * χ) / (p.1 * Real.sqrt p.1)) (α, σ, r) :=
    (contDiffAt_const.div hfst hα0).sub
      (hsin.div (hfst.mul hsqrt) (mul_ne_zero hα0 hω0))
  have h1 : ContDiffAt ℝ ⊤
      (fun p : ℝ × ℝ × ℝ => p.2.1 * ((1 - Real.cos (Real.sqrt p.1 * χ)) / p.1))
      (α, σ, r) := hσ.mul hC
  have h2 : ContDiffAt ℝ ⊤
      (fun p : ℝ × ℝ × ℝ =>
        (1 - p.1 * p.2.2) *
          (χ / p.1 - Real.sin (Real.sqrt p.1 * χ) / (p.1 * Real.sqrt p.1)))
      (α, σ, r) := (contDiffAt_const.sub (hfst.mul hr)).mul hS
  have h3 : ContDiffAt ℝ ⊤ (fun p : ℝ × ℝ × ℝ => p.2.2 * χ) (α, σ, r) :=
    hr.mul contDiffAt_const
  refine ((h1.add h2).add h3).congr_of_eventuallyEq ?_
  exact Eventually.of_forall fun p => by
    simp [univF_ell, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]

lemma contDiffAt_univF_ell_unc {α σ r χ : ℝ} (hα : 0 < α) :
    ContDiffAt ℝ ⊤ (fun q : (ℝ × ℝ × ℝ) × ℝ =>
      univF_ell q.1.1 q.1.2.1 q.1.2.2 q.2) ((α, σ, r), χ) := by
  have hfst : ContDiffAt ℝ ⊤ (fun q : (ℝ × ℝ × ℝ) × ℝ => q.1.1) ((α, σ, r), χ) :=
    (contDiff_fst.comp contDiff_fst).contDiffAt
  have hσ : ContDiffAt ℝ ⊤ (fun q : (ℝ × ℝ × ℝ) × ℝ => q.1.2.1) ((α, σ, r), χ) :=
    ((contDiff_fst.comp contDiff_snd).comp contDiff_fst).contDiffAt
  have hr : ContDiffAt ℝ ⊤ (fun q : (ℝ × ℝ × ℝ) × ℝ => q.1.2.2) ((α, σ, r), χ) :=
    ((contDiff_snd.comp contDiff_snd).comp contDiff_fst).contDiffAt
  have hχ : ContDiffAt ℝ ⊤ (fun q : (ℝ × ℝ × ℝ) × ℝ => q.2) ((α, σ, r), χ) :=
    contDiff_snd.contDiffAt
  have hsqrt : ContDiffAt ℝ ⊤ (fun q : (ℝ × ℝ × ℝ) × ℝ => Real.sqrt q.1.1)
      ((α, σ, r), χ) :=
    (Real.contDiffAt_sqrt hα.ne').comp ((α, σ, r), χ) hfst
  have hωχ : ContDiffAt ℝ ⊤ (fun q : (ℝ × ℝ × ℝ) × ℝ => Real.sqrt q.1.1 * q.2)
      ((α, σ, r), χ) := hsqrt.mul hχ
  have hα0 : α ≠ 0 := hα.ne'
  have hω0 : Real.sqrt α ≠ 0 := Real.sqrt_ne_zero'.2 hα
  have hC : ContDiffAt ℝ ⊤
      (fun q : (ℝ × ℝ × ℝ) × ℝ => (1 - Real.cos (Real.sqrt q.1.1 * q.2)) / q.1.1)
      ((α, σ, r), χ) :=
    (contDiffAt_const.sub hωχ.cos).div hfst hα0
  have hS : ContDiffAt ℝ ⊤
      (fun q : (ℝ × ℝ × ℝ) × ℝ =>
        q.2 / q.1.1 - Real.sin (Real.sqrt q.1.1 * q.2) / (q.1.1 * Real.sqrt q.1.1))
      ((α, σ, r), χ) :=
    (hχ.div hfst hα0).sub (hωχ.sin.div (hfst.mul hsqrt) (mul_ne_zero hα0 hω0))
  have h1 := hσ.mul hC
  have h2 : ContDiffAt ℝ ⊤
      (fun q : (ℝ × ℝ × ℝ) × ℝ =>
        (1 - q.1.1 * q.1.2.2) *
          (q.2 / q.1.1 - Real.sin (Real.sqrt q.1.1 * q.2) / (q.1.1 * Real.sqrt q.1.1)))
      ((α, σ, r), χ) :=
    (contDiffAt_const.sub (hfst.mul hr)).mul hS
  have h3 : ContDiffAt ℝ ⊤ (fun q : (ℝ × ℝ × ℝ) × ℝ => q.1.2.2 * q.2)
      ((α, σ, r), χ) := hr.mul hχ
  refine ((h1.add h2).add h3).congr_of_eventuallyEq ?_
  exact Eventually.of_forall fun q => by
    simp [univF_ell, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]

lemma eventually_rnorm_ne :
    ∀ᶠ s in 𝓝 sStar, rnorm s ≠ 0 := by
  have hmem : {s : Fin 6 → ℝ | 0 < rnorm s} ∈ 𝓝 sStar :=
    continuous_rnorm.continuousAt.preimage_mem_nhds (Ioi_mem_nhds rnorm_sStar_pos)
  exact Filter.eventually_of_mem hmem fun _ hs => ne_of_gt hs

lemma contDiffAt_uncurry_univF (χ0 : ℝ) :
    ContDiffAt ℝ ⊤ (Function.uncurry univF) (sStar, χ0) := by
  have hαpos : 0 < alphaOf sStar := by rw [alphaOf_sStar]; norm_num
  have hr : rnorm sStar ≠ 0 := rnorm_sStar_ne
  have hαnhd : ∀ᶠ v : (Fin 6 → ℝ) × ℝ in 𝓝 (sStar, χ0), 0 < alphaOf v.1 := by
    have hf : ContinuousAt (fun v : (Fin 6 → ℝ) × ℝ => v.1) (sStar, χ0) :=
      continuous_fst.continuousAt
    have : Tendsto (fun v : (Fin 6 → ℝ) × ℝ => alphaOf v.1)
        (𝓝 (sStar, χ0)) (𝓝 (alphaOf sStar)) :=
      Tendsto.comp continuousAt_alphaOf_sStar.tendsto hf.tendsto
    exact this.eventually (Ioi_mem_nhds hαpos)
  have hrnhd : ∀ᶠ v : (Fin 6 → ℝ) × ℝ in 𝓝 (sStar, χ0), rnorm v.1 ≠ 0 := by
    have hf : ContinuousAt (fun v : (Fin 6 → ℝ) × ℝ => v.1) (sStar, χ0) :=
      continuous_fst.continuousAt
    have : Tendsto (rnorm ∘ fun v : (Fin 6 → ℝ) × ℝ => v.1)
        (𝓝 (sStar, χ0)) (𝓝 (rnorm sStar)) :=
      (continuous_rnorm.continuousAt (x := sStar)).tendsto.comp hf.tendsto
    exact this.eventually (isOpen_ne.mem_nhds rnorm_sStar_ne)
  have hell : ContDiffAt ℝ ⊤ (fun v : (Fin 6 → ℝ) × ℝ =>
      univF_ell (alphaOf v.1) (sigmaOf v.1) (rnorm v.1) v.2) (sStar, χ0) := by
    have hasr : ContDiffAt ℝ ⊤ (fun v : (Fin 6 → ℝ) × ℝ =>
        ((alphaOf v.1, sigmaOf v.1, rnorm v.1), v.2)) (sStar, χ0) := by
      have ha := (contDiffAt_alphaOf' hr).comp (sStar, χ0)
        (contDiff_fst.contDiffAt (x := (sStar, χ0)))
      have hs := (contDiffAt_sigmaOf sStar).comp (sStar, χ0)
        (contDiff_fst.contDiffAt (x := (sStar, χ0)))
      have hn := (contDiffAt_rnorm hr).comp (sStar, χ0)
        (contDiff_fst.contDiffAt (x := (sStar, χ0)))
      have hχ : ContDiffAt ℝ ⊤ (fun v : (Fin 6 → ℝ) × ℝ => v.2) (sStar, χ0) :=
        contDiff_snd.contDiffAt
      exact (ha.prodMk (hs.prodMk hn)).prodMk hχ
    exact (contDiffAt_univF_ell_unc (α := alphaOf sStar) (σ := sigmaOf sStar)
      (r := rnorm sStar) (χ := χ0) hαpos).comp (sStar, χ0) hasr
  refine hell.congr_of_eventuallyEq ?_
  filter_upwards [hαnhd] with v hv
  simpa [Function.uncurry] using univF_eq_ell hv

/-- Partial of `univF` in the Cartesian state. -/
def univF_f1 (s : Fin 6 → ℝ) (χ : ℝ) : (Fin 6 → ℝ) →L[ℝ] ℝ :=
  (fderiv ℝ (Function.uncurry univF) (s, χ)).comp (ContinuousLinearMap.inl ℝ (Fin 6 → ℝ) ℝ)

lemma eventually_hasFDerivAt_univF_s (χ0 : ℝ) :
    ∀ᶠ v : (Fin 6 → ℝ) × ℝ in 𝓝 (sStar, χ0),
      HasFDerivAt (fun s' => univF s' v.2) (univF_f1 v.1 v.2) v.1 := by
  have hcd : ContDiffAt ℝ 2 (Function.uncurry univF) (sStar, χ0) :=
    (contDiffAt_uncurry_univF χ0).of_le (by exact le_top)
  have hopen : ∀ᶠ v : (Fin 6 → ℝ) × ℝ in 𝓝 (sStar, χ0),
      ContDiffAt ℝ 2 (Function.uncurry univF) v :=
    hcd.eventually (by decide)
  filter_upwards [hopen] with v hv
  have hjoint : HasFDerivAt (Function.uncurry univF)
      (fderiv ℝ (Function.uncurry univF) v) v :=
    (hv.differentiableAt (by decide)).hasFDerivAt
  have hconst : HasFDerivAt (fun _ : Fin 6 → ℝ => v.2)
      (0 : (Fin 6 → ℝ) →L[ℝ] ℝ) v.1 := hasFDerivAt_const _ _
  have hprod : HasFDerivAt (fun s' : Fin 6 → ℝ => (s', v.2))
      ((ContinuousLinearMap.id ℝ (Fin 6 → ℝ)).prod 0) v.1 :=
    (hasFDerivAt_id v.1).prodMk hconst
  have hcomp := hjoint.comp v.1 hprod
  refine hcomp.congr_fderiv ?_
  ext ds
  simp [univF_f1, ContinuousLinearMap.inl]

lemma continuousAt_univF_f1 (χ0 : ℝ) :
    ContinuousAt (Function.uncurry univF_f1) (sStar, χ0) := by
  have hf : ContDiffAt ℝ 2 (Function.uncurry univF) (sStar, χ0) :=
    (contDiffAt_uncurry_univF χ0).of_le (by exact le_top)
  have hfd : ContinuousAt (fderiv ℝ (Function.uncurry univF)) (sStar, χ0) :=
    hf.continuousAt_fderiv (by decide)
  have hcomp : Continuous
      (fun L : ((Fin 6 → ℝ) × ℝ) →L[ℝ] ℝ =>
        L.comp (ContinuousLinearMap.inl ℝ (Fin 6 → ℝ) ℝ)) :=
    continuous_id.clm_comp continuous_const
  exact hcomp.continuousAt.comp hfd

/-- Inverse Kepler anomaly via the bivariate IFT at `(sStar, 2t/5)`. -/
noncomputable def chiOf (s : Fin 6 → ℝ) (t : ℝ) : ℝ :=
  implicitFunctionOfBivariate
    (eventually_hasFDerivAt_univF_s (2 * t / 5))
    (eventually_hasFDerivAt_univF_chi (2 * t / 5))
    (continuousAt_univF_f1 (2 * t / 5))
    (continuousAt_univF_f2 (2 * t / 5))
    (univF_f2_invertible t) s

lemma chiOf_sStar (t : ℝ) : chiOf sStar t = 2 * t / 5 := by
  have hiff := eventually_apply_eq_iff_implicitFunctionOfBivariate
    (eventually_hasFDerivAt_univF_s (2 * t / 5))
    (eventually_hasFDerivAt_univF_chi (2 * t / 5))
    (continuousAt_univF_f1 (2 * t / 5))
    (continuousAt_univF_f2 (2 * t / 5))
    (univF_f2_invertible t)
  have := hiff.self_of_nhds
  simpa [chiOf] using this.mp rfl

lemma hasDerivAt_chiOf_sStar (t : ℝ) :
    HasDerivAt (chiOf sStar) (5 / 2)⁻¹ t := by
  have heq : chiOf sStar = fun y => 2 * y / 5 := funext chiOf_sStar
  rw [heq]
  have hg : ContinuousAt (fun y : ℝ => 2 * y / 5) t := by fun_prop
  exact HasDerivAt.of_local_left_inverse hg
    (hasDerivAt_univF_sStar (2 * t / 5)) (by norm_num)
    (Eventually.of_forall fun y => by simp [univF_sStar])

def keplerIC (s : Fin 6 → ℝ) : ℝ → Vec :=
  fun t =>
    let χ := chiOf s t
    fg_f s χ • statePos s + fg_g s t χ • stateVel s

lemma keplerIC_sStar_zero : keplerIC sStar 0 = ofCoords (5 / 2) 0 0 := by
  simp [keplerIC, chiOf_sStar, fg_f, fg_g, stumpffC, sStar_pos]

lemma meanMotion_sq : Real.sqrt (8 / 125) ^ 2 = 8 / 125 :=
  Real.sq_sqrt (by norm_num)

/-- `n = 2 √10 / 25`, equivalently `√(8/125)`. -/
lemma meanMotion_eq : Real.sqrt (8 / 125) = 2 * Real.sqrt 10 / 25 := by
  have hnn : (0 : ℝ) ≤ 2 * Real.sqrt 10 / 25 := by positivity
  refine (Real.sqrt_eq_iff_mul_self_eq (by norm_num) hnn).2 ?_
  field_simp
  ring_nf
  simp [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 10)]
  norm_num

lemma omega_sq : Real.sqrt (8 / 125) ^ 2 = 8 / 125 :=
  meanMotion_sq

lemma z_of_sStar (t : ℝ) :
    alphaOf sStar * (2 * t / 5) ^ 2 = 8 * t ^ 2 / 125 := by
  rw [alphaOf_sStar]
  ring

lemma sqrt_z_of_sStar {t : ℝ} (_ht : t ≠ 0) :
    Real.sqrt (alphaOf sStar * (2 * t / 5) ^ 2) = |t| * Real.sqrt (8 / 125) := by
  rw [z_of_sStar, show 8 * t ^ 2 / 125 = (8 / 125) * t ^ 2 by ring]
  rw [Real.sqrt_mul (by positivity : (0 : ℝ) ≤ 8 / 125) (t ^ 2), Real.sqrt_sq_eq_abs]
  ring

lemma fg_f_sStar (t : ℝ) :
    fg_f sStar (2 * t / 5) = Real.cos (Real.sqrt (8 / 125) * t) := by
  unfold fg_f
  rw [rnorm_sStar]
  rcases eq_or_ne t 0 with rfl | ht
  · simp [stumpffC]
  · have hz : 0 < alphaOf sStar * (2 * t / 5) ^ 2 := by
      rw [z_of_sStar]
      exact div_pos (mul_pos (by norm_num) (sq_pos_of_ne_zero ht)) (by norm_num)
    rw [stumpffC_pos hz, z_of_sStar]
    have htn : t ^ 2 ≠ 0 := pow_ne_zero 2 ht
    have hdiv :
        (2 * t / 5) ^ 2 / (5 / 2) * ((1 - Real.cos (Real.sqrt (8 * t ^ 2 / 125))) /
          (8 * t ^ 2 / 125))
        = 1 - Real.cos (Real.sqrt (8 * t ^ 2 / 125)) := by
      field_simp [htn]
      ring
    rw [hdiv]
    have hsqrt : Real.sqrt (8 * t ^ 2 / 125) = |t| * Real.sqrt (8 / 125) := by
      rw [show 8 * t ^ 2 / 125 = (8 / 125) * t ^ 2 by ring]
      rw [Real.sqrt_mul (by positivity : (0 : ℝ) ≤ 8 / 125) (t ^ 2), Real.sqrt_sq_eq_abs]
      ring
    rw [show 1 - (1 - Real.cos (Real.sqrt (8 * t ^ 2 / 125)))
          = Real.cos (Real.sqrt (8 * t ^ 2 / 125)) by ring, hsqrt]
    have hω : 0 ≤ Real.sqrt (8 / 125) := Real.sqrt_nonneg _
    have : |Real.sqrt (8 / 125) * t| = Real.sqrt (8 / 125) * |t| := by
      rw [abs_mul, abs_of_nonneg hω]
    rw [mul_comm |t|, ← this, Real.cos_abs]

lemma sqrt_omega_sq_t (ω t : ℝ) (hω : 0 ≤ ω) :
    Real.sqrt (ω ^ 2 * t ^ 2) = |t| * ω := by
  have : ω ^ 2 * t ^ 2 = (ω * |t|) ^ 2 := by
    calc
      ω ^ 2 * t ^ 2 = ω ^ 2 * |t| ^ 2 := by rw [sq_abs]
      _ = (ω * |t|) ^ 2 := by ring
  rw [this, Real.sqrt_sq (mul_nonneg hω (abs_nonneg t)), mul_comm]

lemma t_div_abs (t : ℝ) (ht : t ≠ 0) : t / |t| = Real.sign t := by
  rcases lt_or_gt_of_ne ht with h | h
  · rw [abs_of_neg h, Real.sign_of_neg h]; field_simp [ne_of_lt h]
  · rw [abs_of_pos h, Real.sign_of_pos h]; field_simp [ne_of_gt h]

lemma fg_g_sStar (t : ℝ) :
    fg_g sStar t (2 * t / 5) = Real.sin (Real.sqrt (8 / 125) * t) / Real.sqrt (8 / 125) := by
  unfold fg_g
  rcases eq_or_ne t 0 with rfl | ht
  · simp [stumpffS]
  · have hz : 0 < alphaOf sStar * (2 * t / 5) ^ 2 := by
      rw [z_of_sStar]
      exact div_pos (mul_pos (by norm_num) (sq_pos_of_ne_zero ht)) (by norm_num)
    set ω := Real.sqrt (8 / 125)
    have hω0 : ω ≠ 0 := Real.sqrt_ne_zero'.2 (by norm_num)
    have hωnn : 0 ≤ ω := Real.sqrt_nonneg _
    have hz' : alphaOf sStar * (2 * t / 5) ^ 2 = ω ^ 2 * t ^ 2 := by
      rw [z_of_sStar, omega_sq]; ring
    have habs : |t| ≠ 0 := abs_ne_zero.mpr ht
    have hχ3 : (2 * t / 5) ^ 3 = 8 * t ^ 3 / 125 := by ring
    have hω2 : ω ^ 2 = 8 / 125 := omega_sq
    have hmain : (2 * t / 5) ^ 3 * stumpffS (alphaOf sStar * (2 * t / 5) ^ 2)
        = t - Real.sin (ω * t) / ω := by
      rw [stumpffS_pos hz, hχ3, hz', sqrt_omega_sq_t ω t hωnn, hω2]
      have hden : (8 / 125 : ℝ) * t ^ 2 * (|t| * ω) ≠ 0 := by
        refine mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 2 ht)) (mul_ne_zero habs hω0)
      have hstep :
          8 * t ^ 3 / 125 * ((|t| * ω - Real.sin (|t| * ω)) / (8 / 125 * t ^ 2 * (|t| * ω)))
            = t - t * Real.sin (|t| * ω) / (|t| * ω) := by
        field_simp [hω0, ht, habs, hden]
      have hsin : t * Real.sin (|t| * ω) / (|t| * ω) = Real.sin (ω * t) / ω := by
        rw [div_eq_div_iff (mul_ne_zero habs hω0) hω0]
        have hs := sin_omega_abs ω t
        calc
          t * Real.sin (|t| * ω) * ω
              = (Real.sign t * |t|) * Real.sin (ω * |t|) * ω := by
                rw [sign_abs_eq t, mul_comm (|t|) ω]
          _ = (Real.sin (ω * |t|) * Real.sign t) * (|t| * ω) := by ring
          _ = Real.sin (ω * t) * (|t| * ω) := by rw [hs]
      rw [hstep, hsin]
    rw [hmain]
    ring

lemma vel_scale :
    (1 / Real.sqrt (8 / 125)) * (Real.sqrt 10 / 5) = (5 / 2 : ℝ) := by
  rw [meanMotion_eq]
  have hs : Real.sqrt 10 ≠ 0 := Real.sqrt_ne_zero'.2 (by norm_num)
  field_simp [hs]
  ring_nf

lemma keplerIC_sStar (t : ℝ) :
    keplerIC sStar t = circular (5 / 2) (Real.sqrt (8 / 125)) 0 t := by
  have hf := fg_f_sStar t
  have hg := fg_g_sStar t
  have hχ : chiOf sStar t = 2 * t / 5 := chiOf_sStar t
  apply (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).injective
  ext i
  fin_cases i
  · simp [keplerIC, hχ, sStar_pos, sStar_vel, circular, ofCoords,
      PiLp.smul_apply, PiLp.add_apply, smul_eq_mul, hf]
    ring
  · simp [keplerIC, hχ, sStar_pos, sStar_vel, circular, ofCoords,
      PiLp.smul_apply, PiLp.add_apply, smul_eq_mul, hg]
    have hω : Real.sqrt (8 / 125) ≠ 0 := Real.sqrt_ne_zero'.2 (by norm_num)
    have hs10 : Real.sqrt 10 ≠ 0 := Real.sqrt_ne_zero'.2 (by norm_num)
    field_simp [hω, hs10]
    have h8 : Real.sqrt 8 ≠ 0 := Real.sqrt_ne_zero'.2 (by norm_num)
    have h125 : Real.sqrt 125 ≠ 0 := Real.sqrt_ne_zero'.2 (by norm_num)
    have hid : Real.sqrt 125 * Real.sqrt 10 * 2 = Real.sqrt 8 * 25 := by
      have hsq : (Real.sqrt 125 * Real.sqrt 10 * 2) ^ 2 = (Real.sqrt 8 * 25) ^ 2 := by
        simp [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 125),
          Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 10),
          Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 8)]
        norm_num
      exact (sq_eq_sq₀ (by positivity) (by positivity)).mp hsq
    set snt := Real.sin (Real.sqrt 8 * t / Real.sqrt 125)
    calc
      Real.sqrt 125 * snt * Real.sqrt 10 * 2
          = (Real.sqrt 125 * Real.sqrt 10 * 2) * snt := by ring
      _ = (Real.sqrt 8 * 25) * snt := by rw [hid]
      _ = Real.sqrt 8 * snt * 5 ^ 2 := by ring
  · simp [keplerIC, hχ, sStar_pos, sStar_vel, circular, ofCoords,
      PiLp.smul_apply, PiLp.add_apply, smul_eq_mul]

/-! Values of the algebraic los-jet at `sStar`, and C^∞ of `losTaylor23`. -/

set_option maxHeartbeats 800000

lemma n0Of_sStar : n0Of sStar = ofCoords (3 / 2) 0 0 := by
  apply (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).injective
  ext i; fin_cases i <;> simp [n0Of, sStar_pos, eJet0, ofCoords, PiLp.sub_apply] <;> norm_num

lemma n1Of_sStar : n1Of sStar = ofCoords 0 (Real.sqrt 10 / 5 - 1) 0 := by
  apply (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).injective
  ext i; fin_cases i <;> simp [n1Of, sStar_vel, eJet1, ofCoords, PiLp.sub_apply]

lemma accelOf_sStar : accelOf sStar = ofCoords (-4 / 25) 0 0 := by
  unfold accelOf
  rw [sStar_rnorm, sStar_pos]
  apply (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).injective
  ext i
  fin_cases i <;> simp [ofCoords, PiLp.smul_apply, smul_eq_mul] <;> norm_num

lemma n2Of_sStar : n2Of sStar = ofCoords (21 / 25) 0 0 := by
  apply (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).injective
  ext i; fin_cases i <;> simp [n2Of, accelOf_sStar, eJet2, ofCoords, PiLp.sub_apply]
    <;> norm_num

lemma jerkOf_sStar : jerkOf sStar = ofCoords 0 (-8 * Real.sqrt 10 / 625) 0 := by
  unfold jerkOf
  rw [sStar_rnorm, sStar_inner_rv, sStar_pos, sStar_vel]
  apply (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).injective
  ext i
  fin_cases i <;> simp [ofCoords, PiLp.smul_apply, PiLp.add_apply, smul_eq_mul]
    <;> field_simp <;> ring

lemma n3Of_sStar : n3Of sStar = ofCoords 0 (1 - 8 * Real.sqrt 10 / 625) 0 := by
  apply (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).injective
  ext i; fin_cases i <;> simp [n3Of, jerkOf_sStar, eJet3, ofCoords, PiLp.sub_apply]
  ring

lemma qOf_sStar : qOf sStar = 9 / 4 := by
  simp [qOf, vecDot, n0Of_sStar, ofLp_ofCoords, Fin.sum_univ_three]
  norm_num

lemma q1Of_sStar : q1Of sStar = 0 := by
  simp [q1Of, vecDot, n0Of_sStar, n1Of_sStar, ofLp_ofCoords, Fin.sum_univ_three]

lemma qOf_sStar_pos : 0 < qOf sStar := by
  rw [qOf_sStar]; norm_num

lemma contDiff_n0Of : ContDiff ℝ ⊤ n0Of := by
  unfold n0Of
  exact contDiff_statePos.sub (contDiff_const (c := eJet0))

lemma contDiff_n1Of : ContDiff ℝ ⊤ n1Of := by
  unfold n1Of
  exact contDiff_stateVel.sub (contDiff_const (c := eJet1))

lemma continuous_qOf : Continuous qOf := by
  have h : Continuous (fun s => ⟪n0Of s, n0Of s⟫) :=
    (contDiff_n0Of.continuous.inner (𝕜 := ℝ) contDiff_n0Of.continuous)
  convert h using 1
  ext s
  exact (vecDot_eq_inner (n0Of s) (n0Of s)).symm

lemma eventually_qOf_pos : ∀ᶠ s in 𝓝 sStar, 0 < qOf s :=
  continuous_qOf.continuousAt.preimage_mem_nhds (Ioi_mem_nhds qOf_sStar_pos)

lemma contDiffAt_accelOf : ContDiffAt ℝ ⊤ accelOf sStar := by
  have hpow : ContDiffAt ℝ ⊤ (fun s => rnorm s ^ 3) sStar :=
    (contDiffAt_rnorm rnorm_sStar_ne).pow 3
  have hinv : ContDiffAt ℝ ⊤ (fun s => (rnorm s ^ 3)⁻¹) sStar :=
    hpow.inv (by rw [rnorm_sStar]; norm_num)
  have hsmul : ContDiffAt ℝ ⊤ (fun s => (rnorm s ^ 3)⁻¹ • statePos s) sStar :=
    hinv.smul contDiff_statePos.contDiffAt
  refine hsmul.neg.congr_of_eventuallyEq ?_
  exact Eventually.of_forall fun s => by
    simp [accelOf, rnorm, neg_smul]

lemma contDiffAt_jerkOf : ContDiffAt ℝ ⊤ jerkOf sStar := by
  have hpow3 : ContDiffAt ℝ ⊤ (fun s => rnorm s ^ 3) sStar :=
    (contDiffAt_rnorm rnorm_sStar_ne).pow 3
  have hinv3 : ContDiffAt ℝ ⊤ (fun s => (rnorm s ^ 3)⁻¹) sStar :=
    hpow3.inv (by rw [rnorm_sStar]; norm_num)
  have hpow5 : ContDiffAt ℝ ⊤ (fun s => rnorm s ^ 5) sStar :=
    (contDiffAt_rnorm rnorm_sStar_ne).pow 5
  have hinv5 : ContDiffAt ℝ ⊤ (fun s => (rnorm s ^ 5)⁻¹) sStar :=
    hpow5.inv (by rw [rnorm_sStar]; norm_num)
  have hterm1 : ContDiffAt ℝ ⊤ (fun s => (rnorm s ^ 3)⁻¹ • stateVel s) sStar :=
    hinv3.smul contDiff_stateVel.contDiffAt
  have hinter : ContDiffAt ℝ ⊤ (fun s => ⟪statePos s, stateVel s⟫) sStar :=
    contDiff_statePos.contDiffAt.inner (𝕜 := ℝ) contDiff_stateVel.contDiffAt
  have hdot : ContDiffAt ℝ ⊤ (fun s => vecDot (statePos s) (stateVel s)) sStar := by
    refine hinter.congr_of_eventuallyEq ?_
    exact Eventually.of_forall fun u => (vecDot_eq_inner _ _).symm
  have hnum : ContDiffAt ℝ ⊤
      (fun s => (3 : ℝ) * vecDot (statePos s) (stateVel s)) sStar :=
    contDiffAt_const.mul hdot
  have hcoef : ContDiffAt ℝ ⊤
      (fun s => ((3 : ℝ) * vecDot (statePos s) (stateVel s)) * (rnorm s ^ 5)⁻¹)
      sStar :=
    hnum.mul hinv5
  have hterm2 : ContDiffAt ℝ ⊤
      (fun s => (((3 : ℝ) * vecDot (statePos s) (stateVel s)) / (rnorm s ^ 5)) •
        statePos s) sStar := by
    refine (hcoef.smul contDiff_statePos.contDiffAt).congr_of_eventuallyEq ?_
    exact Eventually.of_forall fun s => by simp [div_eq_mul_inv]
  refine (hterm1.neg.add hterm2).congr_of_eventuallyEq ?_
  exact Eventually.of_forall fun s => by
    simp [jerkOf, rnorm, neg_smul, div_eq_mul_inv]

lemma contDiffAt_n2Of : ContDiffAt ℝ ⊤ n2Of sStar := by
  unfold n2Of
  exact contDiffAt_accelOf.sub (contDiff_const (c := eJet2)).contDiffAt

lemma contDiffAt_n3Of : ContDiffAt ℝ ⊤ n3Of sStar := by
  unfold n3Of
  exact contDiffAt_jerkOf.sub (contDiff_const (c := eJet3)).contDiffAt

lemma contDiff_qOf : ContDiff ℝ ⊤ qOf := by
  have h : ContDiff ℝ ⊤ (fun s => ⟪n0Of s, n0Of s⟫) :=
    contDiff_n0Of.inner (𝕜 := ℝ) contDiff_n0Of
  convert h using 1
  ext s
  exact (vecDot_eq_inner (n0Of s) (n0Of s)).symm

lemma contDiff_q1Of : ContDiff ℝ ⊤ q1Of := by
  have h : ContDiff ℝ ⊤ (fun s => (2 : ℝ) * ⟪n0Of s, n1Of s⟫) :=
    contDiff_const.mul (contDiff_n0Of.inner (𝕜 := ℝ) contDiff_n1Of)
  convert h using 1
  ext s
  simp [q1Of, vecDot_eq_inner]

lemma contDiffAt_q2Of : ContDiffAt ℝ ⊤ q2Of sStar := by
  have h11 : ContDiffAt ℝ ⊤ (fun s => (2 : ℝ) * ⟪n1Of s, n1Of s⟫) sStar :=
    (contDiff_const.mul (contDiff_n1Of.inner (𝕜 := ℝ) contDiff_n1Of)).contDiffAt
  have h02 : ContDiffAt ℝ ⊤ (fun s => (2 : ℝ) * ⟪n0Of s, n2Of s⟫) sStar :=
    contDiffAt_const.mul (contDiff_n0Of.contDiffAt.inner (𝕜 := ℝ) contDiffAt_n2Of)
  refine (h11.add h02).congr_of_eventuallyEq ?_
  exact Eventually.of_forall fun s => by simp [q2Of, vecDot_eq_inner]

lemma contDiffAt_q3Of : ContDiffAt ℝ ⊤ q3Of sStar := by
  have h12 : ContDiffAt ℝ ⊤ (fun s => (6 : ℝ) * ⟪n1Of s, n2Of s⟫) sStar :=
    contDiffAt_const.mul (contDiff_n1Of.contDiffAt.inner (𝕜 := ℝ) contDiffAt_n2Of)
  have h03 : ContDiffAt ℝ ⊤ (fun s => (2 : ℝ) * ⟪n0Of s, n3Of s⟫) sStar :=
    contDiffAt_const.mul (contDiff_n0Of.contDiffAt.inner (𝕜 := ℝ) contDiffAt_n3Of)
  refine (h12.add h03).congr_of_eventuallyEq ?_
  exact Eventually.of_forall fun s => by simp [q3Of, vecDot_eq_inner]

lemma contDiffAt_rpow_q (p : ℝ) :
    ContDiffAt ℝ ⊤ (fun s => (qOf s) ^ p) sStar :=
  contDiff_qOf.contDiffAt.rpow contDiffAt_const qOf_sStar_pos.ne'

lemma contDiffAt_pOf : ContDiffAt ℝ ⊤ pOf sStar := by
  unfold pOf
  exact contDiffAt_rpow_q (-(1 / 2 : ℝ))

lemma contDiffAt_p1Of : ContDiffAt ℝ ⊤ p1Of sStar := by
  unfold p1Of
  exact (contDiffAt_const.mul (contDiffAt_rpow_q (-(3 / 2 : ℝ)))).mul
    contDiff_q1Of.contDiffAt

lemma contDiffAt_p2Of : ContDiffAt ℝ ⊤ p2Of sStar := by
  have ht1 : ContDiffAt ℝ ⊤
      (fun s => (3 / 4 : ℝ) * (qOf s) ^ (-(5 / 2 : ℝ)) * (q1Of s) ^ 2) sStar :=
    (contDiffAt_const.mul (contDiffAt_rpow_q (-(5 / 2 : ℝ)))).mul
      (contDiff_q1Of.contDiffAt.pow 2)
  have ht2 : ContDiffAt ℝ ⊤
      (fun s => (1 / 2 : ℝ) * (qOf s) ^ (-(3 / 2 : ℝ)) * q2Of s) sStar :=
    (contDiffAt_const.mul (contDiffAt_rpow_q (-(3 / 2 : ℝ)))).mul contDiffAt_q2Of
  unfold p2Of
  exact ht1.sub ht2

lemma contDiffAt_p3Of : ContDiffAt ℝ ⊤ p3Of sStar := by
  have ht1 : ContDiffAt ℝ ⊤
      (fun s => (-(15 / 8 : ℝ)) * (qOf s) ^ (-(7 / 2 : ℝ)) * (q1Of s) ^ 3)
      sStar :=
    (contDiffAt_const.mul (contDiffAt_rpow_q (-(7 / 2 : ℝ)))).mul
      (contDiff_q1Of.contDiffAt.pow 3)
  have ht2 : ContDiffAt ℝ ⊤
      (fun s => (9 / 4 : ℝ) * (qOf s) ^ (-(5 / 2 : ℝ)) * q1Of s * q2Of s)
      sStar :=
    ((contDiffAt_const.mul (contDiffAt_rpow_q (-(5 / 2 : ℝ)))).mul
      contDiff_q1Of.contDiffAt).mul contDiffAt_q2Of
  have ht3 : ContDiffAt ℝ ⊤
      (fun s => (1 / 2 : ℝ) * (qOf s) ^ (-(3 / 2 : ℝ)) * q3Of s) sStar :=
    (contDiffAt_const.mul (contDiffAt_rpow_q (-(3 / 2 : ℝ)))).mul contDiffAt_q3Of
  unfold p3Of
  exact (ht1.add ht2).sub ht3

lemma contDiffAt_u2Of : ContDiffAt ℝ ⊤ u2Of sStar := by
  have a : ContDiffAt ℝ ⊤ (fun s => pOf s • n2Of s) sStar :=
    contDiffAt_pOf.smul contDiffAt_n2Of
  have bmid : ContDiffAt ℝ ⊤ (fun s => p1Of s • n1Of s) sStar :=
    contDiffAt_p1Of.smul contDiff_n1Of.contDiffAt
  have b : ContDiffAt ℝ ⊤ (fun s => (2 : ℝ) • (p1Of s • n1Of s)) sStar :=
    (contDiffAt_const (c := (2 : ℝ))).smul bmid
  have c : ContDiffAt ℝ ⊤ (fun s => p2Of s • n0Of s) sStar :=
    contDiffAt_p2Of.smul contDiff_n0Of.contDiffAt
  unfold u2Of
  exact (a.add b).add c

lemma contDiffAt_u3Of : ContDiffAt ℝ ⊤ u3Of sStar := by
  have a : ContDiffAt ℝ ⊤ (fun s => pOf s • n3Of s) sStar :=
    contDiffAt_pOf.smul contDiffAt_n3Of
  have bmid : ContDiffAt ℝ ⊤ (fun s => p1Of s • n2Of s) sStar :=
    contDiffAt_p1Of.smul contDiffAt_n2Of
  have b : ContDiffAt ℝ ⊤ (fun s => (3 : ℝ) • (p1Of s • n2Of s)) sStar :=
    (contDiffAt_const (c := (3 : ℝ))).smul bmid
  have cmid : ContDiffAt ℝ ⊤ (fun s => p2Of s • n1Of s) sStar :=
    contDiffAt_p2Of.smul contDiff_n1Of.contDiffAt
  have c : ContDiffAt ℝ ⊤ (fun s => (3 : ℝ) • (p2Of s • n1Of s)) sStar :=
    (contDiffAt_const (c := (3 : ℝ))).smul cmid
  have d : ContDiffAt ℝ ⊤ (fun s => p3Of s • n0Of s) sStar :=
    contDiffAt_p3Of.smul contDiff_n0Of.contDiffAt
  unfold u3Of
  exact ((a.add b).add c).add d

lemma contDiff_ofLp_coord (i : Fin 3) : ContDiff ℝ ⊤ (fun w : Vec => w.ofLp i) :=
  (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) i).contDiff.comp
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).contDiff

lemma contDiffAt_losTaylor23 : ContDiffAt ℝ ⊤ losTaylor23 sStar := by
  refine contDiffAt_pi.2 fun i => ?_
  fin_cases i
  · exact ((contDiff_ofLp_coord 0).contDiffAt.comp sStar contDiffAt_u2Of).div
      contDiffAt_const (by norm_num)
  · exact ((contDiff_ofLp_coord 1).contDiffAt.comp sStar contDiffAt_u2Of).div
      contDiffAt_const (by norm_num)
  · exact ((contDiff_ofLp_coord 2).contDiffAt.comp sStar contDiffAt_u2Of).div
      contDiffAt_const (by norm_num)
  · exact ((contDiff_ofLp_coord 0).contDiffAt.comp sStar contDiffAt_u3Of).div
      contDiffAt_const (by norm_num)
  · exact ((contDiff_ofLp_coord 1).contDiffAt.comp sStar contDiffAt_u3Of).div
      contDiffAt_const (by norm_num)
  · exact ((contDiff_ofLp_coord 2).contDiffAt.comp sStar contDiffAt_u3Of).div
      contDiffAt_const (by norm_num)

lemma hasFDerivAt_losTaylor23_fderiv :
    HasFDerivAt losTaylor23 (fderiv ℝ losTaylor23 sStar) sStar :=
  (contDiffAt_losTaylor23.differentiableAt (by decide)).hasFDerivAt

def lineJet (j : Fin 6) (t : ℝ) : Fin 6 → ℝ :=
  sStar + t • Pi.single j (1 : ℝ)

lemma lineJet_zero (j : Fin 6) : lineJet j 0 = sStar := by
  simp [lineJet]

lemma hasDerivAt_lineJet (j : Fin 6) (t : ℝ) :
    HasDerivAt (lineJet j) (Pi.single j (1 : ℝ)) t := by
  unfold lineJet
  have h :=
    ((hasDerivAt_id (𝕜 := ℝ) t).smul_const (Pi.single j (1 : ℝ))).const_add sStar
  have h' : HasDerivAt (fun x => sStar + x • Pi.single j (1 : ℝ))
      ((1 : ℝ) • Pi.single j (1 : ℝ)) t :=
    h.congr_of_eventuallyEq (Eventually.of_forall fun x => by simp)
  have h1 : (1 : ℝ) • Pi.single j (1 : ℝ) = Pi.single j (1 : ℝ) := one_smul ℝ _
  exact h'.congr_deriv h1

lemma hasDerivAt_losTaylor23_line (j i : Fin 6) :
    HasDerivAt (fun t => losTaylor23 (lineJet j t) i)
      (fderiv ℝ losTaylor23 sStar (Pi.single j 1) i) 0 := by
  have hf : HasFDerivAt losTaylor23 (fderiv ℝ losTaylor23 sStar) (lineJet j 0) := by
    rw [lineJet_zero]; exact hasFDerivAt_losTaylor23_fderiv
  have hcomp := hf.comp_hasDerivAt 0 (hasDerivAt_lineJet j 0)
  exact (hasDerivAt_pi.mp hcomp) i

lemma toLin'_jetMatrix_single (j : Fin 6) :
    Matrix.toLin' jetMatrix (Pi.single j (1 : ℝ)) = fun i => jetMatrix i j := by
  ext i
  simp [Matrix.toLin'_apply, Matrix.mulVec, dotProduct]
  rw [Finset.sum_eq_single j]
  · simp
  · intro k _ hkj
    simp [Pi.single_eq_of_ne hkj]
  · simp

lemma fderiv_losTaylor23_single (j i : Fin 6) :
    fderiv ℝ losTaylor23 sStar (Pi.single j 1) i
      = deriv (fun t => losTaylor23 (lineJet j t) i) 0 :=
  (hasDerivAt_losTaylor23_line j i).deriv.symm

lemma q2Of_sStar : q2Of sStar = 133 / 25 - 4 * Real.sqrt 10 / 5 := by
  simp [q2Of, vecDot, n1Of_sStar, n0Of_sStar, n2Of_sStar, ofLp_ofCoords,
    Fin.sum_univ_three]
  field_simp
  ring_nf
  simp [sqrt10_sq]
  ring

lemma q3Of_sStar : q3Of sStar = 0 := by
  simp [q3Of, vecDot, n1Of_sStar, n2Of_sStar, n0Of_sStar, n3Of_sStar,
    ofLp_ofCoords, Fin.sum_univ_three]

lemma sqrt_nine_div_four : Real.sqrt (9 / 4) = 3 / 2 := by
  rw [Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 9)]
  have h9 : Real.sqrt 9 = 3 :=
    (Real.sqrt_eq_iff_eq_sq (by norm_num : (0 : ℝ) ≤ 9) (by norm_num : (0 : ℝ) ≤ 3)).2
      (by norm_num)
  have h4 : Real.sqrt 4 = 2 :=
    (Real.sqrt_eq_iff_eq_sq (by norm_num : (0 : ℝ) ≤ 4) (by norm_num : (0 : ℝ) ≤ 2)).2
      (by norm_num)
  rw [h9, h4]

lemma rpow_neg_half_nine_four : (9 / 4 : ℝ) ^ (-(1 / 2 : ℝ)) = 2 / 3 := by
  have hpos : (0 : ℝ) < 9 / 4 := by norm_num
  rw [Real.rpow_neg hpos.le]
  have hs : (9 / 4 : ℝ) ^ (1 / 2 : ℝ) = Real.sqrt (9 / 4) := by
    rw [Real.sqrt_eq_rpow]
  rw [hs, sqrt_nine_div_four]
  field_simp

lemma rpow_neg_three_halves_nine_four : (9 / 4 : ℝ) ^ (-(3 / 2 : ℝ)) = 8 / 27 := by
  have hpos : (0 : ℝ) < 9 / 4 := by norm_num
  rw [Real.rpow_neg hpos.le]
  have h32 : (9 / 4 : ℝ) ^ (3 / 2 : ℝ) = (9 / 4) * Real.sqrt (9 / 4) := by
    have : (3 / 2 : ℝ) = 1 + 1 / 2 := by norm_num
    rw [this, Real.rpow_add hpos, Real.rpow_one, Real.sqrt_eq_rpow]
  rw [h32, sqrt_nine_div_four]
  field_simp
  norm_num

lemma pOf_sStar : pOf sStar = 2 / 3 := by
  unfold pOf
  rw [qOf_sStar, rpow_neg_half_nine_four]

lemma p1Of_sStar : p1Of sStar = 0 := by
  simp [p1Of, q1Of_sStar]

lemma p2Of_sStar : p2Of sStar = -532 / 675 + 16 * Real.sqrt 10 / 135 := by
  unfold p2Of
  rw [qOf_sStar, q1Of_sStar, q2Of_sStar]
  simp only [zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero, zero_mul, zero_sub]
  rw [rpow_neg_three_halves_nine_four]
  field_simp
  ring

lemma p3Of_sStar : p3Of sStar = 0 := by
  simp [p3Of, q1Of_sStar, q3Of_sStar]

lemma u2Of_sStar :
    u2Of sStar = ofCoords (-28 / 45 + 8 * Real.sqrt 10 / 45) 0 0 := by
  apply (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).injective
  ext i
  fin_cases i <;>
    simp [u2Of, pOf_sStar, p1Of_sStar, p2Of_sStar, n2Of_sStar, n1Of_sStar, n0Of_sStar,
      ofCoords, PiLp.smul_apply, PiLp.add_apply, smul_eq_mul] <;> field_simp <;> ring

lemma u3Of_sStar :
    u3Of sStar = ofCoords 0 (842 / 225 - 4708 * Real.sqrt 10 / 5625) 0 := by
  apply (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).injective
  ext i
  fin_cases i <;>
    simp [u3Of, pOf_sStar, p1Of_sStar, p2Of_sStar, p3Of_sStar, n3Of_sStar, n2Of_sStar,
      n1Of_sStar, n0Of_sStar, ofCoords, PiLp.smul_apply, PiLp.add_apply, smul_eq_mul]
  all_goals (try (field_simp; ring_nf; simp [sqrt10_sq]; ring))

lemma lineJet_apply (j k : Fin 6) (t : ℝ) :
    lineJet j t k = sStar k + if k = j then t else 0 := by
  simp [lineJet, Pi.single_apply, smul_eq_mul]

lemma statePos_lineJet0 (t : ℝ) :
    statePos (lineJet 0 t) = ofCoords (5 / 2 + t) 0 0 := by
  simp [statePos, ofCoords, lineJet_apply, sStar]

lemma stateVel_lineJet0 (t : ℝ) :
    stateVel (lineJet 0 t) = ofCoords 0 (Real.sqrt 10 / 5) 0 := by
  simp [stateVel, ofCoords, lineJet_apply, sStar]

lemma rnorm_lineJet0 {t : ℝ} (ht : -5 / 2 < t) :
    rnorm (lineJet 0 t) = 5 / 2 + t := by
  rw [rnorm, statePos_lineJet0, ofCoords_norm]
  simp
  exact Real.sqrt_sq (by linarith : 0 ≤ 5 / 2 + t)

lemma n0Of_lineJet0 (t : ℝ) :
    n0Of (lineJet 0 t) = ofCoords (3 / 2 + t) 0 0 := by
  apply (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).injective
  ext i
  fin_cases i <;> simp [n0Of, statePos_lineJet0, eJet0, ofCoords, PiLp.sub_apply] <;> ring

lemma n1Of_lineJet0 (t : ℝ) :
    n1Of (lineJet 0 t) = ofCoords 0 (Real.sqrt 10 / 5 - 1) 0 := by
  apply (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).injective
  ext i
  fin_cases i <;> simp [n1Of, stateVel_lineJet0, eJet1, ofCoords, PiLp.sub_apply]

lemma accelOf_lineJet0 {t : ℝ} (ht : -5 / 2 < t) :
    accelOf (lineJet 0 t) = ofCoords (-(5 / 2 + t)⁻¹ ^ 2) 0 0 := by
  have hpos : 0 < 5 / 2 + t := by linarith
  have hr : ‖ofCoords (5 / 2 + t) 0 0‖ = 5 / 2 + t := by
    rw [ofCoords_norm]
    simp [Real.sqrt_sq hpos.le]
  unfold accelOf
  rw [statePos_lineJet0, hr]
  apply (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).injective
  ext i
  fin_cases i
  · simp [ofCoords, PiLp.smul_apply, smul_eq_mul]
    have hne : 5 / 2 + t ≠ 0 := hpos.ne'
    field_simp [hne]
  · simp [ofCoords, PiLp.smul_apply, smul_eq_mul]
  · simp [ofCoords, PiLp.smul_apply, smul_eq_mul]

lemma n2Of_lineJet0 {t : ℝ} (ht : -5 / 2 < t) :
    n2Of (lineJet 0 t) = ofCoords (1 - (5 / 2 + t)⁻¹ ^ 2) 0 0 := by
  apply (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).injective
  ext i
  fin_cases i <;> simp [n2Of, accelOf_lineJet0 ht, eJet2, ofCoords, PiLp.sub_apply] <;> ring

lemma hasDerivAt_ofLp {f : ℝ → Vec} {f' : Vec} {t0 : ℝ}
    (hf : HasDerivAt f f' t0) (i : Fin 3) :
    HasDerivAt (fun t => (f t).ofLp i) (f'.ofLp i) t0 := by
  have h :=
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt
      t0 hf
  exact (hasDerivAt_pi.mp h) i

lemma eventually_lineJet0_pos : ∀ᶠ t : ℝ in 𝓝 0, -5 / 2 < t :=
  eventually_gt_nhds (by norm_num : (-5 / 2 : ℝ) < 0)

lemma vecDot_lineJet0 (t : ℝ) :
    vecDot (statePos (lineJet 0 t)) (stateVel (lineJet 0 t)) = 0 := by
  simp [vecDot, statePos_lineJet0, stateVel_lineJet0, ofLp_ofCoords, Fin.sum_univ_three]

lemma jerkOf_lineJet0 {t : ℝ} (ht : -5 / 2 < t) :
    jerkOf (lineJet 0 t) =
      ofCoords 0 (-(Real.sqrt 10 / 5) * (5 / 2 + t)⁻¹ ^ 3) 0 := by
  have hpos : 0 < 5 / 2 + t := by linarith
  have hr : ‖statePos (lineJet 0 t)‖ = 5 / 2 + t := rnorm_lineJet0 ht
  unfold jerkOf
  rw [hr, vecDot_lineJet0, stateVel_lineJet0, statePos_lineJet0]
  apply (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).injective
  ext i
  fin_cases i
  · simp [ofCoords, PiLp.smul_apply, PiLp.add_apply, smul_eq_mul]
  · simp [ofCoords, PiLp.smul_apply, PiLp.add_apply, smul_eq_mul]
    have hne : 5 / 2 + t ≠ 0 := hpos.ne'
    field_simp [hne]
  · simp [ofCoords, PiLp.smul_apply, PiLp.add_apply, smul_eq_mul]

lemma n3Of_lineJet0 {t : ℝ} (ht : -5 / 2 < t) :
    n3Of (lineJet 0 t) =
      ofCoords 0 (1 - (Real.sqrt 10 / 5) * (5 / 2 + t)⁻¹ ^ 3) 0 := by
  apply (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).injective
  ext i
  fin_cases i <;> simp [n3Of, jerkOf_lineJet0 ht, eJet3, ofCoords, PiLp.sub_apply] <;> ring

lemma qOf_lineJet0 (t : ℝ) : qOf (lineJet 0 t) = (3 / 2 + t) ^ 2 := by
  simp [qOf, vecDot, n0Of_lineJet0, ofLp_ofCoords, Fin.sum_univ_three]
  ring

lemma q1Of_lineJet0 (t : ℝ) : q1Of (lineJet 0 t) = 0 := by
  simp [q1Of, vecDot, n0Of_lineJet0, n1Of_lineJet0, ofLp_ofCoords, Fin.sum_univ_three]

lemma hasDerivAt_id_const_add (c t0 : ℝ) :
    HasDerivAt (fun t : ℝ => c + t) 1 t0 :=
  (hasDerivAt_id t0).const_add c

lemma hasDerivAt_inv_line0 :
    HasDerivAt (fun t : ℝ => (5 / 2 + t)⁻¹) (-4 / 25) 0 := by
  have hne : (5 / 2 + (0 : ℝ)) ≠ 0 := by norm_num
  have hinv := (hasDerivAt_id_const_add (5 / 2) 0).inv hne
  exact hinv.congr_deriv (by norm_num)

lemma hasDerivAt_pow2_at (a : ℝ) :
    HasDerivAt (fun x : ℝ => x ^ 2) (2 * a) a :=
  ((hasDerivAt_id a).pow 2).congr_deriv (by simp [id])

lemma hasDerivAt_pow3_at (a : ℝ) :
    HasDerivAt (fun x : ℝ => x ^ 3) (3 * a ^ 2) a :=
  ((hasDerivAt_id a).pow 3).congr_deriv (by simp [id])

lemma hasDerivAt_inv_pow2_line0 :
    HasDerivAt (fun t : ℝ => (5 / 2 + t)⁻¹ ^ 2) (-16 / 125) 0 := by
  have h := (hasDerivAt_pow2_at ((5 / 2 + (0 : ℝ))⁻¹)).comp 0 hasDerivAt_inv_line0
  exact h.congr_deriv (by norm_num)

lemma hasDerivAt_inv_pow3_line0 :
    HasDerivAt (fun t : ℝ => (5 / 2 + t)⁻¹ ^ 3) (-48 / 625) 0 := by
  have h := (hasDerivAt_pow3_at ((5 / 2 + (0 : ℝ))⁻¹)).comp 0 hasDerivAt_inv_line0
  exact h.congr_deriv (by norm_num)

lemma hasDerivAt_n0_lineJet0 :
    HasDerivAt (fun t => n0Of (lineJet 0 t)) (ofCoords 1 0 0) 0 := by
  have h := hasDerivAt_coord3
    ((hasDerivAt_id_const_add (3 / 2) 0)) (hasDerivAt_const 0 (0 : ℝ))
    (hasDerivAt_const 0 (0 : ℝ))
  exact h.congr_of_eventuallyEq (Eventually.of_forall n0Of_lineJet0)

lemma ofCoords_zero : (ofCoords 0 0 0 : Vec) = 0 := by
  apply (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).injective
  ext i; fin_cases i <;> simp [ofCoords]

lemma hasDerivAt_n1_lineJet0 :
    HasDerivAt (fun t => n1Of (lineJet 0 t)) (0 : Vec) 0 := by
  have h := hasDerivAt_coord3 (hasDerivAt_const 0 (0 : ℝ))
    (hasDerivAt_const 0 (Real.sqrt 10 / 5 - 1)) (hasDerivAt_const 0 (0 : ℝ))
  have h' : HasDerivAt (fun t => n1Of (lineJet 0 t)) (ofCoords 0 0 0) 0 :=
    h.congr_of_eventuallyEq (Eventually.of_forall n1Of_lineJet0)
  exact h'.congr_deriv ofCoords_zero

lemma hasDerivAt_n2_lineJet0 :
    HasDerivAt (fun t => n2Of (lineJet 0 t)) (ofCoords (16 / 125) 0 0) 0 := by
  have hx : HasDerivAt (fun t : ℝ => 1 - (5 / 2 + t)⁻¹ ^ 2) (16 / 125) 0 := by
    have h := (hasDerivAt_const 0 (1 : ℝ)).sub hasDerivAt_inv_pow2_line0
    exact h.congr_deriv (by ring)
  have h := hasDerivAt_coord3 hx (hasDerivAt_const 0 (0 : ℝ)) (hasDerivAt_const 0 (0 : ℝ))
  have heq : (fun t => n2Of (lineJet 0 t)) =ᶠ[𝓝 0]
      fun t => ofCoords (1 - (5 / 2 + t)⁻¹ ^ 2) 0 0 := by
    filter_upwards [eventually_lineJet0_pos] with t ht
    exact n2Of_lineJet0 ht
  exact h.congr_of_eventuallyEq heq

lemma hasDerivAt_n3_lineJet0 :
    HasDerivAt (fun t => n3Of (lineJet 0 t))
      (ofCoords 0 (48 * Real.sqrt 10 / 3125) 0) 0 := by
  have hy : HasDerivAt
      (fun t : ℝ => 1 - (Real.sqrt 10 / 5) * (5 / 2 + t)⁻¹ ^ 3)
      (48 * Real.sqrt 10 / 3125) 0 := by
    have h := (hasDerivAt_const 0 (1 : ℝ)).sub
      ((hasDerivAt_const 0 (Real.sqrt 10 / 5)).mul hasDerivAt_inv_pow3_line0)
    exact h.congr_deriv (by
      simp
      field_simp
      ring)
  have h := hasDerivAt_coord3 (hasDerivAt_const 0 (0 : ℝ)) hy
    (hasDerivAt_const 0 (0 : ℝ))
  have heq : (fun t => n3Of (lineJet 0 t)) =ᶠ[𝓝 0]
      fun t => ofCoords 0 (1 - (Real.sqrt 10 / 5) * (5 / 2 + t)⁻¹ ^ 3) 0 := by
    filter_upwards [eventually_lineJet0_pos] with t ht
    exact n3Of_lineJet0 ht
  exact h.congr_of_eventuallyEq heq

lemma hasDerivAt_q_lineJet0 :
    HasDerivAt (fun t => qOf (lineJet 0 t)) 3 0 := by
  have h := (hasDerivAt_pow2_at (3 / 2 + (0 : ℝ))).comp 0
    (hasDerivAt_id_const_add (3 / 2) 0)
  change HasDerivAt (fun t : ℝ => (3 / 2 + t) ^ 2) (2 * (3 / 2 + 0) * 1) 0 at h
  have hfeq : (2 * (3 / 2 + 0) * 1 : ℝ) = 3 := by norm_num
  have h' := h.congr_deriv hfeq
  exact h'.congr_of_eventuallyEq (Eventually.of_forall qOf_lineJet0)

lemma hasDerivAt_q1_lineJet0 :
    HasDerivAt (fun t => q1Of (lineJet 0 t)) 0 0 :=
  (hasDerivAt_const (0 : ℝ) (0 : ℝ)).congr_of_eventuallyEq
    (Eventually.of_forall q1Of_lineJet0)

lemma q2Of_lineJet0 {t : ℝ} (ht : -5 / 2 < t) :
    q2Of (lineJet 0 t) =
      2 * (Real.sqrt 10 / 5 - 1) ^ 2
        + 2 * (3 / 2 + t) * (1 - (5 / 2 + t)⁻¹ ^ 2) := by
  simp [q2Of, vecDot, n1Of_lineJet0, n0Of_lineJet0, n2Of_lineJet0 ht,
    ofLp_ofCoords, Fin.sum_univ_three]
  ring

lemma hasDerivAt_q2_lineJet0 :
    HasDerivAt (fun t => q2Of (lineJet 0 t)) (258 / 125) 0 := by
  have hx : HasDerivAt (fun t : ℝ => 1 - (5 / 2 + t)⁻¹ ^ 2) (16 / 125) 0 := by
    have h := (hasDerivAt_const 0 (1 : ℝ)).sub hasDerivAt_inv_pow2_line0
    exact h.congr_deriv (by ring)
  have hm := (hasDerivAt_id_const_add (3 / 2) 0).mul hx
  have h2 := HasDerivAt.const_mul (2 : ℝ) hm
  have hc := hasDerivAt_const (0 : ℝ) (2 * (Real.sqrt 10 / 5 - 1) ^ 2)
  have hadd := hc.add h2
  have hd :
      (0 : ℝ) + 2 * (1 * (1 - (5 / 2 + 0)⁻¹ ^ 2) + (3 / 2 + 0) * (16 / 125))
        = 258 / 125 := by norm_num
  have hadd' := hadd.congr_deriv hd
  have heq : (fun t => q2Of (lineJet 0 t)) =ᶠ[𝓝 (0 : ℝ)]
      fun t =>
        2 * (Real.sqrt 10 / 5 - 1) ^ 2
          + 2 * ((3 / 2 + t) * (1 - (5 / 2 + t)⁻¹ ^ 2)) := by
    filter_upwards [eventually_lineJet0_pos] with t ht
    simpa [mul_assoc] using q2Of_lineJet0 ht
  exact hadd'.congr_of_eventuallyEq heq

lemma q3Of_lineJet0 {t : ℝ} (ht : -5 / 2 < t) : q3Of (lineJet 0 t) = 0 := by
  simp [q3Of, vecDot, n1Of_lineJet0, n2Of_lineJet0 ht, n0Of_lineJet0, n3Of_lineJet0 ht,
    ofLp_ofCoords, Fin.sum_univ_three]

lemma hasDerivAt_q3_lineJet0 :
    HasDerivAt (fun t => q3Of (lineJet 0 t)) 0 0 := by
  have heq : (fun t => q3Of (lineJet 0 t)) =ᶠ[𝓝 (0 : ℝ)] fun _ => (0 : ℝ) := by
    filter_upwards [eventually_lineJet0_pos] with t ht
    exact q3Of_lineJet0 ht
  exact (hasDerivAt_const (0 : ℝ) (0 : ℝ)).congr_of_eventuallyEq heq

lemma pOf_lineJet0 {t : ℝ} (ht : -3 / 2 < t) :
    pOf (lineJet 0 t) = (3 / 2 + t)⁻¹ := by
  have hpos : 0 < 3 / 2 + t := by linarith
  unfold pOf
  rw [qOf_lineJet0]
  have : ((3 / 2 + t) ^ 2) ^ (-(1 / 2 : ℝ)) = (3 / 2 + t)⁻¹ := by
    have hsq : ((3 / 2 + t) ^ 2) ^ (1 / 2 : ℝ) = 3 / 2 + t := by
      rw [← Real.sqrt_eq_rpow, Real.sqrt_sq hpos.le]
    rw [Real.rpow_neg (sq_nonneg _), hsq]
  exact this

lemma hasDerivAt_p_lineJet0 :
    HasDerivAt (fun t => pOf (lineJet 0 t)) (-4 / 9) 0 := by
  have hinv : HasDerivAt (fun t : ℝ => (3 / 2 + t)⁻¹) (-4 / 9) 0 := by
    have hne : (3 / 2 + (0 : ℝ)) ≠ 0 := by norm_num
    have h := (hasDerivAt_id_const_add (3 / 2) 0).inv hne
    exact h.congr_deriv (by norm_num)
  have heq : (fun t => pOf (lineJet 0 t)) =ᶠ[𝓝 0] fun t => (3 / 2 + t)⁻¹ := by
    filter_upwards [eventually_gt_nhds (by norm_num : (-3 / 2 : ℝ) < 0)] with t ht
    exact pOf_lineJet0 ht
  exact hinv.congr_of_eventuallyEq heq

lemma p1Of_lineJet0 (t : ℝ) : p1Of (lineJet 0 t) = 0 := by
  simp [p1Of, q1Of_lineJet0]

lemma hasDerivAt_p1_lineJet0 :
    HasDerivAt (fun t => p1Of (lineJet 0 t)) 0 0 :=
  (hasDerivAt_const (0 : ℝ) (0 : ℝ)).congr_of_eventuallyEq
    (Eventually.of_forall p1Of_lineJet0)

lemma rpow_neg_three_halves_sq {t : ℝ} (ht : -3 / 2 < t) :
    ((3 / 2 + t) ^ 2) ^ (-(3 / 2 : ℝ)) = (3 / 2 + t)⁻¹ ^ 3 := by
  have hpos : 0 < 3 / 2 + t := by linarith
  have hsq : ((3 / 2 + t) ^ 2) ^ (3 / 2 : ℝ) = (3 / 2 + t) ^ 3 := by
    have hpow : ((3 / 2 + t) ^ 2) ^ (3 / 2 : ℝ)
        = ((3 / 2 + t) ^ 2) ^ (1 + 1 / 2 : ℝ) := by
      congr 1; norm_num
    rw [hpow, Real.rpow_add (sq_pos_of_pos hpos), Real.rpow_one, ← Real.sqrt_eq_rpow,
      Real.sqrt_sq hpos.le]
    ring
  rw [Real.rpow_neg (sq_nonneg _), hsq]
  field_simp [hpos.ne']

lemma p2Of_lineJet0 {t : ℝ} (ht : -3 / 2 < t) (_hr : -5 / 2 < t) :
    p2Of (lineJet 0 t) =
      -(1 / 2 : ℝ) * ((3 / 2 + t)⁻¹ ^ 3 * q2Of (lineJet 0 t)) := by
  unfold p2Of
  rw [qOf_lineJet0, q1Of_lineJet0]
  simp only [zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero, zero_sub]
  rw [rpow_neg_three_halves_sq ht]
  ring

lemma hasDerivAt_inv_pow3_q_line0 :
    HasDerivAt (fun t : ℝ => (3 / 2 + t)⁻¹ ^ 3) (-16 / 27) 0 := by
  have hinv : HasDerivAt (fun t : ℝ => (3 / 2 + t)⁻¹) (-4 / 9) 0 := by
    have hne : (3 / 2 + (0 : ℝ)) ≠ 0 := by norm_num
    have h := (hasDerivAt_id_const_add (3 / 2) 0).inv hne
    exact h.congr_deriv (by norm_num)
  have h := (hasDerivAt_pow3_at ((3 / 2 + (0 : ℝ))⁻¹)).comp 0 hinv
  exact h.congr_deriv (by norm_num)

lemma inv_three_halves_pow3 : (3 / 2 + (0 : ℝ))⁻¹ ^ 3 = 8 / 27 := by norm_num

lemma p2'_lineJet0 :
    (-(1 / 2 : ℝ)) *
        ((-16 / 27 : ℝ) * (133 / 25 - 4 * Real.sqrt 10 / 5)
          + (8 / 27) * (258 / 125))
      = (4288 - 800 * Real.sqrt 10) / 3375 := by
  field_simp
  ring

lemma hasDerivAt_p2_lineJet0 :
    HasDerivAt (fun t => p2Of (lineJet 0 t))
      ((4288 - 800 * Real.sqrt 10) / 3375) 0 := by
  have hA := hasDerivAt_inv_pow3_q_line0
  have hq2 := hasDerivAt_q2_lineJet0
  have hmul := hA.mul hq2
  have h := HasDerivAt.const_mul (-(1 / 2 : ℝ)) hmul
  have hd :
      (-(1 / 2 : ℝ)) *
          ((-16 / 27) * q2Of (lineJet 0 0)
            + (3 / 2 + (0 : ℝ))⁻¹ ^ 3 * (258 / 125))
        = (4288 - 800 * Real.sqrt 10) / 3375 := by
    have hq : q2Of (lineJet 0 0) = q2Of sStar := by rw [lineJet_zero]
    rw [hq, q2Of_sStar, inv_three_halves_pow3]
    exact p2'_lineJet0
  have h' := h.congr_deriv hd
  have heq : (fun t => p2Of (lineJet 0 t)) =ᶠ[𝓝 (0 : ℝ)]
      fun t =>
        -(1 / 2 : ℝ) * ((3 / 2 + t)⁻¹ ^ 3 * q2Of (lineJet 0 t)) := by
    filter_upwards [eventually_gt_nhds (by norm_num : (-3 / 2 : ℝ) < 0),
      eventually_lineJet0_pos] with t ht hr
    exact p2Of_lineJet0 ht hr
  exact h'.congr_of_eventuallyEq heq

lemma p3Of_lineJet0 {t : ℝ} (hr : -5 / 2 < t) : p3Of (lineJet 0 t) = 0 := by
  simp [p3Of, q1Of_lineJet0, q3Of_lineJet0 hr]

lemma hasDerivAt_p3_lineJet0 :
    HasDerivAt (fun t => p3Of (lineJet 0 t)) 0 0 := by
  have heq : (fun t => p3Of (lineJet 0 t)) =ᶠ[𝓝 (0 : ℝ)] fun _ => (0 : ℝ) := by
    filter_upwards [eventually_lineJet0_pos] with t hr
    exact p3Of_lineJet0 hr
  exact (hasDerivAt_const (0 : ℝ) (0 : ℝ)).congr_of_eventuallyEq heq

lemma u2Of_lineJet0 {t : ℝ} (_ht : -3 / 2 < t) (_hr : -5 / 2 < t) :
    u2Of (lineJet 0 t) =
      pOf (lineJet 0 t) • n2Of (lineJet 0 t)
        + p2Of (lineJet 0 t) • n0Of (lineJet 0 t) := by
  unfold u2Of
  rw [p1Of_lineJet0]
  simp

lemma two_jetA_eval :
    (2 / 3 : ℝ) * (16 / 125) + (-4 / 9) * (21 / 25)
      + (-532 / 675 + 16 * Real.sqrt 10 / 135)
      + ((4288 - 800 * Real.sqrt 10) / 3375) * (3 / 2)
      = 2 * jetA := by
  unfold jetA
  field_simp
  ring

lemma six_jetF_eval :
    (-4 / 9 : ℝ) * (1 - 8 * Real.sqrt 10 / 625)
      + (2 / 3) * (48 * Real.sqrt 10 / 3125)
      + 3 * (((4288 - 800 * Real.sqrt 10) / 3375) * (Real.sqrt 10 / 5 - 1))
      = 6 * jetF := by
  unfold jetF
  field_simp
  ring_nf
  simp [sqrt10_sq]
  ring

lemma hasDerivAt_u2_lineJet0 :
    HasDerivAt (fun t => u2Of (lineJet 0 t)) (ofCoords (2 * jetA) 0 0) 0 := by
  have hp := hasDerivAt_p_lineJet0
  have hn2 := hasDerivAt_n2_lineJet0
  have hp2 := hasDerivAt_p2_lineJet0
  have hn0 := hasDerivAt_n0_lineJet0
  have h1 := hp.smul hn2
  have h2 := hp2.smul hn0
  have hadd := h1.add h2
  have heq : (fun t => u2Of (lineJet 0 t)) =ᶠ[𝓝 (0 : ℝ)]
      fun t => pOf (lineJet 0 t) • n2Of (lineJet 0 t)
        + p2Of (lineJet 0 t) • n0Of (lineJet 0 t) := by
    filter_upwards [eventually_gt_nhds (by norm_num : (-3 / 2 : ℝ) < 0),
      eventually_lineJet0_pos] with t ht hr
    exact u2Of_lineJet0 ht hr
  have h' := hadd.congr_of_eventuallyEq heq
  have hv :
      pOf (lineJet 0 0) • ofCoords (16 / 125) 0 0
          + (-4 / 9 : ℝ) • n2Of (lineJet 0 0)
          + (p2Of (lineJet 0 0) • ofCoords 1 0 0
            + ((4288 - 800 * Real.sqrt 10) / 3375) • n0Of (lineJet 0 0))
        = ofCoords (2 * jetA) 0 0 := by
    rw [lineJet_zero, n2Of_sStar, n0Of_sStar, pOf_sStar, p2Of_sStar]
    apply (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).injective
    ext i
    fin_cases i
    · simp [ofCoords, PiLp.smul_apply, PiLp.add_apply, smul_eq_mul]
      simpa [mul_assoc, add_assoc, add_left_comm, add_comm, mul_comm, mul_left_comm]
        using two_jetA_eval
    · simp [ofCoords, PiLp.smul_apply, PiLp.add_apply, smul_eq_mul]
    · simp [ofCoords, PiLp.smul_apply, PiLp.add_apply, smul_eq_mul]
  exact h'.congr_deriv hv

lemma u3Of_lineJet0 {t : ℝ} (_ht : -3 / 2 < t) (hr : -5 / 2 < t) :
    u3Of (lineJet 0 t) =
      pOf (lineJet 0 t) • n3Of (lineJet 0 t)
        + (3 : ℝ) • (p2Of (lineJet 0 t) • n1Of (lineJet 0 t)) := by
  unfold u3Of
  rw [p1Of_lineJet0, p3Of_lineJet0 hr]
  simp

lemma hasDerivAt_u3_lineJet0 :
    HasDerivAt (fun t => u3Of (lineJet 0 t)) (ofCoords 0 (6 * jetF) 0) 0 := by
  have hp := hasDerivAt_p_lineJet0
  have hn3 := hasDerivAt_n3_lineJet0
  have hp2 := hasDerivAt_p2_lineJet0
  have hn1 := hasDerivAt_n1_lineJet0
  have h1 := hp.smul hn3
  have hmid := hp2.smul hn1
  have h3 := HasDerivAt.const_smul (3 : ℝ) hmid
  have hadd := h1.add h3
  have heq : (fun t => u3Of (lineJet 0 t)) =ᶠ[𝓝 (0 : ℝ)]
      fun t => pOf (lineJet 0 t) • n3Of (lineJet 0 t)
        + (3 : ℝ) • (p2Of (lineJet 0 t) • n1Of (lineJet 0 t)) := by
    filter_upwards [eventually_gt_nhds (by norm_num : (-3 / 2 : ℝ) < 0),
      eventually_lineJet0_pos] with t ht hr
    exact u3Of_lineJet0 ht hr
  have h' := hadd.congr_of_eventuallyEq heq
  have hv :
      pOf (lineJet 0 0) • ofCoords 0 (48 * Real.sqrt 10 / 3125) 0
          + (-4 / 9 : ℝ) • n3Of (lineJet 0 0)
          + (3 : ℝ) •
            (p2Of (lineJet 0 0) • (0 : Vec)
              + ((4288 - 800 * Real.sqrt 10) / 3375) • n1Of (lineJet 0 0))
        = ofCoords 0 (6 * jetF) 0 := by
    rw [lineJet_zero, n3Of_sStar, n1Of_sStar, pOf_sStar, p2Of_sStar]
    apply (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).injective
    ext i
    fin_cases i
    · simp [ofCoords, PiLp.smul_apply, PiLp.add_apply, smul_eq_mul]
    · simp [ofCoords, PiLp.smul_apply, PiLp.add_apply, smul_eq_mul]
      simpa [mul_assoc, add_assoc, add_left_comm, add_comm, mul_comm, mul_left_comm]
        using six_jetF_eval
    · simp [ofCoords, PiLp.smul_apply, PiLp.add_apply, smul_eq_mul]
  exact h'.congr_deriv hv

lemma hasDerivAt_losTaylor23_lineJet0 (i : Fin 6) :
    HasDerivAt (fun t => losTaylor23 (lineJet 0 t) i) (jetMatrix i 0) 0 := by
  have hu2 := hasDerivAt_u2_lineJet0
  have hu3 := hasDerivAt_u3_lineJet0
  fin_cases i
  · have h := (hasDerivAt_ofLp hu2 0).div_const (2 : ℝ)
    refine h.congr_deriv ?_
    simp [jetMatrix, ofLp_ofCoords]
  · have h := (hasDerivAt_ofLp hu2 1).div_const (2 : ℝ)
    refine h.congr_deriv ?_
    simp [jetMatrix, ofLp_ofCoords]
  · have h := (hasDerivAt_ofLp hu2 2).div_const (2 : ℝ)
    refine h.congr_deriv ?_
    simp [jetMatrix, ofLp_ofCoords]
  · have h := (hasDerivAt_ofLp hu3 0).div_const (6 : ℝ)
    refine h.congr_deriv ?_
    simp [jetMatrix, ofLp_ofCoords]
  · have h := (hasDerivAt_ofLp hu3 1).div_const (6 : ℝ)
    refine h.congr_deriv ?_
    simp [jetMatrix, ofLp_ofCoords]
  · have h := (hasDerivAt_ofLp hu3 2).div_const (6 : ℝ)
    refine h.congr_deriv ?_
    simp [jetMatrix, ofLp_ofCoords]

lemma deriv_losTaylor23_lineJet0 (i : Fin 6) :
    deriv (fun t => losTaylor23 (lineJet 0 t) i) 0 = jetMatrix i 0 :=
  (hasDerivAt_losTaylor23_lineJet0 i).deriv

lemma rpow_neg_five_halves_nine_four : (9 / 4 : ℝ) ^ (-(5 / 2 : ℝ)) = 32 / 243 := by
  have hpos : (0 : ℝ) < 9 / 4 := by norm_num
  rw [Real.rpow_neg hpos.le]
  have h52 : (9 / 4 : ℝ) ^ (5 / 2 : ℝ) = (9 / 4) ^ 2 * Real.sqrt (9 / 4) := by
    have : (5 / 2 : ℝ) = 2 + 1 / 2 := by norm_num
    rw [this, Real.rpow_add hpos, Real.rpow_two, Real.sqrt_eq_rpow]
  rw [h52, sqrt_nine_div_four]
  field_simp
  norm_num

lemma rpow_neg_seven_halves_nine_four : (9 / 4 : ℝ) ^ (-(7 / 2 : ℝ)) = 128 / 2187 := by
  have hpos : (0 : ℝ) < 9 / 4 := by norm_num
  rw [Real.rpow_neg hpos.le]
  have : (7 / 2 : ℝ) = (3 : ℝ) + 1 / 2 := by norm_num
  rw [this, Real.rpow_add hpos, ← Real.sqrt_eq_rpow, sqrt_nine_div_four]
  norm_num

lemma hasDerivAt_pow2_id :
    HasDerivAt (fun t : ℝ => t ^ 2) 0 0 :=
  (hasDerivAt_pow2_at 0).congr_deriv (by norm_num)

lemma hasDerivAt_five_halves_sq_add :
    HasDerivAt (fun t : ℝ => (5 / 2) ^ 2 + t ^ 2) 0 0 := by
  have h := (hasDerivAt_const 0 ((5 / 2 : ℝ) ^ 2)).add hasDerivAt_pow2_id
  exact h.congr_deriv (by norm_num)

lemma hasDerivAt_nine_four_sq_add :
    HasDerivAt (fun t : ℝ => (9 / 4 : ℝ) + t ^ 2) 0 0 := by
  have h := (hasDerivAt_const 0 (9 / 4 : ℝ)).add hasDerivAt_pow2_id
  exact h.congr_deriv (by norm_num)

lemma sqrt_25_4 : Real.sqrt ((5 / 2 : ℝ) ^ 2) = 5 / 2 := by
  exact Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 5 / 2)

lemma hasDerivAt_sqrt_five_halves_sq :
    HasDerivAt (fun t : ℝ => Real.sqrt ((5 / 2) ^ 2 + t ^ 2)) 0 0 := by
  have hpos : (0 : ℝ) < (5 / 2) ^ 2 + (0 : ℝ) ^ 2 := by norm_num
  have hs : HasDerivAt Real.sqrt (1 / (2 * Real.sqrt ((5 / 2) ^ 2 + 0 ^ 2)))
      ((5 / 2) ^ 2 + 0 ^ 2) :=
    Real.hasDerivAt_sqrt hpos.ne'
  have h := hs.comp 0 hasDerivAt_five_halves_sq_add
  refine h.congr_deriv ?_
  simp [sqrt_25_4]

/-! Axis 2: z-perturbation of position. -/

lemma statePos_lineJet2 (t : ℝ) :
    statePos (lineJet 2 t) = ofCoords (5 / 2) 0 t := by
  simp [statePos, ofCoords, lineJet_apply, sStar]

lemma stateVel_lineJet2 (t : ℝ) :
    stateVel (lineJet 2 t) = ofCoords 0 (Real.sqrt 10 / 5) 0 := by
  simp [stateVel, ofCoords, lineJet_apply, sStar]

lemma rnorm_lineJet2 (t : ℝ) :
    rnorm (lineJet 2 t) = Real.sqrt ((5 / 2) ^ 2 + t ^ 2) := by
  rw [rnorm, statePos_lineJet2, ofCoords_norm]
  simp

lemma hasDerivAt_rnorm_lineJet2 :
    HasDerivAt (fun t => rnorm (lineJet 2 t)) 0 0 :=
  hasDerivAt_sqrt_five_halves_sq.congr_of_eventuallyEq
    (Eventually.of_forall rnorm_lineJet2)

lemma vecDot_lineJet2 (t : ℝ) :
    vecDot (statePos (lineJet 2 t)) (stateVel (lineJet 2 t)) = 0 := by
  simp [vecDot, statePos_lineJet2, stateVel_lineJet2, ofLp_ofCoords, Fin.sum_univ_three]

lemma n0Of_lineJet2 (t : ℝ) :
    n0Of (lineJet 2 t) = ofCoords (3 / 2) 0 t := by
  apply (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).injective
  ext i
  fin_cases i <;> simp [n0Of, statePos_lineJet2, eJet0, ofCoords, PiLp.sub_apply] <;> ring

lemma n1Of_lineJet2 (t : ℝ) :
    n1Of (lineJet 2 t) = ofCoords 0 (Real.sqrt 10 / 5 - 1) 0 := by
  apply (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).injective
  ext i
  fin_cases i <;> simp [n1Of, stateVel_lineJet2, eJet1, ofCoords, PiLp.sub_apply]

lemma rnorm_lineJet2_ne {t : ℝ} : rnorm (lineJet 2 t) ≠ 0 := by
  rw [rnorm_lineJet2]
  exact Real.sqrt_ne_zero'.2 (by nlinarith [sq_nonneg t])

lemma accelOf_lineJet2 (t : ℝ) :
    accelOf (lineJet 2 t) =
      -((rnorm (lineJet 2 t)) ^ 3)⁻¹ • ofCoords (5 / 2) 0 t := by
  unfold accelOf
  rw [statePos_lineJet2]
  simp [rnorm, statePos_lineJet2]

lemma hasDerivAt_rnorm_inv_lineJet2 :
    HasDerivAt (fun t => (rnorm (lineJet 2 t))⁻¹) 0 0 := by
  have hne : rnorm (lineJet 2 0) ≠ 0 := rnorm_lineJet2_ne
  have h := hasDerivAt_rnorm_lineJet2.inv hne
  exact h.congr_deriv (by simp [rnorm_lineJet2, sqrt_25_4])

lemma hasDerivAt_rnorm_inv_pow3_lineJet2 :
    HasDerivAt (fun t => (rnorm (lineJet 2 t))⁻¹ ^ 3) 0 0 := by
  have h := (hasDerivAt_pow3_at ((rnorm (lineJet 2 0))⁻¹)).comp 0
    hasDerivAt_rnorm_inv_lineJet2
  refine h.congr_deriv ?_
  simp [rnorm_lineJet2, sqrt_25_4]

lemma hasDerivAt_n0_lineJet2 :
    HasDerivAt (fun t => n0Of (lineJet 2 t)) (ofCoords 0 0 1) 0 := by
  have h := hasDerivAt_coord3 (hasDerivAt_const 0 (3 / 2 : ℝ))
    (hasDerivAt_const 0 (0 : ℝ)) (hasDerivAt_id 0)
  exact h.congr_of_eventuallyEq (Eventually.of_forall n0Of_lineJet2)

lemma hasDerivAt_n1_lineJet2 :
    HasDerivAt (fun t => n1Of (lineJet 2 t)) (0 : Vec) 0 := by
  have h := hasDerivAt_coord3 (hasDerivAt_const 0 (0 : ℝ))
    (hasDerivAt_const 0 (Real.sqrt 10 / 5 - 1)) (hasDerivAt_const 0 (0 : ℝ))
  have h' : HasDerivAt (fun t => n1Of (lineJet 2 t)) (ofCoords 0 0 0) 0 :=
    h.congr_of_eventuallyEq (Eventually.of_forall n1Of_lineJet2)
  exact h'.congr_deriv ofCoords_zero

lemma hasDerivAt_pos_lineJet2 :
    HasDerivAt (fun t => statePos (lineJet 2 t)) (ofCoords 0 0 1) 0 := by
  have h := hasDerivAt_coord3 (hasDerivAt_const 0 (5 / 2 : ℝ))
    (hasDerivAt_const 0 (0 : ℝ)) (hasDerivAt_id 0)
  exact h.congr_of_eventuallyEq (Eventually.of_forall statePos_lineJet2)

lemma hasDerivAt_accel_lineJet2 :
    HasDerivAt (fun t => accelOf (lineJet 2 t)) (ofCoords 0 0 (-8 / 125)) 0 := by
  have hc := hasDerivAt_rnorm_inv_pow3_lineJet2
  have hf := hasDerivAt_pos_lineJet2
  have hneg : HasDerivAt (fun t => -((rnorm (lineJet 2 t))⁻¹ ^ 3)) 0 0 :=
    hc.neg.congr_deriv (by simp)
  -- accel = (- r^{-3}) • pos
  have h := hneg.smul hf
  have heq : (fun t => accelOf (lineJet 2 t)) =ᶠ[𝓝 (0 : ℝ)]
      fun t => (-((rnorm (lineJet 2 t))⁻¹ ^ 3)) • statePos (lineJet 2 t) :=
    Eventually.of_forall fun t => by
      simp [accelOf, rnorm, neg_smul]
  have h' := h.congr_of_eventuallyEq heq
  have hv :
      (-((rnorm (lineJet 2 0))⁻¹ ^ 3)) • ofCoords 0 0 1
          + (0 : ℝ) • statePos (lineJet 2 0)
        = ofCoords 0 0 (-8 / 125) := by
    have hr0 : rnorm (lineJet 2 0) = 5 / 2 := by
      rw [rnorm_lineJet2]
      simp [sqrt_25_4]
    rw [hr0]
    apply (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).injective
    ext i
    fin_cases i <;> simp [ofCoords, PiLp.smul_apply, PiLp.add_apply, smul_eq_mul] <;> norm_num
  exact h'.congr_deriv hv

lemma hasDerivAt_n2_lineJet2 :
    HasDerivAt (fun t => n2Of (lineJet 2 t)) (ofCoords 0 0 (-8 / 125)) 0 := by
  have h := hasDerivAt_accel_lineJet2.sub (hasDerivAt_const 0 eJet2)
  refine h.congr_deriv ?_
  simp [eJet2, ofCoords_zero]

lemma jerkOf_lineJet2 (t : ℝ) :
    jerkOf (lineJet 2 t) =
      -((rnorm (lineJet 2 t)) ^ 3)⁻¹ • stateVel (lineJet 2 t) := by
  unfold jerkOf
  rw [vecDot_lineJet2]
  simp [rnorm]

lemma hasDerivAt_vel_lineJet2 :
    HasDerivAt (fun t => stateVel (lineJet 2 t)) (0 : Vec) 0 := by
  have h := hasDerivAt_coord3 (hasDerivAt_const 0 (0 : ℝ))
    (hasDerivAt_const 0 (Real.sqrt 10 / 5)) (hasDerivAt_const 0 (0 : ℝ))
  have h' : HasDerivAt (fun t => stateVel (lineJet 2 t)) (ofCoords 0 0 0) 0 :=
    h.congr_of_eventuallyEq (Eventually.of_forall stateVel_lineJet2)
  exact h'.congr_deriv ofCoords_zero

lemma hasDerivAt_jerk_lineJet2 :
    HasDerivAt (fun t => jerkOf (lineJet 2 t)) (0 : Vec) 0 := by
  have hneg : HasDerivAt (fun t => -((rnorm (lineJet 2 t))⁻¹ ^ 3)) 0 0 :=
    hasDerivAt_rnorm_inv_pow3_lineJet2.neg.congr_deriv (by simp)
  have hv := hasDerivAt_vel_lineJet2
  have h := hneg.smul hv
  have heq : (fun t => jerkOf (lineJet 2 t)) =ᶠ[𝓝 (0 : ℝ)]
      fun t => (-((rnorm (lineJet 2 t))⁻¹ ^ 3)) • stateVel (lineJet 2 t) :=
    Eventually.of_forall fun t => by
      change jerkOf (lineJet 2 t) =
        (-((rnorm (lineJet 2 t))⁻¹ ^ 3)) • stateVel (lineJet 2 t)
      rw [jerkOf_lineJet2]
      have : ((rnorm (lineJet 2 t)) ^ 3)⁻¹ = (rnorm (lineJet 2 t))⁻¹ ^ 3 := by
        field_simp [rnorm_lineJet2_ne]
      rw [this, neg_smul]
  have h' := h.congr_of_eventuallyEq heq
  have hv0 :
      (-((rnorm (lineJet 2 0))⁻¹ ^ 3)) • (0 : Vec)
          + (0 : ℝ) • stateVel (lineJet 2 0) = (0 : Vec) := by
    simp
  exact h'.congr_deriv hv0

lemma hasDerivAt_n3_lineJet2 :
    HasDerivAt (fun t => n3Of (lineJet 2 t)) (0 : Vec) 0 := by
  have h := hasDerivAt_jerk_lineJet2.sub (hasDerivAt_const 0 eJet3)
  refine h.congr_deriv ?_
  simp

lemma qOf_lineJet2 (t : ℝ) : qOf (lineJet 2 t) = (9 / 4 : ℝ) + t ^ 2 := by
  simp [qOf, vecDot, n0Of_lineJet2, ofLp_ofCoords, Fin.sum_univ_three]
  ring

lemma hasDerivAt_q_lineJet2 :
    HasDerivAt (fun t => qOf (lineJet 2 t)) 0 0 :=
  hasDerivAt_nine_four_sq_add.congr_of_eventuallyEq
    (Eventually.of_forall qOf_lineJet2)

lemma q1Of_lineJet2 (t : ℝ) : q1Of (lineJet 2 t) = 0 := by
  simp [q1Of, vecDot, n0Of_lineJet2, n1Of_lineJet2, ofLp_ofCoords, Fin.sum_univ_three]

lemma hasDerivAt_q1_lineJet2 :
    HasDerivAt (fun t => q1Of (lineJet 2 t)) 0 0 :=
  (hasDerivAt_const (0 : ℝ) (0 : ℝ)).congr_of_eventuallyEq
    (Eventually.of_forall q1Of_lineJet2)

lemma inv_pow3_rnorm (s : Fin 6 → ℝ) :
    ((rnorm s) ^ 3)⁻¹ = (rnorm s)⁻¹ ^ 3 := by
  by_cases h : rnorm s = 0
  · simp [h]
  · field_simp [h]

lemma n2Of_lineJet2 (t : ℝ) :
    n2Of (lineJet 2 t) =
      ofCoords (1 - (5 / 2) * (rnorm (lineJet 2 t))⁻¹ ^ 3)
        0 (-t * (rnorm (lineJet 2 t))⁻¹ ^ 3) := by
  apply (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).injective
  ext i
  rw [n2Of, accelOf_lineJet2, inv_pow3_rnorm]
  fin_cases i
  · simp [eJet2, ofCoords, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
    ring
  · simp [eJet2, ofCoords, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
  · simp [eJet2, ofCoords, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
    ring

lemma n3Of_lineJet2 (t : ℝ) :
    n3Of (lineJet 2 t) =
      ofCoords 0 (1 - (Real.sqrt 10 / 5) * (rnorm (lineJet 2 t))⁻¹ ^ 3) 0 := by
  apply (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).injective
  ext i
  have hj : jerkOf (lineJet 2 t) =
      -((rnorm (lineJet 2 t))⁻¹ ^ 3) • stateVel (lineJet 2 t) := by
    rw [jerkOf_lineJet2, inv_pow3_rnorm]
  rw [stateVel_lineJet2] at hj
  fin_cases i
  · simp [n3Of, hj, eJet3, ofCoords, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
  · simp [n3Of, hj, eJet3, ofCoords, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
    ring
  · simp [n3Of, hj, eJet3, ofCoords, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]

lemma q2Of_lineJet2 (t : ℝ) :
    q2Of (lineJet 2 t) =
      2 * (Real.sqrt 10 / 5 - 1) ^ 2
        + 3 * (1 - (5 / 2) * (rnorm (lineJet 2 t))⁻¹ ^ 3)
        - 2 * t ^ 2 * (rnorm (lineJet 2 t))⁻¹ ^ 3 := by
  simp [q2Of, vecDot, n1Of_lineJet2, n0Of_lineJet2, n2Of_lineJet2, ofLp_ofCoords,
    Fin.sum_univ_three]
  ring

lemma hasDerivAt_t_sq_rinv3_lineJet2 :
    HasDerivAt (fun t => t ^ 2 * (rnorm (lineJet 2 t))⁻¹ ^ 3) 0 0 := by
  have h := hasDerivAt_pow2_id.mul hasDerivAt_rnorm_inv_pow3_lineJet2
  exact h.congr_deriv (by simp [rnorm_lineJet2, sqrt_25_4])

lemma hasDerivAt_q2_lineJet2 :
    HasDerivAt (fun t => q2Of (lineJet 2 t)) 0 0 := by
  have hc := hasDerivAt_const (0 : ℝ) (2 * (Real.sqrt 10 / 5 - 1) ^ 2)
  have hr := hasDerivAt_rnorm_inv_pow3_lineJet2
  have hmid : HasDerivAt
      (fun t : ℝ => 1 - (5 / 2) * (rnorm (lineJet 2 t))⁻¹ ^ 3) 0 0 := by
    have h := (hasDerivAt_const 0 (1 : ℝ)).sub
      ((hasDerivAt_const 0 (5 / 2 : ℝ)).mul hr)
    exact h.congr_deriv (by simp)
  have h3 := HasDerivAt.const_mul (3 : ℝ) hmid
  have ht := hasDerivAt_t_sq_rinv3_lineJet2
  have h2t := HasDerivAt.const_mul (2 : ℝ) ht
  have hadd := (hc.add h3).sub h2t
  have heq : (fun t => q2Of (lineJet 2 t)) =ᶠ[𝓝 (0 : ℝ)]
      fun t =>
        2 * (Real.sqrt 10 / 5 - 1) ^ 2
          + 3 * (1 - (5 / 2) * (rnorm (lineJet 2 t))⁻¹ ^ 3)
          - 2 * (t ^ 2 * (rnorm (lineJet 2 t))⁻¹ ^ 3) :=
    Eventually.of_forall fun t => by simpa [mul_assoc] using q2Of_lineJet2 t
  exact hadd.congr_of_eventuallyEq heq |>.congr_deriv (by ring)

lemma q3Of_lineJet2 (t : ℝ) : q3Of (lineJet 2 t) = 0 := by
  simp [q3Of, vecDot, n1Of_lineJet2, n2Of_lineJet2, n0Of_lineJet2, n3Of_lineJet2,
    ofLp_ofCoords, Fin.sum_univ_three]

lemma hasDerivAt_q3_lineJet2 :
    HasDerivAt (fun t => q3Of (lineJet 2 t)) 0 0 :=
  (hasDerivAt_const (0 : ℝ) (0 : ℝ)).congr_of_eventuallyEq
    (Eventually.of_forall q3Of_lineJet2)

lemma pOf_lineJet2 (t : ℝ) :
    pOf (lineJet 2 t) = ((9 / 4 : ℝ) + t ^ 2) ^ (-(1 / 2 : ℝ)) := by
  unfold pOf
  rw [qOf_lineJet2]

lemma hasDerivAt_rpow_neg_half_at_nine_four :
    HasDerivAt (fun x : ℝ => x ^ (-(1 / 2 : ℝ))) (-(4 / 27 : ℝ)) (9 / 4) := by
  have hx : (0 : ℝ) < 9 / 4 := by norm_num
  have h := Real.hasDerivAt_rpow_const (x := (9 / 4 : ℝ)) (p := -(1 / 2 : ℝ))
    (Or.inl hx.ne')
  refine h.congr_deriv ?_
  have : -(1 / 2 : ℝ) - 1 = -(3 / 2) := by norm_num
  rw [this, rpow_neg_three_halves_nine_four]
  field_simp
  ring

lemma hasDerivAt_p_lineJet2 :
    HasDerivAt (fun t => pOf (lineJet 2 t)) 0 0 := by
  have hpt : (9 / 4 : ℝ) + (0 : ℝ) ^ 2 = 9 / 4 := by norm_num
  have hr : HasDerivAt (fun x : ℝ => x ^ (-(1 / 2 : ℝ))) (-(4 / 27 : ℝ))
      ((9 / 4 : ℝ) + 0 ^ 2) := by
    rw [hpt]; exact hasDerivAt_rpow_neg_half_at_nine_four
  have h := hr.comp 0 hasDerivAt_nine_four_sq_add
  have h0 : HasDerivAt ((fun x : ℝ => x ^ (-(1 / 2 : ℝ))) ∘ fun t : ℝ => 9 / 4 + t ^ 2)
      0 0 := h.congr_deriv (mul_zero _)
  refine h0.congr_of_eventuallyEq ?_
  exact Eventually.of_forall pOf_lineJet2

lemma p1Of_lineJet2 (t : ℝ) : p1Of (lineJet 2 t) = 0 := by
  simp [p1Of, q1Of_lineJet2]

lemma hasDerivAt_p1_lineJet2 :
    HasDerivAt (fun t => p1Of (lineJet 2 t)) 0 0 :=
  (hasDerivAt_const (0 : ℝ) (0 : ℝ)).congr_of_eventuallyEq
    (Eventually.of_forall p1Of_lineJet2)

lemma hasDerivAt_rpow_neg_three_halves_at_nine_four :
    HasDerivAt (fun x : ℝ => x ^ (-(3 / 2 : ℝ))) (-(16 / 81 : ℝ)) (9 / 4) := by
  have hx : (0 : ℝ) < 9 / 4 := by norm_num
  have h := Real.hasDerivAt_rpow_const (x := (9 / 4 : ℝ)) (p := -(3 / 2 : ℝ))
    (Or.inl hx.ne')
  refine h.congr_deriv ?_
  have : -(3 / 2 : ℝ) - 1 = -(5 / 2) := by norm_num
  rw [this, rpow_neg_five_halves_nine_four]
  field_simp
  ring

lemma hasDerivAt_q_rpow_neg_three_halves_lineJet2 :
    HasDerivAt (fun t => (qOf (lineJet 2 t)) ^ (-(3 / 2 : ℝ))) 0 0 := by
  have hq : qOf (lineJet 2 0) = 9 / 4 := by
    rw [qOf_lineJet2]; simp
  have hr : HasDerivAt (fun x : ℝ => x ^ (-(3 / 2 : ℝ))) (-(16 / 81 : ℝ))
      (qOf (lineJet 2 0)) := by
    rw [hq]; exact hasDerivAt_rpow_neg_three_halves_at_nine_four
  have h := hr.comp 0 hasDerivAt_q_lineJet2
  exact h.congr_deriv (by simp)

lemma p2Of_lineJet2 (t : ℝ) :
    p2Of (lineJet 2 t) =
      -(1 / 2 : ℝ) * ((qOf (lineJet 2 t)) ^ (-(3 / 2 : ℝ)) * q2Of (lineJet 2 t)) := by
  unfold p2Of
  rw [q1Of_lineJet2]
  simp only [zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero, zero_sub]
  ring

lemma hasDerivAt_p2_lineJet2 :
    HasDerivAt (fun t => p2Of (lineJet 2 t)) 0 0 := by
  have hA := hasDerivAt_q_rpow_neg_three_halves_lineJet2
  have hq2 := hasDerivAt_q2_lineJet2
  have hmul := hA.mul hq2
  have h := HasDerivAt.const_mul (-(1 / 2 : ℝ)) hmul
  have hd :
      (-(1 / 2 : ℝ)) *
          (0 * q2Of (lineJet 2 0)
            + (qOf (lineJet 2 0)) ^ (-(3 / 2 : ℝ)) * 0) = 0 := by
    ring
  have h' := h.congr_deriv hd
  have heq : (fun t => p2Of (lineJet 2 t)) =ᶠ[𝓝 (0 : ℝ)]
      fun t =>
        -(1 / 2 : ℝ) * ((qOf (lineJet 2 t)) ^ (-(3 / 2 : ℝ)) * q2Of (lineJet 2 t)) :=
    Eventually.of_forall p2Of_lineJet2
  exact h'.congr_of_eventuallyEq heq

lemma p3Of_lineJet2 (t : ℝ) : p3Of (lineJet 2 t) = 0 := by
  simp [p3Of, q1Of_lineJet2, q3Of_lineJet2]

lemma hasDerivAt_p3_lineJet2 :
    HasDerivAt (fun t => p3Of (lineJet 2 t)) 0 0 :=
  (hasDerivAt_const (0 : ℝ) (0 : ℝ)).congr_of_eventuallyEq
    (Eventually.of_forall p3Of_lineJet2)

lemma u2Of_lineJet2 (t : ℝ) :
    u2Of (lineJet 2 t) =
      pOf (lineJet 2 t) • n2Of (lineJet 2 t)
        + p2Of (lineJet 2 t) • n0Of (lineJet 2 t) := by
  unfold u2Of
  rw [p1Of_lineJet2]
  simp

lemma two_jetD_eval :
    (2 / 3 : ℝ) * (-8 / 125)
      + (-532 / 675 + 16 * Real.sqrt 10 / 135)
      = 2 * jetD := by
  unfold jetD
  field_simp
  ring

lemma hasDerivAt_u2_lineJet2 :
    HasDerivAt (fun t => u2Of (lineJet 2 t)) (ofCoords 0 0 (2 * jetD)) 0 := by
  have hp := hasDerivAt_p_lineJet2
  have hn2 := hasDerivAt_n2_lineJet2
  have hp2 := hasDerivAt_p2_lineJet2
  have hn0 := hasDerivAt_n0_lineJet2
  have h1 := hp.smul hn2
  have h2 := hp2.smul hn0
  have hadd := h1.add h2
  have heq : (fun t => u2Of (lineJet 2 t)) =ᶠ[𝓝 (0 : ℝ)]
      fun t => pOf (lineJet 2 t) • n2Of (lineJet 2 t)
        + p2Of (lineJet 2 t) • n0Of (lineJet 2 t) :=
    Eventually.of_forall u2Of_lineJet2
  have h' := hadd.congr_of_eventuallyEq heq
  have hv :
      pOf (lineJet 2 0) • ofCoords 0 0 (-8 / 125)
          + (0 : ℝ) • n2Of (lineJet 2 0)
          + (p2Of (lineJet 2 0) • ofCoords 0 0 1
            + (0 : ℝ) • n0Of (lineJet 2 0))
        = ofCoords 0 0 (2 * jetD) := by
    rw [lineJet_zero, n2Of_sStar, n0Of_sStar, pOf_sStar, p2Of_sStar]
    apply (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).injective
    ext i
    fin_cases i
    · simp [ofCoords, PiLp.smul_apply, PiLp.add_apply, smul_eq_mul]
    · simp [ofCoords, PiLp.smul_apply, PiLp.add_apply, smul_eq_mul]
    · simp [ofCoords, PiLp.smul_apply, PiLp.add_apply, smul_eq_mul]
      simpa [mul_assoc, add_assoc, add_left_comm, add_comm, mul_comm, mul_left_comm]
        using two_jetD_eval
  exact h'.congr_deriv hv

lemma u3Of_lineJet2 (t : ℝ) :
    u3Of (lineJet 2 t) =
      pOf (lineJet 2 t) • n3Of (lineJet 2 t)
        + (3 : ℝ) • (p2Of (lineJet 2 t) • n1Of (lineJet 2 t)) := by
  unfold u3Of
  rw [p1Of_lineJet2, p3Of_lineJet2]
  simp

lemma hasDerivAt_u3_lineJet2 :
    HasDerivAt (fun t => u3Of (lineJet 2 t)) (0 : Vec) 0 := by
  have hp := hasDerivAt_p_lineJet2
  have hn3 := hasDerivAt_n3_lineJet2
  have hp2 := hasDerivAt_p2_lineJet2
  have hn1 := hasDerivAt_n1_lineJet2
  have h1 := hp.smul hn3
  have hmid := hp2.smul hn1
  have h3 := HasDerivAt.const_smul (3 : ℝ) hmid
  have hadd := h1.add h3
  have heq : (fun t => u3Of (lineJet 2 t)) =ᶠ[𝓝 (0 : ℝ)]
      fun t => pOf (lineJet 2 t) • n3Of (lineJet 2 t)
        + (3 : ℝ) • (p2Of (lineJet 2 t) • n1Of (lineJet 2 t)) :=
    Eventually.of_forall u3Of_lineJet2
  have h' := hadd.congr_of_eventuallyEq heq
  have hv :
      pOf (lineJet 2 0) • (0 : Vec)
          + (0 : ℝ) • n3Of (lineJet 2 0)
          + (3 : ℝ) •
            (p2Of (lineJet 2 0) • (0 : Vec) + (0 : ℝ) • n1Of (lineJet 2 0))
        = (0 : Vec) := by
    simp
  exact h'.congr_deriv hv

lemma hasDerivAt_losTaylor23_lineJet2 (i : Fin 6) :
    HasDerivAt (fun t => losTaylor23 (lineJet 2 t) i) (jetMatrix i 2) 0 := by
  have hu2 := hasDerivAt_u2_lineJet2
  have hu3 := hasDerivAt_u3_lineJet2
  fin_cases i
  · have h := (hasDerivAt_ofLp hu2 0).div_const (2 : ℝ)
    refine h.congr_deriv ?_
    simp [jetMatrix, ofLp_ofCoords]
  · have h := (hasDerivAt_ofLp hu2 1).div_const (2 : ℝ)
    refine h.congr_deriv ?_
    simp [jetMatrix, ofLp_ofCoords]
  · have h := (hasDerivAt_ofLp hu2 2).div_const (2 : ℝ)
    refine h.congr_deriv ?_
    simp [jetMatrix, ofLp_ofCoords]
  · have h := (hasDerivAt_ofLp hu3 0).div_const (6 : ℝ)
    refine h.congr_deriv ?_
    simp [jetMatrix, ofLp_ofCoords]
  · have h := (hasDerivAt_ofLp hu3 1).div_const (6 : ℝ)
    refine h.congr_deriv ?_
    simp [jetMatrix, ofLp_ofCoords]
  · have h := (hasDerivAt_ofLp hu3 2).div_const (6 : ℝ)
    refine h.congr_deriv ?_
    simp [jetMatrix, ofLp_ofCoords]

lemma deriv_losTaylor23_lineJet2 (i : Fin 6) :
    deriv (fun t => losTaylor23 (lineJet 2 t) i) 0 = jetMatrix i 2 :=
  (hasDerivAt_losTaylor23_lineJet2 i).deriv

/-! Axis 5: vz-perturbation. Position is fixed at `sStar`; many q-jets vanish. -/

lemma statePos_lineJet5 (t : ℝ) :
    statePos (lineJet 5 t) = ofCoords (5 / 2) 0 0 := by
  simp [statePos, ofCoords, lineJet_apply, sStar]

lemma stateVel_lineJet5 (t : ℝ) :
    stateVel (lineJet 5 t) = ofCoords 0 (Real.sqrt 10 / 5) t := by
  simp [stateVel, ofCoords, lineJet_apply, sStar]

lemma rnorm_lineJet5 (t : ℝ) : rnorm (lineJet 5 t) = 5 / 2 := by
  rw [rnorm, statePos_lineJet5, ofCoords_norm]
  simp [sqrt_25_4]

lemma vecDot_lineJet5 (t : ℝ) :
    vecDot (statePos (lineJet 5 t)) (stateVel (lineJet 5 t)) = 0 := by
  simp [vecDot, statePos_lineJet5, stateVel_lineJet5, ofLp_ofCoords, Fin.sum_univ_three]

lemma n0Of_lineJet5 (t : ℝ) :
    n0Of (lineJet 5 t) = ofCoords (3 / 2) 0 0 := by
  apply (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).injective
  ext i
  fin_cases i <;> simp [n0Of, statePos_lineJet5, eJet0, ofCoords, PiLp.sub_apply] <;> ring

lemma n1Of_lineJet5 (t : ℝ) :
    n1Of (lineJet 5 t) = ofCoords 0 (Real.sqrt 10 / 5 - 1) t := by
  apply (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).injective
  ext i
  fin_cases i <;> simp [n1Of, stateVel_lineJet5, eJet1, ofCoords, PiLp.sub_apply]

lemma accelOf_lineJet5 (t : ℝ) :
    accelOf (lineJet 5 t) = ofCoords (-4 / 25) 0 0 := by
  unfold accelOf
  rw [statePos_lineJet5]
  have hr : ‖ofCoords (5 / 2 : ℝ) 0 0‖ = 5 / 2 := by
    rw [ofCoords_norm]; simp [sqrt_25_4]
  rw [hr]
  apply (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).injective
  ext i
  fin_cases i <;> simp [ofCoords, PiLp.smul_apply, smul_eq_mul] <;> norm_num

lemma n2Of_lineJet5 (t : ℝ) :
    n2Of (lineJet 5 t) = ofCoords (21 / 25) 0 0 := by
  apply (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).injective
  ext i
  fin_cases i <;> simp [n2Of, accelOf_lineJet5, eJet2, ofCoords, PiLp.sub_apply] <;> norm_num

lemma jerkOf_lineJet5 (t : ℝ) :
    jerkOf (lineJet 5 t) =
      ofCoords 0 (-8 * Real.sqrt 10 / 625) (-8 * t / 125) := by
  unfold jerkOf
  rw [show ‖statePos (lineJet 5 t)‖ = (5 / 2 : ℝ) from rnorm_lineJet5 t,
    vecDot_lineJet5, stateVel_lineJet5, statePos_lineJet5]
  apply (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).injective
  ext i
  fin_cases i <;> simp [ofCoords, PiLp.smul_apply, PiLp.add_apply, smul_eq_mul]
  · field_simp; ring
  · field_simp; ring

lemma n3Of_lineJet5 (t : ℝ) :
    n3Of (lineJet 5 t) =
      ofCoords 0 (1 - 8 * Real.sqrt 10 / 625) (-8 * t / 125) := by
  apply (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).injective
  ext i
  fin_cases i <;> simp [n3Of, jerkOf_lineJet5, eJet3, ofCoords, PiLp.sub_apply] <;> ring

lemma qOf_lineJet5 (t : ℝ) : qOf (lineJet 5 t) = 9 / 4 := by
  simp [qOf, vecDot, n0Of_lineJet5, ofLp_ofCoords, Fin.sum_univ_three]
  norm_num

lemma q1Of_lineJet5 (t : ℝ) : q1Of (lineJet 5 t) = 0 := by
  simp [q1Of, vecDot, n0Of_lineJet5, n1Of_lineJet5, ofLp_ofCoords, Fin.sum_univ_three]

lemma q2Of_lineJet5 (t : ℝ) :
    q2Of (lineJet 5 t) = 2 * t ^ 2 + (133 / 25 - 4 * Real.sqrt 10 / 5) := by
  simp [q2Of, vecDot, n1Of_lineJet5, n0Of_lineJet5, n2Of_lineJet5, ofLp_ofCoords,
    Fin.sum_univ_three]
  field_simp
  ring_nf
  simp [sqrt10_sq]
  ring

lemma q3Of_lineJet5 (t : ℝ) : q3Of (lineJet 5 t) = 0 := by
  simp [q3Of, vecDot, n1Of_lineJet5, n2Of_lineJet5, n0Of_lineJet5, n3Of_lineJet5,
    ofLp_ofCoords, Fin.sum_univ_three]

lemma pOf_lineJet5 (t : ℝ) : pOf (lineJet 5 t) = 2 / 3 := by
  unfold pOf
  rw [qOf_lineJet5, rpow_neg_half_nine_four]

lemma p1Of_lineJet5 (t : ℝ) : p1Of (lineJet 5 t) = 0 := by
  simp [p1Of, q1Of_lineJet5]

lemma p2Of_lineJet5 (t : ℝ) :
    p2Of (lineJet 5 t) =
      -(1 / 2 : ℝ) * ((9 / 4 : ℝ) ^ (-(3 / 2 : ℝ)) * q2Of (lineJet 5 t)) := by
  unfold p2Of
  rw [qOf_lineJet5, q1Of_lineJet5]
  simp only [zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero, zero_sub]
  ring

lemma p3Of_lineJet5 (t : ℝ) : p3Of (lineJet 5 t) = 0 := by
  simp [p3Of, q1Of_lineJet5, q3Of_lineJet5]

lemma hasDerivAt_n0_lineJet5 :
    HasDerivAt (fun t => n0Of (lineJet 5 t)) (0 : Vec) 0 := by
  have h := hasDerivAt_coord3 (hasDerivAt_const 0 (3 / 2 : ℝ))
    (hasDerivAt_const 0 (0 : ℝ)) (hasDerivAt_const 0 (0 : ℝ))
  have h' : HasDerivAt (fun t => n0Of (lineJet 5 t)) (ofCoords 0 0 0) 0 :=
    h.congr_of_eventuallyEq (Eventually.of_forall n0Of_lineJet5)
  exact h'.congr_deriv ofCoords_zero

lemma hasDerivAt_n1_lineJet5 :
    HasDerivAt (fun t => n1Of (lineJet 5 t)) (ofCoords 0 0 1) 0 := by
  have h := hasDerivAt_coord3 (hasDerivAt_const 0 (0 : ℝ))
    (hasDerivAt_const 0 (Real.sqrt 10 / 5 - 1)) (hasDerivAt_id 0)
  exact h.congr_of_eventuallyEq (Eventually.of_forall n1Of_lineJet5)

lemma hasDerivAt_n2_lineJet5 :
    HasDerivAt (fun t => n2Of (lineJet 5 t)) (0 : Vec) 0 :=
  (hasDerivAt_const (0 : ℝ) (ofCoords (21 / 25) 0 0)).congr_of_eventuallyEq
    (Eventually.of_forall n2Of_lineJet5) |>.congr_deriv (by
      apply (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).injective
      ext i; fin_cases i <;> simp [ofCoords])

lemma hasDerivAt_n3_lineJet5 :
    HasDerivAt (fun t => n3Of (lineJet 5 t)) (ofCoords 0 0 (-8 / 125)) 0 := by
  have hz0 : HasDerivAt (fun t : ℝ => (-8 / 125 : ℝ) * t) (-8 / 125) 0 :=
    ((hasDerivAt_id (0 : ℝ)).const_mul (-8 / 125 : ℝ)).congr_deriv (by simp)
  have hz : HasDerivAt (fun t : ℝ => -8 * t / 125) (-8 / 125) 0 :=
    hz0.congr_of_eventuallyEq (Eventually.of_forall fun t => by field_simp)
  have h := hasDerivAt_coord3 (hasDerivAt_const 0 (0 : ℝ))
    (hasDerivAt_const 0 (1 - 8 * Real.sqrt 10 / 625)) hz
  exact h.congr_of_eventuallyEq (Eventually.of_forall n3Of_lineJet5)

lemma hasDerivAt_q_lineJet5 :
    HasDerivAt (fun t => qOf (lineJet 5 t)) 0 0 :=
  (hasDerivAt_const (0 : ℝ) (9 / 4 : ℝ)).congr_of_eventuallyEq
    (Eventually.of_forall qOf_lineJet5)

lemma hasDerivAt_q1_lineJet5 :
    HasDerivAt (fun t => q1Of (lineJet 5 t)) 0 0 :=
  (hasDerivAt_const (0 : ℝ) (0 : ℝ)).congr_of_eventuallyEq
    (Eventually.of_forall q1Of_lineJet5)

lemma hasDerivAt_q2_lineJet5 :
    HasDerivAt (fun t => q2Of (lineJet 5 t)) 0 0 := by
  have h2 : HasDerivAt (fun t : ℝ => 2 * t ^ 2) 0 0 :=
    (HasDerivAt.const_mul (2 : ℝ) hasDerivAt_pow2_id).congr_deriv (by simp)
  have h : HasDerivAt
      ((fun _ : ℝ => 133 / 25 - 4 * Real.sqrt 10 / 5) + fun t => 2 * t ^ 2) 0 0 :=
    (hasDerivAt_const 0 (133 / 25 - 4 * Real.sqrt 10 / 5)).add h2 |>.congr_deriv (by ring)
  exact h.congr_of_eventuallyEq (Eventually.of_forall fun t => by
    simpa [add_comm] using q2Of_lineJet5 t)

lemma hasDerivAt_q3_lineJet5 :
    HasDerivAt (fun t => q3Of (lineJet 5 t)) 0 0 :=
  (hasDerivAt_const (0 : ℝ) (0 : ℝ)).congr_of_eventuallyEq
    (Eventually.of_forall q3Of_lineJet5)

lemma hasDerivAt_p_lineJet5 :
    HasDerivAt (fun t => pOf (lineJet 5 t)) 0 0 :=
  (hasDerivAt_const (0 : ℝ) (2 / 3 : ℝ)).congr_of_eventuallyEq
    (Eventually.of_forall pOf_lineJet5)

lemma hasDerivAt_p1_lineJet5 :
    HasDerivAt (fun t => p1Of (lineJet 5 t)) 0 0 :=
  (hasDerivAt_const (0 : ℝ) (0 : ℝ)).congr_of_eventuallyEq
    (Eventually.of_forall p1Of_lineJet5)

lemma hasDerivAt_p2_lineJet5 :
    HasDerivAt (fun t => p2Of (lineJet 5 t)) 0 0 := by
  have hq2 := hasDerivAt_q2_lineJet5
  have hA := hasDerivAt_const (0 : ℝ) ((9 / 4 : ℝ) ^ (-(3 / 2 : ℝ)))
  have hmul := hA.mul hq2
  have h := HasDerivAt.const_mul (-(1 / 2 : ℝ)) hmul
  have hd :
      (-(1 / 2 : ℝ)) *
          (0 * q2Of (lineJet 5 0)
            + (9 / 4 : ℝ) ^ (-(3 / 2 : ℝ)) * 0) = 0 := by
    ring
  have h' := h.congr_deriv hd
  exact h'.congr_of_eventuallyEq (Eventually.of_forall p2Of_lineJet5)

lemma hasDerivAt_p3_lineJet5 :
    HasDerivAt (fun t => p3Of (lineJet 5 t)) 0 0 :=
  (hasDerivAt_const (0 : ℝ) (0 : ℝ)).congr_of_eventuallyEq
    (Eventually.of_forall p3Of_lineJet5)

lemma u2Of_lineJet5 (t : ℝ) :
    u2Of (lineJet 5 t) =
      pOf (lineJet 5 t) • n2Of (lineJet 5 t)
        + p2Of (lineJet 5 t) • n0Of (lineJet 5 t) := by
  unfold u2Of
  rw [p1Of_lineJet5]
  simp

lemma hasDerivAt_u2_lineJet5 :
    HasDerivAt (fun t => u2Of (lineJet 5 t)) (0 : Vec) 0 := by
  have hp := hasDerivAt_p_lineJet5
  have hn2 := hasDerivAt_n2_lineJet5
  have hp2 := hasDerivAt_p2_lineJet5
  have hn0 := hasDerivAt_n0_lineJet5
  have h1 := hp.smul hn2
  have h2 := hp2.smul hn0
  have hadd := h1.add h2
  have heq : (fun t => u2Of (lineJet 5 t)) =ᶠ[𝓝 (0 : ℝ)]
      fun t => pOf (lineJet 5 t) • n2Of (lineJet 5 t)
        + p2Of (lineJet 5 t) • n0Of (lineJet 5 t) :=
    Eventually.of_forall u2Of_lineJet5
  have h' := hadd.congr_of_eventuallyEq heq
  exact h'.congr_deriv (by simp)

lemma u3Of_lineJet5 (t : ℝ) :
    u3Of (lineJet 5 t) =
      pOf (lineJet 5 t) • n3Of (lineJet 5 t)
        + (3 : ℝ) • (p2Of (lineJet 5 t) • n1Of (lineJet 5 t)) := by
  unfold u3Of
  rw [p1Of_lineJet5, p3Of_lineJet5]
  simp

lemma six_jetH_eval :
    (2 / 3 : ℝ) * (-8 / 125)
      + 3 * (-532 / 675 + 16 * Real.sqrt 10 / 135)
      = 6 * jetH := by
  unfold jetH
  field_simp
  ring

lemma hasDerivAt_u3_lineJet5 :
    HasDerivAt (fun t => u3Of (lineJet 5 t)) (ofCoords 0 0 (6 * jetH)) 0 := by
  have hp := hasDerivAt_p_lineJet5
  have hn3 := hasDerivAt_n3_lineJet5
  have hp2 := hasDerivAt_p2_lineJet5
  have hn1 := hasDerivAt_n1_lineJet5
  have h1 := hp.smul hn3
  have hmid := hp2.smul hn1
  have h3 := HasDerivAt.const_smul (3 : ℝ) hmid
  have hadd := h1.add h3
  have heq : (fun t => u3Of (lineJet 5 t)) =ᶠ[𝓝 (0 : ℝ)]
      fun t => pOf (lineJet 5 t) • n3Of (lineJet 5 t)
        + (3 : ℝ) • (p2Of (lineJet 5 t) • n1Of (lineJet 5 t)) :=
    Eventually.of_forall u3Of_lineJet5
  have h' := hadd.congr_of_eventuallyEq heq
  have hv :
      pOf (lineJet 5 0) • ofCoords 0 0 (-8 / 125)
          + (0 : ℝ) • n3Of (lineJet 5 0)
          + (3 : ℝ) •
            (p2Of (lineJet 5 0) • ofCoords 0 0 1
              + (0 : ℝ) • n1Of (lineJet 5 0))
        = ofCoords 0 0 (6 * jetH) := by
    rw [lineJet_zero, n3Of_sStar, n1Of_sStar, pOf_sStar, p2Of_sStar]
    apply (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).injective
    ext i
    fin_cases i
    · simp [ofCoords, PiLp.smul_apply, PiLp.add_apply, smul_eq_mul]
    · simp [ofCoords, PiLp.smul_apply, PiLp.add_apply, smul_eq_mul]
    · simp [ofCoords, PiLp.smul_apply, PiLp.add_apply, smul_eq_mul]
      simpa [mul_assoc, add_assoc, add_left_comm, add_comm, mul_comm, mul_left_comm]
        using six_jetH_eval
  exact h'.congr_deriv hv

lemma hasDerivAt_losTaylor23_lineJet5 (i : Fin 6) :
    HasDerivAt (fun t => losTaylor23 (lineJet 5 t) i) (jetMatrix i 5) 0 := by
  have hu2 := hasDerivAt_u2_lineJet5
  have hu3 := hasDerivAt_u3_lineJet5
  fin_cases i
  · have h := (hasDerivAt_ofLp hu2 0).div_const (2 : ℝ)
    refine h.congr_deriv ?_
    simp [jetMatrix, ofLp_ofCoords]
  · have h := (hasDerivAt_ofLp hu2 1).div_const (2 : ℝ)
    refine h.congr_deriv ?_
    simp [jetMatrix, ofLp_ofCoords]
  · have h := (hasDerivAt_ofLp hu2 2).div_const (2 : ℝ)
    refine h.congr_deriv ?_
    simp [jetMatrix, ofLp_ofCoords]
  · have h := (hasDerivAt_ofLp hu3 0).div_const (6 : ℝ)
    refine h.congr_deriv ?_
    simp [jetMatrix, ofLp_ofCoords]
  · have h := (hasDerivAt_ofLp hu3 1).div_const (6 : ℝ)
    refine h.congr_deriv ?_
    simp [jetMatrix, ofLp_ofCoords]
  · have h := (hasDerivAt_ofLp hu3 2).div_const (6 : ℝ)
    refine h.congr_deriv ?_
    simp [jetMatrix, ofLp_ofCoords]

lemma deriv_losTaylor23_lineJet5 (i : Fin 6) :
    deriv (fun t => losTaylor23 (lineJet 5 t) i) 0 = jetMatrix i 5 :=
  (hasDerivAt_losTaylor23_lineJet5 i).deriv

/-! Axis 4: vy-perturbation. Position is fixed; `q1 = q3 = 0`. -/

lemma statePos_lineJet4 (t : ℝ) :
    statePos (lineJet 4 t) = ofCoords (5 / 2) 0 0 := by
  simp [statePos, ofCoords, lineJet_apply, sStar]

lemma stateVel_lineJet4 (t : ℝ) :
    stateVel (lineJet 4 t) = ofCoords 0 (Real.sqrt 10 / 5 + t) 0 := by
  simp [stateVel, ofCoords, lineJet_apply, sStar]

lemma rnorm_lineJet4 (t : ℝ) : rnorm (lineJet 4 t) = 5 / 2 := by
  rw [rnorm, statePos_lineJet4, ofCoords_norm]
  simp [sqrt_25_4]

lemma vecDot_lineJet4 (t : ℝ) :
    vecDot (statePos (lineJet 4 t)) (stateVel (lineJet 4 t)) = 0 := by
  simp [vecDot, statePos_lineJet4, stateVel_lineJet4, ofLp_ofCoords, Fin.sum_univ_three]

lemma n0Of_lineJet4 (t : ℝ) :
    n0Of (lineJet 4 t) = ofCoords (3 / 2) 0 0 := by
  apply (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).injective
  ext i
  fin_cases i <;> simp [n0Of, statePos_lineJet4, eJet0, ofCoords, PiLp.sub_apply] <;> ring

lemma n1Of_lineJet4 (t : ℝ) :
    n1Of (lineJet 4 t) = ofCoords 0 (Real.sqrt 10 / 5 - 1 + t) 0 := by
  apply (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).injective
  ext i
  fin_cases i <;> simp [n1Of, stateVel_lineJet4, eJet1, ofCoords, PiLp.sub_apply] <;> ring

lemma accelOf_lineJet4 (t : ℝ) :
    accelOf (lineJet 4 t) = ofCoords (-4 / 25) 0 0 := by
  unfold accelOf
  rw [statePos_lineJet4]
  have hr : ‖ofCoords (5 / 2 : ℝ) 0 0‖ = 5 / 2 := by
    rw [ofCoords_norm]; simp [sqrt_25_4]
  rw [hr]
  apply (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).injective
  ext i
  fin_cases i <;> simp [ofCoords, PiLp.smul_apply, smul_eq_mul] <;> norm_num

lemma n2Of_lineJet4 (t : ℝ) :
    n2Of (lineJet 4 t) = ofCoords (21 / 25) 0 0 := by
  apply (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).injective
  ext i
  fin_cases i <;> simp [n2Of, accelOf_lineJet4, eJet2, ofCoords, PiLp.sub_apply] <;> norm_num

lemma inv_five_halves_pow3 : ((5 / 2 : ℝ) ^ 3)⁻¹ = 8 / 125 := by norm_num

lemma jerkOf_lineJet4 (t : ℝ) :
    jerkOf (lineJet 4 t) =
      ofCoords 0 (-(8 / 125) * (Real.sqrt 10 / 5 + t)) 0 := by
  unfold jerkOf
  rw [show ‖statePos (lineJet 4 t)‖ = (5 / 2 : ℝ) from rnorm_lineJet4 t,
    vecDot_lineJet4, stateVel_lineJet4, statePos_lineJet4]
  apply (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).injective
  ext i
  fin_cases i
  · simp [ofCoords, PiLp.smul_apply, smul_eq_mul]
  · simp [ofCoords, PiLp.smul_apply, smul_eq_mul, inv_five_halves_pow3]
  · simp [ofCoords, PiLp.smul_apply, smul_eq_mul]

lemma n3Of_lineJet4 (t : ℝ) :
    n3Of (lineJet 4 t) =
      ofCoords 0 (1 - (8 / 125) * (Real.sqrt 10 / 5 + t)) 0 := by
  apply (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).injective
  ext i
  fin_cases i <;> simp [n3Of, jerkOf_lineJet4, eJet3, ofCoords, PiLp.sub_apply] <;> ring

lemma qOf_lineJet4 (t : ℝ) : qOf (lineJet 4 t) = 9 / 4 := by
  simp [qOf, vecDot, n0Of_lineJet4, ofLp_ofCoords, Fin.sum_univ_three]
  norm_num

lemma q1Of_lineJet4 (t : ℝ) : q1Of (lineJet 4 t) = 0 := by
  simp [q1Of, vecDot, n0Of_lineJet4, n1Of_lineJet4, ofLp_ofCoords, Fin.sum_univ_three]

lemma q2Of_lineJet4 (t : ℝ) :
    q2Of (lineJet 4 t) =
      2 * (Real.sqrt 10 / 5 - 1 + t) ^ 2 + 63 / 25 := by
  simp [q2Of, vecDot, n1Of_lineJet4, n0Of_lineJet4, n2Of_lineJet4, ofLp_ofCoords,
    Fin.sum_univ_three]
  ring

lemma q3Of_lineJet4 (t : ℝ) : q3Of (lineJet 4 t) = 0 := by
  simp [q3Of, vecDot, n1Of_lineJet4, n2Of_lineJet4, n0Of_lineJet4, n3Of_lineJet4,
    ofLp_ofCoords, Fin.sum_univ_three]

lemma pOf_lineJet4 (t : ℝ) : pOf (lineJet 4 t) = 2 / 3 := by
  unfold pOf
  rw [qOf_lineJet4, rpow_neg_half_nine_four]

lemma p1Of_lineJet4 (t : ℝ) : p1Of (lineJet 4 t) = 0 := by
  simp [p1Of, q1Of_lineJet4]

lemma p2Of_lineJet4 (t : ℝ) :
    p2Of (lineJet 4 t) =
      -(1 / 2 : ℝ) * ((9 / 4 : ℝ) ^ (-(3 / 2 : ℝ)) * q2Of (lineJet 4 t)) := by
  unfold p2Of
  rw [qOf_lineJet4, q1Of_lineJet4]
  simp only [zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero, zero_sub]
  ring

lemma p3Of_lineJet4 (t : ℝ) : p3Of (lineJet 4 t) = 0 := by
  simp [p3Of, q1Of_lineJet4, q3Of_lineJet4]

lemma hasDerivAt_n0_lineJet4 :
    HasDerivAt (fun t => n0Of (lineJet 4 t)) (0 : Vec) 0 := by
  have h := hasDerivAt_coord3 (hasDerivAt_const 0 (3 / 2 : ℝ))
    (hasDerivAt_const 0 (0 : ℝ)) (hasDerivAt_const 0 (0 : ℝ))
  have h' : HasDerivAt (fun t => n0Of (lineJet 4 t)) (ofCoords 0 0 0) 0 :=
    h.congr_of_eventuallyEq (Eventually.of_forall n0Of_lineJet4)
  exact h'.congr_deriv ofCoords_zero

lemma hasDerivAt_n1_lineJet4 :
    HasDerivAt (fun t => n1Of (lineJet 4 t)) (ofCoords 0 1 0) 0 := by
  have hy := hasDerivAt_id_const_add (Real.sqrt 10 / 5 - 1) 0
  have h := hasDerivAt_coord3 (hasDerivAt_const 0 (0 : ℝ)) hy
    (hasDerivAt_const 0 (0 : ℝ))
  exact h.congr_of_eventuallyEq (Eventually.of_forall n1Of_lineJet4)

lemma hasDerivAt_n2_lineJet4 :
    HasDerivAt (fun t => n2Of (lineJet 4 t)) (0 : Vec) 0 :=
  (hasDerivAt_const (0 : ℝ) (ofCoords (21 / 25) 0 0)).congr_of_eventuallyEq
    (Eventually.of_forall n2Of_lineJet4) |>.congr_deriv (by
      apply (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).injective
      ext i; fin_cases i <;> simp)

lemma hasDerivAt_n3_lineJet4 :
    HasDerivAt (fun t => n3Of (lineJet 4 t)) (ofCoords 0 (-8 / 125) 0) 0 := by
  have hy : HasDerivAt
      (fun t : ℝ => 1 - (8 / 125) * (Real.sqrt 10 / 5 + t)) (-8 / 125) 0 := by
    have hadd := hasDerivAt_id_const_add (Real.sqrt 10 / 5) 0
    have hm := hadd.const_mul (8 / 125 : ℝ)
    have h := (hasDerivAt_const 0 (1 : ℝ)).sub hm
    exact h.congr_deriv (by norm_num)
  have h := hasDerivAt_coord3 (hasDerivAt_const 0 (0 : ℝ)) hy
    (hasDerivAt_const 0 (0 : ℝ))
  exact h.congr_of_eventuallyEq (Eventually.of_forall n3Of_lineJet4)

lemma hasDerivAt_q_lineJet4 :
    HasDerivAt (fun t => qOf (lineJet 4 t)) 0 0 :=
  (hasDerivAt_const (0 : ℝ) (9 / 4 : ℝ)).congr_of_eventuallyEq
    (Eventually.of_forall qOf_lineJet4)

lemma hasDerivAt_q1_lineJet4 :
    HasDerivAt (fun t => q1Of (lineJet 4 t)) 0 0 :=
  (hasDerivAt_const (0 : ℝ) (0 : ℝ)).congr_of_eventuallyEq
    (Eventually.of_forall q1Of_lineJet4)

lemma hasDerivAt_q2_lineJet4 :
    HasDerivAt (fun t => q2Of (lineJet 4 t))
      (4 * (Real.sqrt 10 / 5 - 1)) 0 := by
  have hc : HasDerivAt (fun t : ℝ => Real.sqrt 10 / 5 - 1 + t) 1 0 :=
    hasDerivAt_id_const_add (Real.sqrt 10 / 5 - 1) 0
  have hsq : HasDerivAt (fun t : ℝ => (Real.sqrt 10 / 5 - 1 + t) ^ 2)
      (2 * (Real.sqrt 10 / 5 - 1)) 0 := by
    have h := (hasDerivAt_pow2_at (Real.sqrt 10 / 5 - 1 + (0 : ℝ))).comp 0 hc
    exact h.congr_deriv (by simp)
  have h2 := HasDerivAt.const_mul (2 : ℝ) hsq
  have h := (hasDerivAt_const 0 (63 / 25 : ℝ)).add h2
  have h' : HasDerivAt
      ((fun _ : ℝ => (63 / 25 : ℝ)) + fun t => 2 * (Real.sqrt 10 / 5 - 1 + t) ^ 2)
      (4 * (Real.sqrt 10 / 5 - 1)) 0 :=
    h.congr_deriv (by ring)
  exact h'.congr_of_eventuallyEq (Eventually.of_forall fun t => by
    simpa [add_comm] using q2Of_lineJet4 t)

lemma hasDerivAt_q3_lineJet4 :
    HasDerivAt (fun t => q3Of (lineJet 4 t)) 0 0 :=
  (hasDerivAt_const (0 : ℝ) (0 : ℝ)).congr_of_eventuallyEq
    (Eventually.of_forall q3Of_lineJet4)

lemma hasDerivAt_p_lineJet4 :
    HasDerivAt (fun t => pOf (lineJet 4 t)) 0 0 :=
  (hasDerivAt_const (0 : ℝ) (2 / 3 : ℝ)).congr_of_eventuallyEq
    (Eventually.of_forall pOf_lineJet4)

lemma hasDerivAt_p1_lineJet4 :
    HasDerivAt (fun t => p1Of (lineJet 4 t)) 0 0 :=
  (hasDerivAt_const (0 : ℝ) (0 : ℝ)).congr_of_eventuallyEq
    (Eventually.of_forall p1Of_lineJet4)

lemma hasDerivAt_p2_lineJet4 :
    HasDerivAt (fun t => p2Of (lineJet 4 t))
      (16 / 27 - 16 * Real.sqrt 10 / 135) 0 := by
  have hq2 := hasDerivAt_q2_lineJet4
  have hA := hasDerivAt_const (0 : ℝ) ((9 / 4 : ℝ) ^ (-(3 / 2 : ℝ)))
  have hmul := hA.mul hq2
  have h := HasDerivAt.const_mul (-(1 / 2 : ℝ)) hmul
  have hd :
      (-(1 / 2 : ℝ)) *
          (0 * q2Of (lineJet 4 0)
            + (9 / 4 : ℝ) ^ (-(3 / 2 : ℝ)) * (4 * (Real.sqrt 10 / 5 - 1)))
        = 16 / 27 - 16 * Real.sqrt 10 / 135 := by
    rw [rpow_neg_three_halves_nine_four]
    field_simp
    ring
  have h' := h.congr_deriv hd
  exact h'.congr_of_eventuallyEq (Eventually.of_forall p2Of_lineJet4)

lemma hasDerivAt_p3_lineJet4 :
    HasDerivAt (fun t => p3Of (lineJet 4 t)) 0 0 :=
  (hasDerivAt_const (0 : ℝ) (0 : ℝ)).congr_of_eventuallyEq
    (Eventually.of_forall p3Of_lineJet4)

lemma u2Of_lineJet4 (t : ℝ) :
    u2Of (lineJet 4 t) =
      pOf (lineJet 4 t) • n2Of (lineJet 4 t)
        + p2Of (lineJet 4 t) • n0Of (lineJet 4 t) := by
  unfold u2Of
  rw [p1Of_lineJet4]
  simp

lemma two_jetB_eval :
    (16 / 27 - 16 * Real.sqrt 10 / 135) * (3 / 2) = 2 * jetB := by
  unfold jetB
  field_simp
  ring

lemma hasDerivAt_u2_lineJet4 :
    HasDerivAt (fun t => u2Of (lineJet 4 t)) (ofCoords (2 * jetB) 0 0) 0 := by
  have hp := hasDerivAt_p_lineJet4
  have hn2 := hasDerivAt_n2_lineJet4
  have hp2 := hasDerivAt_p2_lineJet4
  have hn0 := hasDerivAt_n0_lineJet4
  have h1 := hp.smul hn2
  have h2 := hp2.smul hn0
  have hadd := h1.add h2
  have heq : (fun t => u2Of (lineJet 4 t)) =ᶠ[𝓝 (0 : ℝ)]
      fun t => pOf (lineJet 4 t) • n2Of (lineJet 4 t)
        + p2Of (lineJet 4 t) • n0Of (lineJet 4 t) :=
    Eventually.of_forall u2Of_lineJet4
  have h' := hadd.congr_of_eventuallyEq heq
  have hv :
      pOf (lineJet 4 0) • (0 : Vec)
          + (0 : ℝ) • n2Of (lineJet 4 0)
          + (p2Of (lineJet 4 0) • (0 : Vec)
            + (16 / 27 - 16 * Real.sqrt 10 / 135) • n0Of (lineJet 4 0))
        = ofCoords (2 * jetB) 0 0 := by
    rw [lineJet_zero, n0Of_sStar, pOf_sStar, p2Of_sStar]
    apply (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).injective
    ext i
    fin_cases i
    · simp [ofCoords, PiLp.smul_apply, PiLp.add_apply, smul_eq_mul]
      simpa [mul_assoc, mul_comm, mul_left_comm] using two_jetB_eval
    · simp [ofCoords, PiLp.smul_apply, PiLp.add_apply, smul_eq_mul]
    · simp [ofCoords, PiLp.smul_apply, PiLp.add_apply, smul_eq_mul]
  exact h'.congr_deriv hv

lemma u3Of_lineJet4 (t : ℝ) :
    u3Of (lineJet 4 t) =
      pOf (lineJet 4 t) • n3Of (lineJet 4 t)
        + (3 : ℝ) • (p2Of (lineJet 4 t) • n1Of (lineJet 4 t)) := by
  unfold u3Of
  rw [p1Of_lineJet4, p3Of_lineJet4]
  simp

lemma six_jetG_eval :
    (2 / 3 : ℝ) * (-8 / 125)
      + (3 * (-532 / 675 + 16 * Real.sqrt 10 / 135)
        + 3 * ((16 / 27 - 16 * Real.sqrt 10 / 135) * (Real.sqrt 10 / 5 - 1)))
      = 6 * jetG := by
  unfold jetG
  field_simp
  ring_nf
  simp [sqrt10_sq]
  ring

lemma hasDerivAt_u3_lineJet4 :
    HasDerivAt (fun t => u3Of (lineJet 4 t)) (ofCoords 0 (6 * jetG) 0) 0 := by
  have hp := hasDerivAt_p_lineJet4
  have hn3 := hasDerivAt_n3_lineJet4
  have hp2 := hasDerivAt_p2_lineJet4
  have hn1 := hasDerivAt_n1_lineJet4
  have h1 := hp.smul hn3
  have hmid := hp2.smul hn1
  have h3 := HasDerivAt.const_smul (3 : ℝ) hmid
  have hadd := h1.add h3
  have heq : (fun t => u3Of (lineJet 4 t)) =ᶠ[𝓝 (0 : ℝ)]
      fun t => pOf (lineJet 4 t) • n3Of (lineJet 4 t)
        + (3 : ℝ) • (p2Of (lineJet 4 t) • n1Of (lineJet 4 t)) :=
    Eventually.of_forall u3Of_lineJet4
  have h' := hadd.congr_of_eventuallyEq heq
  have hv :
      pOf (lineJet 4 0) • ofCoords 0 (-8 / 125) 0
          + (0 : ℝ) • n3Of (lineJet 4 0)
          + (3 : ℝ) •
            (p2Of (lineJet 4 0) • ofCoords 0 1 0
              + (16 / 27 - 16 * Real.sqrt 10 / 135) • n1Of (lineJet 4 0))
        = ofCoords 0 (6 * jetG) 0 := by
    rw [lineJet_zero, n1Of_sStar, n3Of_sStar, pOf_sStar, p2Of_sStar]
    apply (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).injective
    ext i
    fin_cases i
    · simp [ofCoords, PiLp.smul_apply, PiLp.add_apply, smul_eq_mul]
    · simp [ofCoords, PiLp.smul_apply, PiLp.add_apply, smul_eq_mul]
      simpa [mul_assoc, add_assoc, add_left_comm, add_comm, mul_comm, mul_left_comm]
        using six_jetG_eval
    · simp [ofCoords, PiLp.smul_apply, PiLp.add_apply, smul_eq_mul]
  exact h'.congr_deriv hv

lemma hasDerivAt_losTaylor23_lineJet4 (i : Fin 6) :
    HasDerivAt (fun t => losTaylor23 (lineJet 4 t) i) (jetMatrix i 4) 0 := by
  have hu2 := hasDerivAt_u2_lineJet4
  have hu3 := hasDerivAt_u3_lineJet4
  fin_cases i
  · have h := (hasDerivAt_ofLp hu2 0).div_const (2 : ℝ)
    refine h.congr_deriv ?_
    simp [jetMatrix, ofLp_ofCoords]
  · have h := (hasDerivAt_ofLp hu2 1).div_const (2 : ℝ)
    refine h.congr_deriv ?_
    simp [jetMatrix, ofLp_ofCoords]
  · have h := (hasDerivAt_ofLp hu2 2).div_const (2 : ℝ)
    refine h.congr_deriv ?_
    simp [jetMatrix, ofLp_ofCoords]
  · have h := (hasDerivAt_ofLp hu3 0).div_const (6 : ℝ)
    refine h.congr_deriv ?_
    simp [jetMatrix, ofLp_ofCoords]
  · have h := (hasDerivAt_ofLp hu3 1).div_const (6 : ℝ)
    refine h.congr_deriv ?_
    simp [jetMatrix, ofLp_ofCoords]
  · have h := (hasDerivAt_ofLp hu3 2).div_const (6 : ℝ)
    refine h.congr_deriv ?_
    simp [jetMatrix, ofLp_ofCoords]

lemma deriv_losTaylor23_lineJet4 (i : Fin 6) :
    deriv (fun t => losTaylor23 (lineJet 4 t) i) 0 = jetMatrix i 4 :=
  (hasDerivAt_losTaylor23_lineJet4 i).deriv

/-! Axis 3: vx-perturbation. Position fixed; `q1 = 3t` is the new term. -/

lemma statePos_lineJet3 (t : ℝ) :
    statePos (lineJet 3 t) = ofCoords (5 / 2) 0 0 := by
  simp [statePos, ofCoords, lineJet_apply, sStar]

lemma stateVel_lineJet3 (t : ℝ) :
    stateVel (lineJet 3 t) = ofCoords t (Real.sqrt 10 / 5) 0 := by
  simp [stateVel, ofCoords, lineJet_apply, sStar]

lemma rnorm_lineJet3 (t : ℝ) : rnorm (lineJet 3 t) = 5 / 2 := by
  rw [rnorm, statePos_lineJet3, ofCoords_norm]
  simp [sqrt_25_4]

lemma vecDot_lineJet3 (t : ℝ) :
    vecDot (statePos (lineJet 3 t)) (stateVel (lineJet 3 t)) = (5 / 2) * t := by
  simp [vecDot, statePos_lineJet3, stateVel_lineJet3, ofLp_ofCoords, Fin.sum_univ_three]

lemma n0Of_lineJet3 (t : ℝ) :
    n0Of (lineJet 3 t) = ofCoords (3 / 2) 0 0 := by
  apply (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).injective
  ext i
  fin_cases i <;> simp [n0Of, statePos_lineJet3, eJet0, ofCoords, PiLp.sub_apply] <;> ring

lemma n1Of_lineJet3 (t : ℝ) :
    n1Of (lineJet 3 t) = ofCoords t (Real.sqrt 10 / 5 - 1) 0 := by
  apply (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).injective
  ext i
  fin_cases i <;> simp [n1Of, stateVel_lineJet3, eJet1, ofCoords, PiLp.sub_apply]

lemma accelOf_lineJet3 (t : ℝ) :
    accelOf (lineJet 3 t) = ofCoords (-4 / 25) 0 0 := by
  unfold accelOf
  rw [statePos_lineJet3]
  have hr : ‖ofCoords (5 / 2 : ℝ) 0 0‖ = 5 / 2 := by
    rw [ofCoords_norm]; simp [sqrt_25_4]
  rw [hr]
  apply (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).injective
  ext i
  fin_cases i <;> simp [ofCoords, PiLp.smul_apply, smul_eq_mul] <;> norm_num

lemma n2Of_lineJet3 (t : ℝ) :
    n2Of (lineJet 3 t) = ofCoords (21 / 25) 0 0 := by
  apply (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).injective
  ext i
  fin_cases i <;> simp [n2Of, accelOf_lineJet3, eJet2, ofCoords, PiLp.sub_apply] <;> norm_num

lemma inv_five_halves_pow5 : ((5 / 2 : ℝ) ^ 5)⁻¹ = 32 / 3125 := by norm_num

lemma jerkOf_lineJet3 (t : ℝ) :
    jerkOf (lineJet 3 t) = ofCoords (16 * t / 125) (-8 * Real.sqrt 10 / 625) 0 := by
  unfold jerkOf
  rw [show ‖statePos (lineJet 3 t)‖ = (5 / 2 : ℝ) from rnorm_lineJet3 t,
    vecDot_lineJet3, stateVel_lineJet3, statePos_lineJet3]
  apply (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).injective
  ext i
  fin_cases i
  · simp [ofCoords, PiLp.smul_apply, PiLp.add_apply, smul_eq_mul,
      inv_five_halves_pow3, inv_five_halves_pow5]
    ring
  · simp [ofCoords, PiLp.smul_apply, PiLp.add_apply, smul_eq_mul,
      inv_five_halves_pow3, inv_five_halves_pow5]
    ring
  · simp [ofCoords, PiLp.smul_apply, PiLp.add_apply, smul_eq_mul]

lemma n3Of_lineJet3 (t : ℝ) :
    n3Of (lineJet 3 t) =
      ofCoords (16 * t / 125) (1 - 8 * Real.sqrt 10 / 625) 0 := by
  apply (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).injective
  ext i
  fin_cases i <;> simp [n3Of, jerkOf_lineJet3, eJet3, ofCoords, PiLp.sub_apply] <;> ring

lemma qOf_lineJet3 (t : ℝ) : qOf (lineJet 3 t) = 9 / 4 := by
  simp [qOf, vecDot, n0Of_lineJet3, ofLp_ofCoords, Fin.sum_univ_three]
  norm_num

lemma q1Of_lineJet3 (t : ℝ) : q1Of (lineJet 3 t) = 3 * t := by
  simp [q1Of, vecDot, n0Of_lineJet3, n1Of_lineJet3, ofLp_ofCoords, Fin.sum_univ_three]
  ring

lemma q2Of_lineJet3 (t : ℝ) :
    q2Of (lineJet 3 t) = 2 * t ^ 2 + (133 / 25 - 4 * Real.sqrt 10 / 5) := by
  simp [q2Of, vecDot, n1Of_lineJet3, n0Of_lineJet3, n2Of_lineJet3, ofLp_ofCoords,
    Fin.sum_univ_three]
  field_simp
  ring_nf
  simp [sqrt10_sq]
  ring

lemma q3Of_lineJet3 (t : ℝ) : q3Of (lineJet 3 t) = 678 * t / 125 := by
  simp [q3Of, vecDot, n1Of_lineJet3, n2Of_lineJet3, n0Of_lineJet3, n3Of_lineJet3,
    ofLp_ofCoords, Fin.sum_univ_three]
  ring

lemma pOf_lineJet3 (t : ℝ) : pOf (lineJet 3 t) = 2 / 3 := by
  unfold pOf
  rw [qOf_lineJet3, rpow_neg_half_nine_four]

lemma p1Of_lineJet3 (t : ℝ) :
    p1Of (lineJet 3 t) = (-(4 / 9 : ℝ)) * t := by
  unfold p1Of
  rw [qOf_lineJet3, q1Of_lineJet3, rpow_neg_three_halves_nine_four]
  ring

lemma hasDerivAt_n0_lineJet3 :
    HasDerivAt (fun t => n0Of (lineJet 3 t)) (0 : Vec) 0 := by
  have h := hasDerivAt_coord3 (hasDerivAt_const 0 (3 / 2 : ℝ))
    (hasDerivAt_const 0 (0 : ℝ)) (hasDerivAt_const 0 (0 : ℝ))
  have h' : HasDerivAt (fun t => n0Of (lineJet 3 t)) (ofCoords 0 0 0) 0 :=
    h.congr_of_eventuallyEq (Eventually.of_forall n0Of_lineJet3)
  exact h'.congr_deriv ofCoords_zero

lemma hasDerivAt_n1_lineJet3 :
    HasDerivAt (fun t => n1Of (lineJet 3 t)) (ofCoords 1 0 0) 0 := by
  have h := hasDerivAt_coord3 (hasDerivAt_id 0)
    (hasDerivAt_const 0 (Real.sqrt 10 / 5 - 1)) (hasDerivAt_const 0 (0 : ℝ))
  exact h.congr_of_eventuallyEq (Eventually.of_forall n1Of_lineJet3)

lemma hasDerivAt_n2_lineJet3 :
    HasDerivAt (fun t => n2Of (lineJet 3 t)) (0 : Vec) 0 :=
  (hasDerivAt_const (0 : ℝ) (ofCoords (21 / 25) 0 0)).congr_of_eventuallyEq
    (Eventually.of_forall n2Of_lineJet3) |>.congr_deriv (by
      apply (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).injective
      ext i; fin_cases i <;> simp)

lemma hasDerivAt_n3_lineJet3 :
    HasDerivAt (fun t => n3Of (lineJet 3 t)) (ofCoords (16 / 125) 0 0) 0 := by
  have hx0 : HasDerivAt (fun t : ℝ => (16 / 125 : ℝ) * t) (16 / 125) 0 :=
    ((hasDerivAt_id (0 : ℝ)).const_mul (16 / 125 : ℝ)).congr_deriv (by simp)
  have hx : HasDerivAt (fun t : ℝ => 16 * t / 125) (16 / 125) 0 :=
    hx0.congr_of_eventuallyEq (Eventually.of_forall fun t => by field_simp)
  have h := hasDerivAt_coord3 hx
    (hasDerivAt_const 0 (1 - 8 * Real.sqrt 10 / 625)) (hasDerivAt_const 0 (0 : ℝ))
  exact h.congr_of_eventuallyEq (Eventually.of_forall n3Of_lineJet3)

lemma hasDerivAt_q_lineJet3 :
    HasDerivAt (fun t => qOf (lineJet 3 t)) 0 0 :=
  (hasDerivAt_const (0 : ℝ) (9 / 4 : ℝ)).congr_of_eventuallyEq
    (Eventually.of_forall qOf_lineJet3)

lemma hasDerivAt_q1_lineJet3 :
    HasDerivAt (fun t => q1Of (lineJet 3 t)) 3 0 := by
  have h := (hasDerivAt_id (0 : ℝ)).const_mul (3 : ℝ)
  exact (h.congr_deriv (by simp)).congr_of_eventuallyEq
    (Eventually.of_forall q1Of_lineJet3)

lemma hasDerivAt_q2_lineJet3 :
    HasDerivAt (fun t => q2Of (lineJet 3 t)) 0 0 := by
  have h2 : HasDerivAt (fun t : ℝ => 2 * t ^ 2) 0 0 :=
    (HasDerivAt.const_mul (2 : ℝ) hasDerivAt_pow2_id).congr_deriv (by simp)
  have h : HasDerivAt
      ((fun _ : ℝ => 133 / 25 - 4 * Real.sqrt 10 / 5) + fun t => 2 * t ^ 2) 0 0 :=
    (hasDerivAt_const 0 (133 / 25 - 4 * Real.sqrt 10 / 5)).add h2 |>.congr_deriv (by ring)
  exact h.congr_of_eventuallyEq (Eventually.of_forall fun t => by
    simpa [add_comm] using q2Of_lineJet3 t)

lemma hasDerivAt_q3_lineJet3 :
    HasDerivAt (fun t => q3Of (lineJet 3 t)) (678 / 125) 0 := by
  have h0 : HasDerivAt (fun t : ℝ => (678 / 125 : ℝ) * t) (678 / 125) 0 :=
    ((hasDerivAt_id (0 : ℝ)).const_mul (678 / 125 : ℝ)).congr_deriv (by simp)
  have h : HasDerivAt (fun t : ℝ => 678 * t / 125) (678 / 125) 0 :=
    h0.congr_of_eventuallyEq (Eventually.of_forall fun t => by field_simp)
  exact h.congr_of_eventuallyEq (Eventually.of_forall q3Of_lineJet3)

lemma hasDerivAt_p_lineJet3 :
    HasDerivAt (fun t => pOf (lineJet 3 t)) 0 0 :=
  (hasDerivAt_const (0 : ℝ) (2 / 3 : ℝ)).congr_of_eventuallyEq
    (Eventually.of_forall pOf_lineJet3)

lemma hasDerivAt_p1_lineJet3 :
    HasDerivAt (fun t => p1Of (lineJet 3 t)) (-4 / 9) 0 := by
  have h := (hasDerivAt_id (0 : ℝ)).const_mul (-(4 / 9 : ℝ))
  exact (h.congr_deriv (by norm_num)).congr_of_eventuallyEq
    (Eventually.of_forall p1Of_lineJet3)

lemma hasDerivAt_p2_lineJet3 :
    HasDerivAt (fun t => p2Of (lineJet 3 t)) 0 0 := by
  have hq1 := hasDerivAt_q1_lineJet3
  have hq2 := hasDerivAt_q2_lineJet3
  have hA := hasDerivAt_const (0 : ℝ) ((9 / 4 : ℝ) ^ (-(5 / 2 : ℝ)))
  have hB := hasDerivAt_const (0 : ℝ) ((9 / 4 : ℝ) ^ (-(3 / 2 : ℝ)))
  have hq1sq := hq1.pow 2
  have ht1 := (HasDerivAt.const_mul (3 / 4 : ℝ) (hA.mul hq1sq))
  have ht2 := (HasDerivAt.const_mul (1 / 2 : ℝ) (hB.mul hq2))
  have h := ht1.sub ht2
  have hd :
      (3 / 4 : ℝ) *
            (0 * ((fun t => q1Of (lineJet 3 t)) ^ 2) 0
              + (9 / 4 : ℝ) ^ (-(5 / 2 : ℝ)) *
                ((2 : ℕ) * q1Of (lineJet 3 0) ^ (2 - 1) * 3))
          - (1 / 2 : ℝ) *
            (0 * q2Of (lineJet 3 0)
              + (9 / 4 : ℝ) ^ (-(3 / 2 : ℝ)) * 0)
        = 0 := by
    simp [q1Of_lineJet3, Pi.pow_apply]
  have h' := h.congr_deriv hd
  have heq : (fun t => p2Of (lineJet 3 t)) =ᶠ[𝓝 (0 : ℝ)]
      fun t =>
        (3 / 4 : ℝ) * ((9 / 4 : ℝ) ^ (-(5 / 2 : ℝ)) * q1Of (lineJet 3 t) ^ 2)
          - (1 / 2 : ℝ) * ((9 / 4 : ℝ) ^ (-(3 / 2 : ℝ)) * q2Of (lineJet 3 t)) :=
    Eventually.of_forall fun t => by
      simp [p2Of, qOf_lineJet3, mul_assoc]
  exact h'.congr_of_eventuallyEq heq

lemma p3'_lineJet3_eval :
    (9 / 4 : ℝ) * ((9 / 4 : ℝ) ^ (-(5 / 2 : ℝ)) * 3 *
        (133 / 25 - 4 * Real.sqrt 10 / 5))
      - (2⁻¹) * ((9 / 4 : ℝ) ^ (-(3 / 2 : ℝ)) * (678 / 125))
      = 1472 / 375 - 32 * Real.sqrt 10 / 45 := by
  rw [rpow_neg_five_halves_nine_four, rpow_neg_three_halves_nine_four]
  field_simp
  ring

lemma hasDerivAt_p3_lineJet3 :
    HasDerivAt (fun t => p3Of (lineJet 3 t))
      (1472 / 375 - 32 * Real.sqrt 10 / 45) 0 := by
  have hq1 := hasDerivAt_q1_lineJet3
  have hq2 := hasDerivAt_q2_lineJet3
  have hq3 := hasDerivAt_q3_lineJet3
  have hA := hasDerivAt_const (0 : ℝ) ((9 / 4 : ℝ) ^ (-(7 / 2 : ℝ)))
  have hB := hasDerivAt_const (0 : ℝ) ((9 / 4 : ℝ) ^ (-(5 / 2 : ℝ)))
  have hC := hasDerivAt_const (0 : ℝ) ((9 / 4 : ℝ) ^ (-(3 / 2 : ℝ)))
  have hq1c := hq1.pow 3
  have ht1 := HasDerivAt.const_mul (-(15 / 8 : ℝ)) (hA.mul hq1c)
  have hmid := (hB.mul hq1).mul hq2
  have ht2 := HasDerivAt.const_mul (9 / 4 : ℝ) hmid
  have ht3 := HasDerivAt.const_mul (1 / 2 : ℝ) (hC.mul hq3)
  have h := (ht1.add ht2).sub ht3
  have hd :
      (-(15 / 8 : ℝ)) *
            (0 * q1Of (lineJet 3 0) ^ 3
              + (9 / 4 : ℝ) ^ (-(7 / 2 : ℝ)) *
                (3 * q1Of (lineJet 3 0) ^ 2 * 3))
          + (9 / 4 : ℝ) *
            ((0 * q1Of (lineJet 3 0) + (9 / 4 : ℝ) ^ (-(5 / 2 : ℝ)) * 3) *
                q2Of (lineJet 3 0)
              + ((9 / 4 : ℝ) ^ (-(5 / 2 : ℝ)) * q1Of (lineJet 3 0)) * 0)
          - (1 / 2 : ℝ) *
            (0 * q3Of (lineJet 3 0)
              + (9 / 4 : ℝ) ^ (-(3 / 2 : ℝ)) * (678 / 125))
        = 1472 / 375 - 32 * Real.sqrt 10 / 45 := by
    rw [q1Of_lineJet3, q2Of_lineJet3, q3Of_lineJet3]
    simp
    exact p3'_lineJet3_eval
  have h' := h.congr_deriv hd
  have heq : (fun t => p3Of (lineJet 3 t)) =ᶠ[𝓝 (0 : ℝ)]
      fun t =>
        (-(15 / 8 : ℝ)) * ((9 / 4 : ℝ) ^ (-(7 / 2 : ℝ)) * q1Of (lineJet 3 t) ^ 3)
          + (9 / 4 : ℝ) *
            ((9 / 4 : ℝ) ^ (-(5 / 2 : ℝ)) * q1Of (lineJet 3 t) * q2Of (lineJet 3 t))
          - (1 / 2 : ℝ) * ((9 / 4 : ℝ) ^ (-(3 / 2 : ℝ)) * q3Of (lineJet 3 t)) :=
    Eventually.of_forall fun t => by
      simp [p3Of, qOf_lineJet3, mul_assoc]
  exact h'.congr_of_eventuallyEq heq

lemma hasDerivAt_u2_lineJet3 :
    HasDerivAt (fun t => u2Of (lineJet 3 t)) (ofCoords 0 (2 * jetB) 0) 0 := by
  have hp := hasDerivAt_p_lineJet3
  have hn2 := hasDerivAt_n2_lineJet3
  have hp1 := hasDerivAt_p1_lineJet3
  have hn1 := hasDerivAt_n1_lineJet3
  have hp2 := hasDerivAt_p2_lineJet3
  have hn0 := hasDerivAt_n0_lineJet3
  have h1 := hp.smul hn2
  have hmid := hp1.smul hn1
  have h2 := HasDerivAt.const_smul (2 : ℝ) hmid
  have h3 := hp2.smul hn0
  have hadd := (h1.add h2).add h3
  have hv :
      pOf (lineJet 3 0) • (0 : Vec) + (0 : ℝ) • n2Of (lineJet 3 0)
          + (2 : ℝ) •
            (p1Of (lineJet 3 0) • ofCoords 1 0 0
              + (-4 / 9 : ℝ) • n1Of (lineJet 3 0))
          + (p2Of (lineJet 3 0) • (0 : Vec) + (0 : ℝ) • n0Of (lineJet 3 0))
        = ofCoords 0 (2 * jetB) 0 := by
    rw [lineJet_zero, pOf_sStar, p1Of_sStar, p2Of_sStar, n1Of_sStar, n2Of_sStar]
    apply (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).injective
    ext i
    fin_cases i
    · simp [ofCoords, PiLp.smul_apply, PiLp.add_apply, smul_eq_mul]
    · simp [ofCoords, PiLp.smul_apply, PiLp.add_apply, smul_eq_mul]
      unfold jetB
      field_simp
      ring
    · simp [ofCoords, PiLp.smul_apply, PiLp.add_apply, smul_eq_mul]
  exact hadd.congr_deriv hv

lemma six_jetA_axis3_eval :
    (2 / 3 : ℝ) * (16 / 125)
      + 3 * ((-4 / 9 : ℝ) * (21 / 25))
      + 3 * (-532 / 675 + 16 * Real.sqrt 10 / 135)
      + (1472 / 375 - 32 * Real.sqrt 10 / 45) * (3 / 2)
      = 6 * jetA := by
  unfold jetA
  field_simp
  ring

lemma hasDerivAt_u3_lineJet3 :
    HasDerivAt (fun t => u3Of (lineJet 3 t)) (ofCoords (6 * jetA) 0 0) 0 := by
  have hp := hasDerivAt_p_lineJet3
  have hn3 := hasDerivAt_n3_lineJet3
  have hp1 := hasDerivAt_p1_lineJet3
  have hn2 := hasDerivAt_n2_lineJet3
  have hp2 := hasDerivAt_p2_lineJet3
  have hn1 := hasDerivAt_n1_lineJet3
  have hp3 := hasDerivAt_p3_lineJet3
  have hn0 := hasDerivAt_n0_lineJet3
  have h1 := hp.smul hn3
  have ha := hp1.smul hn2
  have h2 := HasDerivAt.const_smul (3 : ℝ) ha
  have hb := hp2.smul hn1
  have h3 := HasDerivAt.const_smul (3 : ℝ) hb
  have h4 := hp3.smul hn0
  have hadd := ((h1.add h2).add h3).add h4
  have hv :
      pOf (lineJet 3 0) • ofCoords (16 / 125) 0 0 + (0 : ℝ) • n3Of (lineJet 3 0)
          + (3 : ℝ) •
            (p1Of (lineJet 3 0) • (0 : Vec) + (-4 / 9 : ℝ) • n2Of (lineJet 3 0))
          + (3 : ℝ) •
            (p2Of (lineJet 3 0) • ofCoords 1 0 0 + (0 : ℝ) • n1Of (lineJet 3 0))
          + (p3Of (lineJet 3 0) • (0 : Vec)
            + (1472 / 375 - 32 * Real.sqrt 10 / 45) • n0Of (lineJet 3 0))
        = ofCoords (6 * jetA) 0 0 := by
    rw [lineJet_zero, pOf_sStar, p1Of_sStar, p2Of_sStar, p3Of_sStar,
      n0Of_sStar, n1Of_sStar, n2Of_sStar, n3Of_sStar]
    apply (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).injective
    ext i
    fin_cases i
    · simp [ofCoords, PiLp.smul_apply, PiLp.add_apply, smul_eq_mul]
      simpa [mul_assoc, add_assoc, add_left_comm, add_comm, mul_comm, mul_left_comm]
        using six_jetA_axis3_eval
    · simp [ofCoords, PiLp.smul_apply, PiLp.add_apply, smul_eq_mul]
    · simp [ofCoords, PiLp.smul_apply, PiLp.add_apply, smul_eq_mul]
  exact hadd.congr_deriv hv

lemma hasDerivAt_losTaylor23_lineJet3 (i : Fin 6) :
    HasDerivAt (fun t => losTaylor23 (lineJet 3 t) i) (jetMatrix i 3) 0 := by
  have hu2 := hasDerivAt_u2_lineJet3
  have hu3 := hasDerivAt_u3_lineJet3
  fin_cases i
  · have h := (hasDerivAt_ofLp hu2 0).div_const (2 : ℝ)
    refine h.congr_deriv ?_
    simp [jetMatrix, ofLp_ofCoords]
  · have h := (hasDerivAt_ofLp hu2 1).div_const (2 : ℝ)
    refine h.congr_deriv ?_
    simp [jetMatrix, ofLp_ofCoords]
  · have h := (hasDerivAt_ofLp hu2 2).div_const (2 : ℝ)
    refine h.congr_deriv ?_
    simp [jetMatrix, ofLp_ofCoords]
  · have h := (hasDerivAt_ofLp hu3 0).div_const (6 : ℝ)
    refine h.congr_deriv ?_
    simp [jetMatrix, ofLp_ofCoords]
  · have h := (hasDerivAt_ofLp hu3 1).div_const (6 : ℝ)
    refine h.congr_deriv ?_
    simp [jetMatrix, ofLp_ofCoords]
  · have h := (hasDerivAt_ofLp hu3 2).div_const (6 : ℝ)
    refine h.congr_deriv ?_
    simp [jetMatrix, ofLp_ofCoords]

lemma deriv_losTaylor23_lineJet3 (i : Fin 6) :
    deriv (fun t => losTaylor23 (lineJet 3 t) i) 0 = jetMatrix i 3 :=
  (hasDerivAt_losTaylor23_lineJet3 i).deriv

/-! Axis 1: y-perturbation of position.  `q = 9/4+t²`, `q1 = 2t(√10/5-1)`,
`σ = t √10/5` (jerk extra term).  Clone of axis 3 (nonzero q1/p1) plus
the axis-2 `rnorm`/`vecDot` helpers. -/

lemma statePos_lineJet1 (t : ℝ) :
    statePos (lineJet 1 t) = ofCoords (5 / 2) t 0 := by
  simp [statePos, ofCoords, lineJet_apply, sStar]

lemma stateVel_lineJet1 (t : ℝ) :
    stateVel (lineJet 1 t) = ofCoords 0 (Real.sqrt 10 / 5) 0 := by
  simp [stateVel, ofCoords, lineJet_apply, sStar]

lemma rnorm_lineJet1 (t : ℝ) :
    rnorm (lineJet 1 t) = Real.sqrt ((5 / 2) ^ 2 + t ^ 2) := by
  rw [rnorm, statePos_lineJet1, ofCoords_norm]
  simp [add_comm, add_left_comm]

lemma hasDerivAt_rnorm_lineJet1 :
    HasDerivAt (fun t => rnorm (lineJet 1 t)) 0 0 :=
  hasDerivAt_sqrt_five_halves_sq.congr_of_eventuallyEq
    (Eventually.of_forall rnorm_lineJet1)

lemma vecDot_lineJet1 (t : ℝ) :
    vecDot (statePos (lineJet 1 t)) (stateVel (lineJet 1 t)) =
      t * (Real.sqrt 10 / 5) := by
  simp [vecDot, statePos_lineJet1, stateVel_lineJet1, ofLp_ofCoords,
    Fin.sum_univ_three]

lemma n0Of_lineJet1 (t : ℝ) :
    n0Of (lineJet 1 t) = ofCoords (3 / 2) t 0 := by
  apply (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).injective
  ext i
  fin_cases i <;> simp [n0Of, statePos_lineJet1, eJet0, ofCoords, PiLp.sub_apply]
    <;> ring

lemma n1Of_lineJet1 (t : ℝ) :
    n1Of (lineJet 1 t) = ofCoords 0 (Real.sqrt 10 / 5 - 1) 0 := by
  apply (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).injective
  ext i
  fin_cases i <;> simp [n1Of, stateVel_lineJet1, eJet1, ofCoords, PiLp.sub_apply]

lemma rnorm_lineJet1_ne {t : ℝ} : rnorm (lineJet 1 t) ≠ 0 := by
  rw [rnorm_lineJet1]
  exact Real.sqrt_ne_zero'.2 (by nlinarith [sq_nonneg t])

lemma rnorm_lineJet1_zero : rnorm (lineJet 1 0) = 5 / 2 := by
  rw [rnorm_lineJet1]; simp [sqrt_25_4]

lemma hasDerivAt_rnorm_inv_lineJet1 :
    HasDerivAt (fun t => (rnorm (lineJet 1 t))⁻¹) 0 0 := by
  have hne : rnorm (lineJet 1 0) ≠ 0 := rnorm_lineJet1_ne
  have h := hasDerivAt_rnorm_lineJet1.inv hne
  exact h.congr_deriv (by simp [rnorm_lineJet1_zero])

lemma hasDerivAt_rnorm_inv_pow3_lineJet1 :
    HasDerivAt (fun t => (rnorm (lineJet 1 t))⁻¹ ^ 3) 0 0 := by
  have h := (hasDerivAt_pow3_at ((rnorm (lineJet 1 0))⁻¹)).comp 0
    hasDerivAt_rnorm_inv_lineJet1
  refine h.congr_deriv ?_
  simp [rnorm_lineJet1_zero]

lemma hasDerivAt_pow5_at (a : ℝ) :
    HasDerivAt (fun x : ℝ => x ^ 5) (5 * a ^ 4) a :=
  ((hasDerivAt_id a).pow 5).congr_deriv (by simp [id])

lemma hasDerivAt_rnorm_inv_pow5_lineJet1 :
    HasDerivAt (fun t => (rnorm (lineJet 1 t))⁻¹ ^ 5) 0 0 := by
  have h := (hasDerivAt_pow5_at ((rnorm (lineJet 1 0))⁻¹)).comp 0
    hasDerivAt_rnorm_inv_lineJet1
  refine h.congr_deriv ?_
  simp [rnorm_lineJet1_zero]

lemma hasDerivAt_n0_lineJet1 :
    HasDerivAt (fun t => n0Of (lineJet 1 t)) (ofCoords 0 1 0) 0 := by
  have h := hasDerivAt_coord3 (hasDerivAt_const 0 (3 / 2 : ℝ))
    (hasDerivAt_id 0) (hasDerivAt_const 0 (0 : ℝ))
  exact h.congr_of_eventuallyEq (Eventually.of_forall n0Of_lineJet1)

lemma hasDerivAt_n1_lineJet1 :
    HasDerivAt (fun t => n1Of (lineJet 1 t)) (0 : Vec) 0 := by
  have h := hasDerivAt_coord3 (hasDerivAt_const 0 (0 : ℝ))
    (hasDerivAt_const 0 (Real.sqrt 10 / 5 - 1)) (hasDerivAt_const 0 (0 : ℝ))
  have h' : HasDerivAt (fun t => n1Of (lineJet 1 t)) (ofCoords 0 0 0) 0 :=
    h.congr_of_eventuallyEq (Eventually.of_forall n1Of_lineJet1)
  exact h'.congr_deriv ofCoords_zero

lemma hasDerivAt_pos_lineJet1 :
    HasDerivAt (fun t => statePos (lineJet 1 t)) (ofCoords 0 1 0) 0 := by
  have h := hasDerivAt_coord3 (hasDerivAt_const 0 (5 / 2 : ℝ))
    (hasDerivAt_id 0) (hasDerivAt_const 0 (0 : ℝ))
  exact h.congr_of_eventuallyEq (Eventually.of_forall statePos_lineJet1)

lemma hasDerivAt_vel_lineJet1 :
    HasDerivAt (fun t => stateVel (lineJet 1 t)) (0 : Vec) 0 := by
  have h := hasDerivAt_coord3 (hasDerivAt_const 0 (0 : ℝ))
    (hasDerivAt_const 0 (Real.sqrt 10 / 5)) (hasDerivAt_const 0 (0 : ℝ))
  have h' : HasDerivAt (fun t => stateVel (lineJet 1 t)) (ofCoords 0 0 0) 0 :=
    h.congr_of_eventuallyEq (Eventually.of_forall stateVel_lineJet1)
  exact h'.congr_deriv ofCoords_zero

lemma hasDerivAt_accel_lineJet1 :
    HasDerivAt (fun t => accelOf (lineJet 1 t)) (ofCoords 0 (-8 / 125) 0) 0 := by
  have hc := hasDerivAt_rnorm_inv_pow3_lineJet1
  have hf := hasDerivAt_pos_lineJet1
  have hneg : HasDerivAt (fun t => -((rnorm (lineJet 1 t))⁻¹ ^ 3)) 0 0 :=
    hc.neg.congr_deriv (by simp)
  have h := hneg.smul hf
  have heq : (fun t => accelOf (lineJet 1 t)) =ᶠ[𝓝 (0 : ℝ)]
      fun t => (-((rnorm (lineJet 1 t))⁻¹ ^ 3)) • statePos (lineJet 1 t) :=
    Eventually.of_forall fun t => by
      simp [accelOf, rnorm, neg_smul]
  have h' := h.congr_of_eventuallyEq heq
  have hv :
      (-((rnorm (lineJet 1 0))⁻¹ ^ 3)) • ofCoords 0 1 0
          + (0 : ℝ) • statePos (lineJet 1 0)
        = ofCoords 0 (-8 / 125) 0 := by
    rw [rnorm_lineJet1_zero]
    apply (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).injective
    ext i
    fin_cases i <;> simp [ofCoords, PiLp.smul_apply, PiLp.add_apply, smul_eq_mul]
      <;> norm_num
  exact h'.congr_deriv hv

lemma hasDerivAt_n2_lineJet1 :
    HasDerivAt (fun t => n2Of (lineJet 1 t)) (ofCoords 0 (-8 / 125) 0) 0 := by
  have h := hasDerivAt_accel_lineJet1.sub (hasDerivAt_const 0 eJet2)
  refine h.congr_deriv ?_
  simp [eJet2, ofCoords_zero]

lemma hasDerivAt_sigma_lineJet1 :
    HasDerivAt (fun t => vecDot (statePos (lineJet 1 t)) (stateVel (lineJet 1 t)))
      (Real.sqrt 10 / 5) 0 := by
  have h := (hasDerivAt_id (0 : ℝ)).const_mul (Real.sqrt 10 / 5)
  exact (h.congr_deriv (by simp)).congr_of_eventuallyEq
    (Eventually.of_forall fun t => by simpa [mul_comm] using vecDot_lineJet1 t)

lemma hasDerivAt_sigma_rinv5_lineJet1 :
    HasDerivAt
      (fun t =>
        vecDot (statePos (lineJet 1 t)) (stateVel (lineJet 1 t)) *
          (rnorm (lineJet 1 t))⁻¹ ^ 5)
      ((Real.sqrt 10 / 5) * (32 / 3125)) 0 := by
  have h := hasDerivAt_sigma_lineJet1.mul hasDerivAt_rnorm_inv_pow5_lineJet1
  refine h.congr_deriv ?_
  simp [vecDot_lineJet1, rnorm_lineJet1_zero]
  norm_num

lemma hasDerivAt_jerk_extra_lineJet1 :
    HasDerivAt
      (fun t =>
        ((3 : ℝ) *
            (vecDot (statePos (lineJet 1 t)) (stateVel (lineJet 1 t)) *
              (rnorm (lineJet 1 t))⁻¹ ^ 5)) •
          statePos (lineJet 1 t))
      (ofCoords (48 * Real.sqrt 10 / 3125) 0 0) 0 := by
  have hc := HasDerivAt.const_mul (3 : ℝ) hasDerivAt_sigma_rinv5_lineJet1
  have hp := hasDerivAt_pos_lineJet1
  have h := hc.smul hp
  have hv :
      ((3 : ℝ) *
            (vecDot (statePos (lineJet 1 0)) (stateVel (lineJet 1 0)) *
              (rnorm (lineJet 1 0))⁻¹ ^ 5)) •
          ofCoords 0 1 0
        + ((3 : ℝ) * ((Real.sqrt 10 / 5) * (32 / 3125))) • statePos (lineJet 1 0)
        = ofCoords (48 * Real.sqrt 10 / 3125) 0 0 := by
    have hσ :
        vecDot (statePos (lineJet 1 0)) (stateVel (lineJet 1 0)) = 0 := by
      simp [vecDot_lineJet1]
    rw [hσ, rnorm_lineJet1_zero, statePos_lineJet1]
    apply (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).injective
    ext i
    fin_cases i
    · simp [ofCoords, PiLp.smul_apply, PiLp.add_apply, smul_eq_mul]
      field_simp
      ring
    · simp [ofCoords, PiLp.smul_apply, PiLp.add_apply, smul_eq_mul]
    · simp [ofCoords, PiLp.smul_apply, PiLp.add_apply, smul_eq_mul]
  exact h.congr_deriv hv

lemma hasDerivAt_jerk_main_lineJet1 :
    HasDerivAt
      (fun t => (-((rnorm (lineJet 1 t))⁻¹ ^ 3)) • stateVel (lineJet 1 t))
      (0 : Vec) 0 := by
  have hneg : HasDerivAt (fun t => -((rnorm (lineJet 1 t))⁻¹ ^ 3)) 0 0 :=
    hasDerivAt_rnorm_inv_pow3_lineJet1.neg.congr_deriv (by simp)
  have h := hneg.smul hasDerivAt_vel_lineJet1
  exact h.congr_deriv (by simp)

lemma hasDerivAt_jerk_lineJet1 :
    HasDerivAt (fun t => jerkOf (lineJet 1 t))
      (ofCoords (48 * Real.sqrt 10 / 3125) 0 0) 0 := by
  have h1 := hasDerivAt_jerk_main_lineJet1
  have h2 := hasDerivAt_jerk_extra_lineJet1
  have h := h1.add h2
  have heq : (fun t => jerkOf (lineJet 1 t)) =ᶠ[𝓝 (0 : ℝ)]
      fun t =>
        (-((rnorm (lineJet 1 t))⁻¹ ^ 3)) • stateVel (lineJet 1 t)
          + ((3 : ℝ) *
              (vecDot (statePos (lineJet 1 t)) (stateVel (lineJet 1 t)) *
                (rnorm (lineJet 1 t))⁻¹ ^ 5)) •
            statePos (lineJet 1 t) :=
    Eventually.of_forall fun t => by
      unfold jerkOf
      have h3 : ((rnorm (lineJet 1 t)) ^ 3)⁻¹ = (rnorm (lineJet 1 t))⁻¹ ^ 3 :=
        inv_pow3_rnorm _
      have h5 : ((rnorm (lineJet 1 t)) ^ 5)⁻¹ = (rnorm (lineJet 1 t))⁻¹ ^ 5 := by
        have hn : rnorm (lineJet 1 t) ≠ 0 := rnorm_lineJet1_ne
        field_simp [hn]
      simp [h3, h5, rnorm, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
  have h' := h.congr_of_eventuallyEq heq
  exact h'.congr_deriv (by simp)

lemma hasDerivAt_n3_lineJet1 :
    HasDerivAt (fun t => n3Of (lineJet 1 t))
      (ofCoords (48 * Real.sqrt 10 / 3125) 0 0) 0 := by
  have h := hasDerivAt_jerk_lineJet1.sub (hasDerivAt_const 0 eJet3)
  refine h.congr_deriv ?_
  simp [eJet3, ofCoords_zero]

lemma qOf_lineJet1 (t : ℝ) : qOf (lineJet 1 t) = (9 / 4 : ℝ) + t ^ 2 := by
  simp [qOf, vecDot, n0Of_lineJet1, ofLp_ofCoords, Fin.sum_univ_three]
  ring

lemma hasDerivAt_q_lineJet1 :
    HasDerivAt (fun t => qOf (lineJet 1 t)) 0 0 :=
  hasDerivAt_nine_four_sq_add.congr_of_eventuallyEq
    (Eventually.of_forall qOf_lineJet1)

lemma q1Of_lineJet1 (t : ℝ) :
    q1Of (lineJet 1 t) = 2 * t * (Real.sqrt 10 / 5 - 1) := by
  simp [q1Of, vecDot, n0Of_lineJet1, n1Of_lineJet1, ofLp_ofCoords,
    Fin.sum_univ_three]
  ring

lemma hasDerivAt_q1_lineJet1 :
    HasDerivAt (fun t => q1Of (lineJet 1 t)) (2 * (Real.sqrt 10 / 5 - 1)) 0 := by
  have h := (hasDerivAt_id (0 : ℝ)).const_mul (2 * (Real.sqrt 10 / 5 - 1))
  exact (h.congr_deriv (by simp)).congr_of_eventuallyEq
    (Eventually.of_forall fun t => by simpa [mul_assoc, mul_comm, mul_left_comm] using q1Of_lineJet1 t)

lemma n2Of_lineJet1 (t : ℝ) :
    n2Of (lineJet 1 t) =
      ofCoords (1 - (5 / 2) * (rnorm (lineJet 1 t))⁻¹ ^ 3)
        (-t * (rnorm (lineJet 1 t))⁻¹ ^ 3) 0 := by
  apply (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).injective
  ext i
  have ha : accelOf (lineJet 1 t) =
      -((rnorm (lineJet 1 t))⁻¹ ^ 3) • statePos (lineJet 1 t) := by
    simp [accelOf, rnorm, inv_pow3_rnorm, neg_smul]
  rw [n2Of, ha, statePos_lineJet1]
  fin_cases i
  · simp [eJet2, ofCoords, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
    ring
  · simp [eJet2, ofCoords, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
    ring
  · simp [eJet2, ofCoords, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]

lemma n3Of_lineJet1 (t : ℝ) :
    n3Of (lineJet 1 t) =
      ofCoords
        ((15 / 2) * t * (Real.sqrt 10 / 5) * (rnorm (lineJet 1 t))⁻¹ ^ 5)
        (1 - (Real.sqrt 10 / 5) * (rnorm (lineJet 1 t))⁻¹ ^ 3
          + 3 * t ^ 2 * (Real.sqrt 10 / 5) * (rnorm (lineJet 1 t))⁻¹ ^ 5)
        0 := by
  apply (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).injective
  ext i
  have h3 : ((rnorm (lineJet 1 t)) ^ 3)⁻¹ = (rnorm (lineJet 1 t))⁻¹ ^ 3 :=
    inv_pow3_rnorm _
  have h5 : ((rnorm (lineJet 1 t)) ^ 5)⁻¹ = (rnorm (lineJet 1 t))⁻¹ ^ 5 := by
    have hn : rnorm (lineJet 1 t) ≠ 0 := rnorm_lineJet1_ne
    field_simp [hn]
  have hj :
      jerkOf (lineJet 1 t) =
        (-((rnorm (lineJet 1 t))⁻¹ ^ 3)) • stateVel (lineJet 1 t)
          + ((3 : ℝ) * vecDot (statePos (lineJet 1 t)) (stateVel (lineJet 1 t)) *
              (rnorm (lineJet 1 t))⁻¹ ^ 5) •
            statePos (lineJet 1 t) := by
    unfold jerkOf
    simp [h3, h5, rnorm, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
  rw [n3Of, hj, vecDot_lineJet1, stateVel_lineJet1, statePos_lineJet1]
  fin_cases i
  · simp [eJet3, ofCoords, PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply,
      smul_eq_mul]
    ring
  · simp [eJet3, ofCoords, PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply,
      smul_eq_mul]
    ring
  · simp [eJet3, ofCoords, PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply,
      smul_eq_mul]

lemma q2Of_lineJet1 (t : ℝ) :
    q2Of (lineJet 1 t) =
      2 * (Real.sqrt 10 / 5 - 1) ^ 2
        + 3 * (1 - (5 / 2) * (rnorm (lineJet 1 t))⁻¹ ^ 3)
        - 2 * t ^ 2 * (rnorm (lineJet 1 t))⁻¹ ^ 3 := by
  simp [q2Of, vecDot, n1Of_lineJet1, n0Of_lineJet1, n2Of_lineJet1, ofLp_ofCoords,
    Fin.sum_univ_three]
  ring

lemma hasDerivAt_t_sq_rinv3_lineJet1 :
    HasDerivAt (fun t => t ^ 2 * (rnorm (lineJet 1 t))⁻¹ ^ 3) 0 0 := by
  have h := hasDerivAt_pow2_id.mul hasDerivAt_rnorm_inv_pow3_lineJet1
  exact h.congr_deriv (by simp [rnorm_lineJet1_zero])

lemma hasDerivAt_q2_lineJet1 :
    HasDerivAt (fun t => q2Of (lineJet 1 t)) 0 0 := by
  have hc := hasDerivAt_const (0 : ℝ) (2 * (Real.sqrt 10 / 5 - 1) ^ 2)
  have hr := hasDerivAt_rnorm_inv_pow3_lineJet1
  have hmid : HasDerivAt
      (fun t : ℝ => 1 - (5 / 2) * (rnorm (lineJet 1 t))⁻¹ ^ 3) 0 0 := by
    have h := (hasDerivAt_const 0 (1 : ℝ)).sub
      ((hasDerivAt_const 0 (5 / 2 : ℝ)).mul hr)
    exact h.congr_deriv (by simp)
  have h3 := HasDerivAt.const_mul (3 : ℝ) hmid
  have ht := hasDerivAt_t_sq_rinv3_lineJet1
  have h2t := HasDerivAt.const_mul (2 : ℝ) ht
  have hadd := (hc.add h3).sub h2t
  have heq : (fun t => q2Of (lineJet 1 t)) =ᶠ[𝓝 (0 : ℝ)]
      fun t =>
        2 * (Real.sqrt 10 / 5 - 1) ^ 2
          + 3 * (1 - (5 / 2) * (rnorm (lineJet 1 t))⁻¹ ^ 3)
          - 2 * (t ^ 2 * (rnorm (lineJet 1 t))⁻¹ ^ 3) :=
    Eventually.of_forall fun t => by simpa [mul_assoc] using q2Of_lineJet1 t
  exact hadd.congr_of_eventuallyEq heq |>.congr_deriv (by ring)

lemma q3Of_lineJet1 (t : ℝ) :
    q3Of (lineJet 1 t) =
      -6 * (Real.sqrt 10 / 5 - 1) * t * (rnorm (lineJet 1 t))⁻¹ ^ 3
        + (45 / 2) * t * (Real.sqrt 10 / 5) * (rnorm (lineJet 1 t))⁻¹ ^ 5
        + 2 * t
        - 2 * t * (Real.sqrt 10 / 5) * (rnorm (lineJet 1 t))⁻¹ ^ 3
        + 6 * t ^ 3 * (Real.sqrt 10 / 5) * (rnorm (lineJet 1 t))⁻¹ ^ 5 := by
  simp [q3Of, vecDot, n1Of_lineJet1, n2Of_lineJet1, n0Of_lineJet1, n3Of_lineJet1,
    ofLp_ofCoords, Fin.sum_univ_three]
  ring

lemma hasDerivAt_t_rinv3_lineJet1 :
    HasDerivAt (fun t => t * (rnorm (lineJet 1 t))⁻¹ ^ 3) (8 / 125) 0 := by
  have h := (hasDerivAt_id (0 : ℝ)).mul hasDerivAt_rnorm_inv_pow3_lineJet1
  refine h.congr_deriv ?_
  simp [rnorm_lineJet1_zero]
  norm_num

lemma hasDerivAt_t_rinv5_lineJet1 :
    HasDerivAt (fun t => t * (rnorm (lineJet 1 t))⁻¹ ^ 5) (32 / 3125) 0 := by
  have h := (hasDerivAt_id (0 : ℝ)).mul hasDerivAt_rnorm_inv_pow5_lineJet1
  refine h.congr_deriv ?_
  simp [rnorm_lineJet1_zero]
  norm_num

lemma hasDerivAt_t3_rinv5_lineJet1 :
    HasDerivAt (fun t => t ^ 3 * (rnorm (lineJet 1 t))⁻¹ ^ 5) 0 0 := by
  have ht : HasDerivAt (fun t : ℝ => t ^ 3) 0 0 :=
    (hasDerivAt_pow3_at 0).congr_deriv (by norm_num)
  have h := ht.mul hasDerivAt_rnorm_inv_pow5_lineJet1
  exact h.congr_deriv (by simp [rnorm_lineJet1_zero])

lemma q3'_lineJet1_eval :
    -6 * (Real.sqrt 10 / 5 - 1) * (8 / 125)
      + (45 / 2) * (Real.sqrt 10 / 5) * (32 / 3125)
      + 2
      - 2 * (Real.sqrt 10 / 5) * (8 / 125)
      = 298 / 125 - 176 * Real.sqrt 10 / 3125 := by
  field_simp
  ring

lemma hasDerivAt_q3_lineJet1 :
    HasDerivAt (fun t => q3Of (lineJet 1 t))
      (298 / 125 - 176 * Real.sqrt 10 / 3125) 0 := by
  have hA := HasDerivAt.const_mul (-6 * (Real.sqrt 10 / 5 - 1))
    hasDerivAt_t_rinv3_lineJet1
  have hB := HasDerivAt.const_mul ((45 / 2) * (Real.sqrt 10 / 5))
    hasDerivAt_t_rinv5_lineJet1
  have hC := HasDerivAt.const_mul (2 : ℝ) (hasDerivAt_id (0 : ℝ))
  have hD := HasDerivAt.const_mul (-2 * (Real.sqrt 10 / 5))
    hasDerivAt_t_rinv3_lineJet1
  have hE := HasDerivAt.const_mul (6 * (Real.sqrt 10 / 5))
    hasDerivAt_t3_rinv5_lineJet1
  have h := (((hA.add hB).add hC).add hD).add hE
  have hd :
      (-6 * (Real.sqrt 10 / 5 - 1)) * (8 / 125)
          + ((45 / 2) * (Real.sqrt 10 / 5)) * (32 / 3125)
          + (2 : ℝ) * 1
          + (-2 * (Real.sqrt 10 / 5)) * (8 / 125)
          + (6 * (Real.sqrt 10 / 5)) * 0
        = 298 / 125 - 176 * Real.sqrt 10 / 3125 := by
    convert q3'_lineJet1_eval using 1
    · ring
  have h' := h.congr_deriv hd
  have heq : (fun t => q3Of (lineJet 1 t)) =ᶠ[𝓝 (0 : ℝ)]
      fun t =>
        -6 * (Real.sqrt 10 / 5 - 1) * (t * (rnorm (lineJet 1 t))⁻¹ ^ 3)
          + (45 / 2) * (Real.sqrt 10 / 5) * (t * (rnorm (lineJet 1 t))⁻¹ ^ 5)
          + 2 * t
          + (-2 * (Real.sqrt 10 / 5)) * (t * (rnorm (lineJet 1 t))⁻¹ ^ 3)
          + (6 * (Real.sqrt 10 / 5)) * (t ^ 3 * (rnorm (lineJet 1 t))⁻¹ ^ 5) :=
    Eventually.of_forall fun t => by
      simpa [mul_assoc, mul_left_comm, mul_comm, sub_eq_add_neg] using
        q3Of_lineJet1 t
  exact h'.congr_of_eventuallyEq heq

lemma hasDerivAt_p_lineJet1 :
    HasDerivAt (fun t => pOf (lineJet 1 t)) 0 0 := by
  have hpt : (9 / 4 : ℝ) + (0 : ℝ) ^ 2 = 9 / 4 := by norm_num
  have hr : HasDerivAt (fun x : ℝ => x ^ (-(1 / 2 : ℝ))) (-(4 / 27 : ℝ))
      ((9 / 4 : ℝ) + 0 ^ 2) := by
    rw [hpt]; exact hasDerivAt_rpow_neg_half_at_nine_four
  have h := hr.comp 0 hasDerivAt_nine_four_sq_add
  have h0 : HasDerivAt ((fun x : ℝ => x ^ (-(1 / 2 : ℝ))) ∘ fun t : ℝ => 9 / 4 + t ^ 2)
      0 0 := h.congr_deriv (mul_zero _)
  refine h0.congr_of_eventuallyEq ?_
  exact Eventually.of_forall fun t => by simp [pOf, qOf_lineJet1]

lemma hasDerivAt_q_rpow_neg_three_halves_lineJet1 :
    HasDerivAt (fun t => (qOf (lineJet 1 t)) ^ (-(3 / 2 : ℝ))) 0 0 := by
  have hq : qOf (lineJet 1 0) = 9 / 4 := by
    rw [qOf_lineJet1]; simp
  have hr : HasDerivAt (fun x : ℝ => x ^ (-(3 / 2 : ℝ))) (-(16 / 81 : ℝ))
      (qOf (lineJet 1 0)) := by
    rw [hq]; exact hasDerivAt_rpow_neg_three_halves_at_nine_four
  have h := hr.comp 0 hasDerivAt_q_lineJet1
  exact h.congr_deriv (by simp)

lemma hasDerivAt_p1_lineJet1 :
    HasDerivAt (fun t => p1Of (lineJet 1 t))
      (-(8 / 27) * (Real.sqrt 10 / 5 - 1)) 0 := by
  have hA := hasDerivAt_q_rpow_neg_three_halves_lineJet1
  have hq1 := hasDerivAt_q1_lineJet1
  have hmul := hA.mul hq1
  have h := HasDerivAt.const_mul (-(1 / 2 : ℝ)) hmul
  have hd :
      (-(1 / 2 : ℝ)) *
          (0 * q1Of (lineJet 1 0)
            + (qOf (lineJet 1 0)) ^ (-(3 / 2 : ℝ)) *
              (2 * (Real.sqrt 10 / 5 - 1)))
        = -(8 / 27) * (Real.sqrt 10 / 5 - 1) := by
    rw [qOf_lineJet1, q1Of_lineJet1]
    simp [rpow_neg_three_halves_nine_four]
    ring
  have h' := h.congr_deriv hd
  have heq : (fun t => p1Of (lineJet 1 t)) =ᶠ[𝓝 (0 : ℝ)]
      fun t =>
        -(1 / 2 : ℝ) * ((qOf (lineJet 1 t)) ^ (-(3 / 2 : ℝ)) * q1Of (lineJet 1 t)) :=
    Eventually.of_forall fun t => by simp [p1Of, mul_assoc]
  exact h'.congr_of_eventuallyEq heq

lemma hasDerivAt_q_rpow_neg_five_halves_lineJet1 :
    HasDerivAt (fun t => (qOf (lineJet 1 t)) ^ (-(5 / 2 : ℝ))) 0 0 := by
  have hq : qOf (lineJet 1 0) = 9 / 4 := by rw [qOf_lineJet1]; simp
  have hx : (0 : ℝ) < qOf (lineJet 1 0) := by rw [hq]; norm_num
  have hr := Real.hasDerivAt_rpow_const (x := qOf (lineJet 1 0))
    (p := -(5 / 2 : ℝ)) (Or.inl hx.ne')
  have h := hr.comp 0 hasDerivAt_q_lineJet1
  exact h.congr_deriv (by simp)

lemma hasDerivAt_q_rpow_neg_seven_halves_lineJet1 :
    HasDerivAt (fun t => (qOf (lineJet 1 t)) ^ (-(7 / 2 : ℝ))) 0 0 := by
  have hq : qOf (lineJet 1 0) = 9 / 4 := by rw [qOf_lineJet1]; simp
  have hx : (0 : ℝ) < qOf (lineJet 1 0) := by rw [hq]; norm_num
  have hr := Real.hasDerivAt_rpow_const (x := qOf (lineJet 1 0))
    (p := -(7 / 2 : ℝ)) (Or.inl hx.ne')
  have h := hr.comp 0 hasDerivAt_q_lineJet1
  exact h.congr_deriv (by simp)

lemma hasDerivAt_p2_lineJet1 :
    HasDerivAt (fun t => p2Of (lineJet 1 t)) 0 0 := by
  have hq1 := hasDerivAt_q1_lineJet1
  have hq2 := hasDerivAt_q2_lineJet1
  have hA := hasDerivAt_q_rpow_neg_five_halves_lineJet1
  have hB := hasDerivAt_q_rpow_neg_three_halves_lineJet1
  have hq1sq := hq1.pow 2
  have ht1 := (HasDerivAt.const_mul (3 / 4 : ℝ) (hA.mul hq1sq))
  have ht2 := (HasDerivAt.const_mul (1 / 2 : ℝ) (hB.mul hq2))
  have h := ht1.sub ht2
  have hd :
      (3 / 4 : ℝ) *
            (0 * ((fun t => q1Of (lineJet 1 t)) ^ 2) 0
              + (qOf (lineJet 1 0)) ^ (-(5 / 2 : ℝ)) *
                ((2 : ℕ) * q1Of (lineJet 1 0) ^ (2 - 1) *
                  (2 * (Real.sqrt 10 / 5 - 1))))
          - (1 / 2 : ℝ) *
            (0 * q2Of (lineJet 1 0)
              + (qOf (lineJet 1 0)) ^ (-(3 / 2 : ℝ)) * 0)
        = 0 := by
    simp [q1Of_lineJet1, Pi.pow_apply]
  have h' := h.congr_deriv hd
  have heq : (fun t => p2Of (lineJet 1 t)) =ᶠ[𝓝 (0 : ℝ)]
      fun t =>
        (3 / 4 : ℝ) * ((qOf (lineJet 1 t)) ^ (-(5 / 2 : ℝ)) * q1Of (lineJet 1 t) ^ 2)
          - (1 / 2 : ℝ) * ((qOf (lineJet 1 t)) ^ (-(3 / 2 : ℝ)) * q2Of (lineJet 1 t)) :=
    Eventually.of_forall fun t => by
      simp [p2Of, mul_assoc]
  exact h'.congr_of_eventuallyEq heq

def p3deriv_axis1 : ℝ :=
  (9 / 4 : ℝ) * ((9 / 4 : ℝ) ^ (-(5 / 2 : ℝ)) *
      (2 * (Real.sqrt 10 / 5 - 1)) *
      (133 / 25 - 4 * Real.sqrt 10 / 5))
    - (2⁻¹) * ((9 / 4 : ℝ) ^ (-(3 / 2 : ℝ)) *
      (298 / 125 - 176 * Real.sqrt 10 / 3125))

lemma hasDerivAt_p3_lineJet1 :
    HasDerivAt (fun t => p3Of (lineJet 1 t)) p3deriv_axis1 0 := by
  have hq1 := hasDerivAt_q1_lineJet1
  have hq2 := hasDerivAt_q2_lineJet1
  have hq3 := hasDerivAt_q3_lineJet1
  have hA := hasDerivAt_q_rpow_neg_seven_halves_lineJet1
  have hB := hasDerivAt_q_rpow_neg_five_halves_lineJet1
  have hC := hasDerivAt_q_rpow_neg_three_halves_lineJet1
  have hq1c := hq1.pow 3
  have ht1 := HasDerivAt.const_mul (-(15 / 8 : ℝ)) (hA.mul hq1c)
  have hmid := (hB.mul hq1).mul hq2
  have ht2 := HasDerivAt.const_mul (9 / 4 : ℝ) hmid
  have ht3 := HasDerivAt.const_mul (1 / 2 : ℝ) (hC.mul hq3)
  have h := (ht1.add ht2).sub ht3
  have hd :
      (-(15 / 8 : ℝ)) *
            (0 * q1Of (lineJet 1 0) ^ 3
              + (qOf (lineJet 1 0)) ^ (-(7 / 2 : ℝ)) *
                (3 * q1Of (lineJet 1 0) ^ 2 * (2 * (Real.sqrt 10 / 5 - 1))))
          + (9 / 4 : ℝ) *
            ((0 * q1Of (lineJet 1 0)
                + (qOf (lineJet 1 0)) ^ (-(5 / 2 : ℝ)) * (2 * (Real.sqrt 10 / 5 - 1))) *
                q2Of (lineJet 1 0)
              + ((qOf (lineJet 1 0)) ^ (-(5 / 2 : ℝ)) * q1Of (lineJet 1 0)) * 0)
          - (1 / 2 : ℝ) *
            (0 * q3Of (lineJet 1 0)
              + (qOf (lineJet 1 0)) ^ (-(3 / 2 : ℝ)) *
                (298 / 125 - 176 * Real.sqrt 10 / 3125))
        = p3deriv_axis1 := by
    have hq0 : qOf (lineJet 1 0) = 9 / 4 := by rw [qOf_lineJet1]; simp
    have hq20 : q2Of (lineJet 1 0) = 133 / 25 - 4 * Real.sqrt 10 / 5 := by
      rw [lineJet_zero, q2Of_sStar]
    rw [q1Of_lineJet1, hq0, hq20]
    simp
    rfl
  have h' := h.congr_deriv hd
  have heq : (fun t => p3Of (lineJet 1 t)) =ᶠ[𝓝 (0 : ℝ)]
      fun t =>
        (-(15 / 8 : ℝ)) * ((qOf (lineJet 1 t)) ^ (-(7 / 2 : ℝ)) * q1Of (lineJet 1 t) ^ 3)
          + (9 / 4 : ℝ) *
            ((qOf (lineJet 1 t)) ^ (-(5 / 2 : ℝ)) * q1Of (lineJet 1 t) * q2Of (lineJet 1 t))
          - (1 / 2 : ℝ) * ((qOf (lineJet 1 t)) ^ (-(3 / 2 : ℝ)) * q3Of (lineJet 1 t)) :=
    Eventually.of_forall fun t => by
      simp [p3Of, mul_assoc]
  exact h'.congr_of_eventuallyEq heq

lemma two_jetC_axis1_eval :
    (2 / 3 : ℝ) * (-8 / 125)
      + 2 * ((-(8 / 27) * (Real.sqrt 10 / 5 - 1)) * (Real.sqrt 10 / 5 - 1))
      + (-532 / 675 + 16 * Real.sqrt 10 / 135)
      = 2 * jetC := by
  unfold jetC
  field_simp
  ring_nf
  simp [sqrt10_sq]
  ring

lemma hasDerivAt_u2_lineJet1 :
    HasDerivAt (fun t => u2Of (lineJet 1 t)) (ofCoords 0 (2 * jetC) 0) 0 := by
  have hp := hasDerivAt_p_lineJet1
  have hn2 := hasDerivAt_n2_lineJet1
  have hp1 := hasDerivAt_p1_lineJet1
  have hn1 := hasDerivAt_n1_lineJet1
  have hp2 := hasDerivAt_p2_lineJet1
  have hn0 := hasDerivAt_n0_lineJet1
  have h1 := hp.smul hn2
  have hmid := hp1.smul hn1
  have h2 := HasDerivAt.const_smul (2 : ℝ) hmid
  have h3 := hp2.smul hn0
  have hadd := (h1.add h2).add h3
  have hv :
      pOf (lineJet 1 0) • ofCoords 0 (-8 / 125) 0 + (0 : ℝ) • n2Of (lineJet 1 0)
          + (2 : ℝ) •
            (p1Of (lineJet 1 0) • (0 : Vec)
              + (-(8 / 27) * (Real.sqrt 10 / 5 - 1)) • n1Of (lineJet 1 0))
          + (p2Of (lineJet 1 0) • ofCoords 0 1 0 + (0 : ℝ) • n0Of (lineJet 1 0))
        = ofCoords 0 (2 * jetC) 0 := by
    rw [lineJet_zero, pOf_sStar, p1Of_sStar, p2Of_sStar, n1Of_sStar, n2Of_sStar]
    apply (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).injective
    ext i
    fin_cases i
    · simp [ofCoords, PiLp.smul_apply, PiLp.add_apply, smul_eq_mul]
    · simp [ofCoords, PiLp.smul_apply, PiLp.add_apply, smul_eq_mul]
      simpa [mul_assoc, add_assoc, add_left_comm, add_comm, mul_comm, mul_left_comm]
        using two_jetC_axis1_eval
    · simp [ofCoords, PiLp.smul_apply, PiLp.add_apply, smul_eq_mul]
  exact hadd.congr_deriv hv

lemma six_jetE_axis1_eval :
    (2 / 3 : ℝ) * (48 * Real.sqrt 10 / 3125)
      + 3 * ((-(8 / 27) * (Real.sqrt 10 / 5 - 1)) * (21 / 25))
      + p3deriv_axis1 * (3 / 2)
      = 6 * jetE := by
  unfold p3deriv_axis1 jetE
  rw [rpow_neg_five_halves_nine_four, rpow_neg_three_halves_nine_four]
  field_simp
  ring_nf
  simp [sqrt10_sq]
  ring

lemma hasDerivAt_u3_lineJet1 :
    HasDerivAt (fun t => u3Of (lineJet 1 t)) (ofCoords (6 * jetE) 0 0) 0 := by
  have hp := hasDerivAt_p_lineJet1
  have hn3 := hasDerivAt_n3_lineJet1
  have hp1 := hasDerivAt_p1_lineJet1
  have hn2 := hasDerivAt_n2_lineJet1
  have hp2 := hasDerivAt_p2_lineJet1
  have hn1 := hasDerivAt_n1_lineJet1
  have hp3 := hasDerivAt_p3_lineJet1
  have hn0 := hasDerivAt_n0_lineJet1
  have h1 := hp.smul hn3
  have ha := hp1.smul hn2
  have h2 := HasDerivAt.const_smul (3 : ℝ) ha
  have hb := hp2.smul hn1
  have h3 := HasDerivAt.const_smul (3 : ℝ) hb
  have h4 := hp3.smul hn0
  have hadd := ((h1.add h2).add h3).add h4
  have hv :
      pOf (lineJet 1 0) • ofCoords (48 * Real.sqrt 10 / 3125) 0 0
          + (0 : ℝ) • n3Of (lineJet 1 0)
          + (3 : ℝ) •
            (p1Of (lineJet 1 0) • ofCoords 0 (-8 / 125) 0
              + (-(8 / 27) * (Real.sqrt 10 / 5 - 1)) • n2Of (lineJet 1 0))
          + (3 : ℝ) •
            (p2Of (lineJet 1 0) • (0 : Vec) + (0 : ℝ) • n1Of (lineJet 1 0))
          + (p3Of (lineJet 1 0) • ofCoords 0 1 0
            + p3deriv_axis1 • n0Of (lineJet 1 0))
        = ofCoords (6 * jetE) 0 0 := by
    rw [lineJet_zero, pOf_sStar, p1Of_sStar, p2Of_sStar, p3Of_sStar,
      n0Of_sStar, n1Of_sStar, n2Of_sStar, n3Of_sStar]
    apply (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).injective
    ext i
    fin_cases i
    · simp [ofCoords, PiLp.smul_apply, PiLp.add_apply, smul_eq_mul]
      simpa [mul_assoc, add_assoc, add_left_comm, add_comm, mul_comm, mul_left_comm]
        using six_jetE_axis1_eval
    · simp [ofCoords, PiLp.smul_apply, PiLp.add_apply, smul_eq_mul]
    · simp [ofCoords, PiLp.smul_apply, PiLp.add_apply, smul_eq_mul]
  exact hadd.congr_deriv hv

lemma hasDerivAt_losTaylor23_lineJet1 (i : Fin 6) :
    HasDerivAt (fun t => losTaylor23 (lineJet 1 t) i) (jetMatrix i 1) 0 := by
  have hu2 := hasDerivAt_u2_lineJet1
  have hu3 := hasDerivAt_u3_lineJet1
  fin_cases i
  · have h := (hasDerivAt_ofLp hu2 0).div_const (2 : ℝ)
    refine h.congr_deriv ?_
    simp [jetMatrix, ofLp_ofCoords]
  · have h := (hasDerivAt_ofLp hu2 1).div_const (2 : ℝ)
    refine h.congr_deriv ?_
    simp [jetMatrix, ofLp_ofCoords]
  · have h := (hasDerivAt_ofLp hu2 2).div_const (2 : ℝ)
    refine h.congr_deriv ?_
    simp [jetMatrix, ofLp_ofCoords]
  · have h := (hasDerivAt_ofLp hu3 0).div_const (6 : ℝ)
    refine h.congr_deriv ?_
    simp [jetMatrix, ofLp_ofCoords]
  · have h := (hasDerivAt_ofLp hu3 1).div_const (6 : ℝ)
    refine h.congr_deriv ?_
    simp [jetMatrix, ofLp_ofCoords]
  · have h := (hasDerivAt_ofLp hu3 2).div_const (6 : ℝ)
    refine h.congr_deriv ?_
    simp [jetMatrix, ofLp_ofCoords]

lemma deriv_losTaylor23_lineJet1 (i : Fin 6) :
    deriv (fun t => losTaylor23 (lineJet 1 t) i) 0 = jetMatrix i 1 :=
  (hasDerivAt_losTaylor23_lineJet1 i).deriv

lemma eq_sum_single (v : Fin 6 → ℝ) :
    v = ∑ j : Fin 6, v j • Pi.single j (1 : ℝ) := by
  ext k
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply]
  rw [Finset.sum_eq_single k]
  · simp
  · intro j _ hjk
    have : k ≠ j := hjk.symm
    simp [this]
  · simp

lemma fderiv_losTaylor23_basis (j i : Fin 6) :
    fderiv ℝ losTaylor23 sStar (Pi.single j 1) i = jetMatrix i j := by
  rw [fderiv_losTaylor23_single]
  fin_cases j
  · exact deriv_losTaylor23_lineJet0 i
  · exact deriv_losTaylor23_lineJet1 i
  · exact deriv_losTaylor23_lineJet2 i
  · exact deriv_losTaylor23_lineJet3 i
  · exact deriv_losTaylor23_lineJet4 i
  · exact deriv_losTaylor23_lineJet5 i

lemma fderiv_losTaylor23_eq_toLin' :
    (fderiv ℝ losTaylor23 sStar : (Fin 6 → ℝ) →ₗ[ℝ] (Fin 6 → ℝ))
      = Matrix.toLin' jetMatrix := by
  apply LinearMap.ext
  intro v
  ext i
  change fderiv ℝ losTaylor23 sStar v i = Matrix.toLin' jetMatrix v i
  have hL :
      fderiv ℝ losTaylor23 sStar v i
        = ∑ j : Fin 6, v j * jetMatrix i j := by
    conv_lhs => rw [eq_sum_single v]
    simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    refine Finset.sum_congr rfl ?_
    intro j _
    simp [fderiv_losTaylor23_basis]
  have hR :
      Matrix.toLin' jetMatrix v i = ∑ j : Fin 6, jetMatrix i j * v j := by
    simp [Matrix.toLin'_apply, Matrix.mulVec, dotProduct]
  rw [hL, hR]
  refine Finset.sum_congr rfl ?_
  intro j _
  ring

def cartRadius : ℝ := 1 / 80

def sdCart (s : Fin 6 → ℝ) : Fin 6 → ℝ :=
  sdPairCoord
    (secondDiff (fun t => los obs (keplerIC s) t) hSD1)
    (secondDiff (fun t => los obs (keplerIC s) t) hSD2)

lemma secondDiff_add (f g : ℝ → Vec) (h : ℝ) :
    secondDiff (fun t => f t + g t) h = secondDiff f h + secondDiff g h := by
  ext i
  simp [secondDiff, PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  ring

lemma secondDiff_smul (c : ℝ) (f : ℝ → Vec) (h : ℝ) :
    secondDiff (fun t => c • f t) h = c • secondDiff f h := by
  ext i
  simp [secondDiff, PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  ring

lemma univF_zero (s : Fin 6 → ℝ) : univF s 0 = 0 := by
  simp [univF, stumpffC, stumpffS]

lemma hasFDerivAt_uncurry_univF (chi0 : ℝ) :
    HasFDerivAt (Function.uncurry univF)
      (fderiv ℝ (Function.uncurry univF) (sStar, chi0)) (sStar, chi0) :=
  ((contDiffAt_uncurry_univF chi0).differentiableAt (by decide)).hasFDerivAt

lemma hasFDerivAt_pair_sStar (chi0 : ℝ) :
    HasFDerivAt (fun chi : ℝ => (sStar, chi))
      (ContinuousLinearMap.inr ℝ (Fin 6 → ℝ) ℝ) chi0 := by
  have hconst : HasFDerivAt (fun _ : ℝ => sStar)
      (0 : ℝ →L[ℝ] (Fin 6 → ℝ)) chi0 := hasFDerivAt_const _ _
  have hid : HasFDerivAt (fun chi : ℝ => chi) (ContinuousLinearMap.id ℝ ℝ) chi0 :=
    hasFDerivAt_id chi0
  exact hconst.prodMk hid

lemma fderiv_univF_comp_inr (chi0 : ℝ) :
    fderiv ℝ (Function.uncurry univF) (sStar, chi0) ∘L
        ContinuousLinearMap.inr ℝ (Fin 6 → ℝ) ℝ
      = ContinuousLinearMap.toSpanSingleton ℝ (5 / 2) := by
  apply ContinuousLinearMap.ext
  intro c
  have hjoint := hasFDerivAt_uncurry_univF chi0
  have hpair := hasFDerivAt_pair_sStar chi0
  have hcomp := hjoint.comp chi0 hpair
  have hchi : HasFDerivAt (univF sStar)
      (ContinuousLinearMap.toSpanSingleton ℝ (5 / 2)) chi0 := by
    rw [← univF_f2_sStar]
    exact hasFDerivAt_univF_chi_sStar chi0
  have : fderiv ℝ (Function.uncurry univF) (sStar, chi0)
        (ContinuousLinearMap.inr ℝ (Fin 6 → ℝ) ℝ c)
      = (5 / 2) * c := by
    have h1 := hcomp.unique hchi
    have := congrArg (fun L : ℝ →L[ℝ] ℝ => L c) h1
    simpa [ContinuousLinearMap.comp_apply, ContinuousLinearMap.toSpanSingleton_apply, mul_comm] using this
  simpa [ContinuousLinearMap.comp_apply, ContinuousLinearMap.toSpanSingleton_apply, mul_comm] using this


lemma univF_partial_chi_invertible (t : ℝ) :
    (fderiv ℝ (Function.uncurry univF) (sStar, 2 * t / 5) ∘L
        ContinuousLinearMap.inr ℝ (Fin 6 → ℝ) ℝ).IsInvertible := by
  rw [fderiv_univF_comp_inr]
  exact ContinuousLinearMap.IsInvertible.of_inverse
    (g := ContinuousLinearMap.toSpanSingleton ℝ (2 / 5))
    (by ext; simp) (by ext; simp)

lemma contDiffAt_uncurry_univF_two (t : ℝ) :
    ContDiffAt ℝ 2 (Function.uncurry univF) (sStar, 2 * t / 5) :=
  (contDiffAt_uncurry_univF (2 * t / 5)).of_le (by exact le_top)

noncomputable def chiSmooth (t : ℝ) : (Fin 6 → ℝ) → ℝ :=
  (contDiffAt_uncurry_univF_two t).implicitFunction
    (by decide) (univF_partial_chi_invertible t)

lemma chiSmooth_sStar (t : ℝ) : chiSmooth t sStar = 2 * t / 5 :=
  (contDiffAt_uncurry_univF_two t).implicitFunction_apply_self
    (by decide) (univF_partial_chi_invertible t)

lemma eventually_univF_chiSmooth (t : ℝ) :
    ∀ᶠ s in 𝓝 sStar, univF s (chiSmooth t s) = t := by
  have h := (contDiffAt_uncurry_univF_two t).eventually_apply_implicitFunction
    (by decide) (univF_partial_chi_invertible t)
  refine h.mono ?_
  intro s hs
  simpa [chiSmooth, Function.uncurry, univF_sStar] using hs

lemma contDiffAt_chiSmooth (t : ℝ) :
    ContDiffAt ℝ 2 (chiSmooth t) sStar :=
  (contDiffAt_uncurry_univF_two t).contDiffAt_implicitFunction
    (by decide) (univF_partial_chi_invertible t)

lemma eventually_chiOf_eq_chiSmooth (t : ℝ) :
    ∀ᶠ s in 𝓝 sStar, chiOf s t = chiSmooth t s := by
  have hiff := eventually_apply_eq_iff_implicitFunctionOfBivariate
    (eventually_hasFDerivAt_univF_s (2 * t / 5))
    (eventually_hasFDerivAt_univF_chi (2 * t / 5))
    (continuousAt_univF_f1 (2 * t / 5))
    (continuousAt_univF_f2 (2 * t / 5))
    (univF_f2_invertible t)
  have hsm := eventually_univF_chiSmooth t
  have htend : Tendsto (fun s => (s, chiSmooth t s)) (𝓝 sStar)
      (𝓝 (sStar, 2 * t / 5)) := by
    have hc := (contDiffAt_chiSmooth t).continuousAt
    have : Tendsto (chiSmooth t) (𝓝 sStar) (𝓝 (2 * t / 5)) := by
      simpa [chiSmooth_sStar] using hc.tendsto
    exact Tendsto.prodMk_nhds continuousAt_id.tendsto this
  have hiff' : ∀ᶠ s in 𝓝 sStar,
      univF s (chiSmooth t s) = t ↔ chiOf s t = chiSmooth t s := by
    have : ∀ᶠ v : (Fin 6 → ℝ) × ℝ in 𝓝 (sStar, 2 * t / 5),
        univF v.1 v.2 = t ↔
          implicitFunctionOfBivariate
              (eventually_hasFDerivAt_univF_s (2 * t / 5))
              (eventually_hasFDerivAt_univF_chi (2 * t / 5))
              (continuousAt_univF_f1 (2 * t / 5))
              (continuousAt_univF_f2 (2 * t / 5))
              (univF_f2_invertible t) v.1 = v.2 := by
      refine hiff.mono ?_
      intro v hv
      simpa [univF_sStar] using hv
    exact htend.eventually this
  filter_upwards [hiff', hsm] with s hiffs hs
  exact hiffs.mp hs

lemma contDiffAt_chiOf (t : ℝ) :
    ContDiffAt ℝ 2 (fun s => chiOf s t) sStar := by
  refine (contDiffAt_chiSmooth t).congr_of_eventuallyEq ?_
  filter_upwards [eventually_chiOf_eq_chiSmooth t] with s hs
  exact hs


lemma fg_f_ell {s : Fin 6 → ℝ} {chi : ℝ} (hα : 0 < alphaOf s) :
    fg_f s chi =
      1 - (1 - Real.cos (Real.sqrt (alphaOf s) * chi)) /
        (alphaOf s * rnorm s) := by
  unfold fg_f
  have hf := chiSq_mul_stumpffC (χ := chi) hα
  have hα0 : alphaOf s ≠ 0 := hα.ne'
  have : chi ^ 2 / rnorm s * stumpffC (alphaOf s * chi ^ 2)
      = (1 - Real.cos (Real.sqrt (alphaOf s) * chi)) / (alphaOf s * rnorm s) := by
    calc
      chi ^ 2 / rnorm s * stumpffC (alphaOf s * chi ^ 2)
          = (chi ^ 2 * stumpffC (alphaOf s * chi ^ 2)) / rnorm s := by ring
      _ = ((1 - Real.cos (Real.sqrt (alphaOf s) * chi)) / alphaOf s) / rnorm s := by
            rw [hf]
      _ = (1 - Real.cos (Real.sqrt (alphaOf s) * chi)) / (alphaOf s * rnorm s) := by
            field_simp [hα0]
  rw [this]

lemma fg_g_ell {s : Fin 6 → ℝ} {t chi : ℝ} (hα : 0 < alphaOf s) :
    fg_g s t chi =
      t - (chi / alphaOf s
        - Real.sin (Real.sqrt (alphaOf s) * chi)
          / (alphaOf s * Real.sqrt (alphaOf s))) := by
  unfold fg_g
  rw [chiCube_mul_stumpffS (χ := chi) hα]

lemma eventually_alphaOf_pos_prod (chi0 : ℝ) :
    ∀ᶠ v : (Fin 6 → ℝ) × ℝ in 𝓝 (sStar, chi0), 0 < alphaOf v.1 := by
  have hαpos : 0 < alphaOf sStar := by rw [alphaOf_sStar]; norm_num
  have : Tendsto (fun v : (Fin 6 → ℝ) × ℝ => alphaOf v.1)
      (𝓝 (sStar, chi0)) (𝓝 (alphaOf sStar)) :=
    continuousAt_alphaOf_sStar.tendsto.comp (continuous_fst.tendsto (sStar, chi0))
  exact this.eventually (Ioi_mem_nhds hαpos)

lemma contDiffAt_fg_f_unc (chi0 : ℝ) :
    ContDiffAt ℝ ⊤ (fun p : (Fin 6 → ℝ) × ℝ => fg_f p.1 p.2)
      (sStar, chi0) := by
  have hαpos : 0 < alphaOf sStar := by rw [alphaOf_sStar]; norm_num
  have hr : rnorm sStar ≠ 0 := rnorm_sStar_ne
  have ha := (contDiffAt_alphaOf' hr).comp (sStar, chi0)
    (contDiff_fst.contDiffAt (x := (sStar, chi0)))
  have hn := (contDiffAt_rnorm hr).comp (sStar, chi0)
    (contDiff_fst.contDiffAt (x := (sStar, chi0)))
  have hchi : ContDiffAt ℝ ⊤ (fun v : (Fin 6 → ℝ) × ℝ => v.2)
      (sStar, chi0) := contDiff_snd.contDiffAt
  have hsqrt := (Real.contDiffAt_sqrt hαpos.ne').comp (sStar, chi0) ha
  have hωchi := hsqrt.mul hchi
  have hnum := (contDiffAt_const (c := (1 : ℝ))).sub hωchi.cos
  have hden := ha.mul hn
  have hdiv := hnum.div hden (by
    change alphaOf sStar * rnorm sStar ≠ 0
    rw [alphaOf_sStar, rnorm_sStar]; norm_num)
  have hell := (contDiffAt_const (c := (1 : ℝ))).sub hdiv
  refine hell.congr_of_eventuallyEq ?_
  filter_upwards [eventually_alphaOf_pos_prod chi0] with v hv
  exact fg_f_ell hv

lemma contDiffAt_fg_g_unc (t chi0 : ℝ) :
    ContDiffAt ℝ ⊤ (fun p : (Fin 6 → ℝ) × ℝ => fg_g p.1 t p.2)
      (sStar, chi0) := by
  have hαpos : 0 < alphaOf sStar := by rw [alphaOf_sStar]; norm_num
  have hr : rnorm sStar ≠ 0 := rnorm_sStar_ne
  have ha := (contDiffAt_alphaOf' hr).comp (sStar, chi0)
    (contDiff_fst.contDiffAt (x := (sStar, chi0)))
  have hchi : ContDiffAt ℝ ⊤ (fun v : (Fin 6 → ℝ) × ℝ => v.2)
      (sStar, chi0) := contDiff_snd.contDiffAt
  have hsqrt := (Real.contDiffAt_sqrt hαpos.ne').comp (sStar, chi0) ha
  have hωchi := hsqrt.mul hchi
  have hden2 := ha.mul hsqrt
  have hα0 : alphaOf sStar ≠ 0 := by rw [alphaOf_sStar]; norm_num
  have hω0 : Real.sqrt (alphaOf sStar) ≠ 0 :=
    Real.sqrt_ne_zero'.2 (by rw [alphaOf_sStar]; norm_num)
  have hfrac2 := hωchi.sin.div hden2 (mul_ne_zero hα0 hω0)
  have hfrac1 := hchi.div ha hα0
  have hell := (contDiffAt_const (c := t)).sub (hfrac1.sub hfrac2)
  refine hell.congr_of_eventuallyEq ?_
  filter_upwards [eventually_alphaOf_pos_prod chi0] with v hv
  exact fg_g_ell (t := t) (chi := v.2) hv

lemma contDiffAt_fg_f_chiOf (t : ℝ) :
    ContDiffAt ℝ 2 (fun s => fg_f s (chiOf s t)) sStar := by
  have hunc : ContDiffAt ℝ 2 (fun p : (Fin 6 → ℝ) × ℝ => fg_f p.1 p.2)
      (sStar, 2 * t / 5) :=
    (contDiffAt_fg_f_unc (2 * t / 5)).of_le (by exact le_top)
  have hpair : ContDiffAt ℝ 2 (fun s => (s, chiOf s t)) sStar :=
    contDiffAt_id.prodMk (contDiffAt_chiOf t)
  have hunc' : ContDiffAt ℝ 2 (fun p : (Fin 6 → ℝ) × ℝ => fg_f p.1 p.2)
      (sStar, chiOf sStar t) := by
    simpa [chiOf_sStar] using hunc
  change ContDiffAt ℝ 2 ((fun p : (Fin 6 → ℝ) × ℝ => fg_f p.1 p.2) ∘ fun s => (s, chiOf s t)) sStar
  exact hunc'.comp sStar hpair

lemma contDiffAt_fg_g_chiOf (t : ℝ) :
    ContDiffAt ℝ 2 (fun s => fg_g s t (chiOf s t)) sStar := by
  have hunc : ContDiffAt ℝ 2 (fun p : (Fin 6 → ℝ) × ℝ => fg_g p.1 t p.2)
      (sStar, 2 * t / 5) :=
    (contDiffAt_fg_g_unc t (2 * t / 5)).of_le (by exact le_top)
  have hpair : ContDiffAt ℝ 2 (fun s => (s, chiOf s t)) sStar :=
    contDiffAt_id.prodMk (contDiffAt_chiOf t)
  have hunc' : ContDiffAt ℝ 2 (fun p : (Fin 6 → ℝ) × ℝ => fg_g p.1 t p.2)
      (sStar, chiOf sStar t) := by
    simpa [chiOf_sStar] using hunc
  change ContDiffAt ℝ 2 ((fun p : (Fin 6 → ℝ) × ℝ => fg_g p.1 t p.2) ∘ fun s => (s, chiOf s t)) sStar
  exact hunc'.comp sStar hpair

lemma contDiffAt_keplerIC (t : ℝ) :
    ContDiffAt ℝ 2 (fun s => keplerIC s t) sStar := by
  have hf := contDiffAt_fg_f_chiOf t
  have hg := contDiffAt_fg_g_chiOf t
  have hp : ContDiffAt ℝ 2 statePos sStar :=
    (contDiff_statePos.contDiffAt (x := sStar)).of_le (by exact le_top)
  have hv : ContDiffAt ℝ 2 stateVel sStar :=
    (contDiff_stateVel.contDiffAt (x := sStar)).of_le (by exact le_top)
  have h1 := hf.smul hp
  have h2 := hg.smul hv
  refine (h1.add h2).congr_of_eventuallyEq ?_
  exact Eventually.of_forall fun s => by simp [keplerIC]

lemma keplerIC_sStar_obs_ne (t : ℝ) :
    keplerIC sStar t ≠ obs t := by
  intro h
  have hx := keplerIC_sStar t
  have : circular (5 / 2) (Real.sqrt (8 / 125)) 0 t = circular 1 1 0 t := by
    simpa [obs, hx] using h
  have hL : ‖circular (5 / 2) (Real.sqrt (8 / 125)) 0 t‖ = (5 / 2 : ℝ) :=
    circular_norm _ _ _ _ (by norm_num)
  have hR : ‖circular 1 1 0 t‖ = (1 : ℝ) :=
    circular_norm _ _ _ _ (by norm_num)
  have : (5 / 2 : ℝ) = 1 := by rw [← hL, this, hR]
  norm_num at this

lemma contDiffAt_los_keplerIC (t : ℝ) :
    ContDiffAt ℝ 2 (fun s => los obs (keplerIC s) t) sStar := by
  have hx := contDiffAt_keplerIC t
  have hconst : ContDiffAt ℝ 2 (fun _ : Fin 6 → ℝ => obs t) sStar :=
    (contDiff_const (c := obs t)).contDiffAt.of_le (by exact le_top)
  have hsub : ContDiffAt ℝ 2 (fun s => keplerIC s t - obs t) sStar :=
    hx.sub hconst
  have hne : keplerIC sStar t - obs t ≠ 0 :=
    sub_ne_zero.mpr (keplerIC_sStar_obs_ne t)
  have hsq : ContDiffAt ℝ 2 (fun s => ‖keplerIC s t - obs t‖ ^ 2) sStar :=
    hsub.norm_sq ℝ
  have hnz : ‖keplerIC sStar t - obs t‖ ^ 2 ≠ 0 :=
    pow_ne_zero 2 (norm_ne_zero_iff.mpr hne)
  have hsqrt : ContDiffAt ℝ 2
      (fun s => Real.sqrt (‖keplerIC s t - obs t‖ ^ 2)) sStar :=
    hsq.sqrt hnz
  have hnorm : ContDiffAt ℝ 2 (fun s => ‖keplerIC s t - obs t‖) sStar := by
    refine hsqrt.congr_of_eventuallyEq ?_
    exact Eventually.of_forall fun s =>
      (Real.sqrt_sq (norm_nonneg (keplerIC s t - obs t))).symm
  have hinv : ContDiffAt ℝ 2 (fun s => ‖keplerIC s t - obs t‖⁻¹) sStar :=
    hnorm.inv (norm_ne_zero_iff.mpr hne)
  refine (hinv.smul hsub).congr_of_eventuallyEq ?_
  exact Eventually.of_forall fun s => by simp [los]

lemma contDiffAt_secondDiff_los (h : ℝ) :
    ContDiffAt ℝ 2
      (fun s => secondDiff (fun t => los obs (keplerIC s) t) h) sStar := by
  have h0 := contDiffAt_los_keplerIC 0
  have hh := contDiffAt_los_keplerIC h
  have h2 := contDiffAt_los_keplerIC (2 * h)
  have hsmul : ContDiffAt ℝ 2 (fun s => (2 : ℝ) • los obs (keplerIC s) h) sStar :=
    (contDiffAt_const (c := (2 : ℝ))).smul hh
  refine ((h0.sub hsmul).add h2).congr_of_eventuallyEq ?_
  exact Eventually.of_forall fun s => by simp [secondDiff]

lemma contDiff_sdPairCoord :
    ContDiff ℝ ⊤ (fun w : Vec × Vec => sdPairCoord w.1 w.2) := by
  refine contDiff_pi.2 fun i => ?_
  fin_cases i
  · exact (contDiff_ofLp_coord 0).comp contDiff_fst
  · exact (contDiff_ofLp_coord 1).comp contDiff_fst
  · exact (contDiff_ofLp_coord 2).comp contDiff_fst
  · exact (contDiff_ofLp_coord 0).comp contDiff_snd
  · exact (contDiff_ofLp_coord 1).comp contDiff_snd
  · exact (contDiff_ofLp_coord 2).comp contDiff_snd

lemma contDiffAt_sdCart : ContDiffAt ℝ 2 sdCart sStar := by
  have h1 := contDiffAt_secondDiff_los hSD1
  have h2 := contDiffAt_secondDiff_los hSD2
  have hpair := h1.prodMk h2
  have hsd : ContDiffAt ℝ 2 (fun w : Vec × Vec => sdPairCoord w.1 w.2)
      (secondDiff (fun t => los obs (keplerIC sStar) t) hSD1,
        secondDiff (fun t => los obs (keplerIC sStar) t) hSD2) :=
    (contDiff_sdPairCoord.contDiffAt).of_le (by exact le_top)
  refine (hsd.comp sStar hpair).congr_of_eventuallyEq ?_
  exact Eventually.of_forall fun s => by simp [sdCart]

lemma hasFDerivAt_sdCart :
    HasFDerivAt sdCart (fderiv ℝ sdCart sStar) sStar :=
  (contDiffAt_sdCart.differentiableAt (by decide)).hasFDerivAt

lemma hasFDerivAt_los_keplerIC (t : ℝ) :
    HasFDerivAt (fun s => los obs (keplerIC s) t)
      (fderiv ℝ (fun s => los obs (keplerIC s) t) sStar) sStar :=
  ((contDiffAt_los_keplerIC t).differentiableAt (by decide)).hasFDerivAt

lemma hasFDerivAt_secondDiff_los (h : ℝ) :
    HasFDerivAt (fun s => secondDiff (fun t => los obs (keplerIC s) t) h)
      (fderiv ℝ (fun s => secondDiff (fun t => los obs (keplerIC s) t) h) sStar)
      sStar :=
  ((contDiffAt_secondDiff_los h).differentiableAt (by decide)).hasFDerivAt

lemma fderiv_secondDiff_los (h : ℝ) (v : Fin 6 → ℝ) :
    fderiv ℝ (fun s => secondDiff (fun t => los obs (keplerIC s) t) h) sStar v =
      secondDiff (fun t => fderiv ℝ (fun s => los obs (keplerIC s) t) sStar v) h := by
  have h0 := hasFDerivAt_los_keplerIC 0
  have hh := hasFDerivAt_los_keplerIC h
  have h2 := hasFDerivAt_los_keplerIC (2 * h)
  have hsmul : HasFDerivAt (fun s => (2 : ℝ) • los obs (keplerIC s) h)
      ((2 : ℝ) • fderiv ℝ (fun s => los obs (keplerIC s) h) sStar) sStar :=
    hh.const_smul (2 : ℝ)
  have hsum := (h0.sub hsmul).add h2
  have hCLM :
      fderiv ℝ (fun s => secondDiff (fun t => los obs (keplerIC s) t) h) sStar
        = fderiv ℝ (fun s => los obs (keplerIC s) 0) sStar
            - (2 : ℝ) • fderiv ℝ (fun s => los obs (keplerIC s) h) sStar
            + fderiv ℝ (fun s => los obs (keplerIC s) (2 * h)) sStar :=
    (hasFDerivAt_secondDiff_los h).unique
      (hsum.congr_of_eventuallyEq (Eventually.of_forall fun _ => by simp [secondDiff]))
  rw [hCLM]
  simp [secondDiff]

def clm_ofLp (i : Fin 3) : Vec →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) i).comp
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).toContinuousLinearMap

lemma clm_ofLp_apply (i : Fin 3) (w : Vec) : clm_ofLp i w = w.ofLp i := rfl

lemma fderiv_ofLp_comp {f : (Fin 6 → ℝ) → Vec}
    (hf : HasFDerivAt f (fderiv ℝ f sStar) sStar) (i : Fin 3) (v : Fin 6 → ℝ) :
    fderiv ℝ (fun s => (f s).ofLp i) sStar v = (fderiv ℝ f sStar v).ofLp i := by
  have hL : HasFDerivAt (fun w : Vec => w.ofLp i) (clm_ofLp i) (f sStar) :=
    (clm_ofLp i).hasFDerivAt
  have hcomp := hL.comp sStar hf
  have heq : (fun s => (f s).ofLp i) = (fun w : Vec => w.ofLp i) ∘ f := rfl
  rw [heq, hcomp.fderiv]
  simp [ContinuousLinearMap.comp_apply, clm_ofLp_apply]

lemma fderiv_eval_coord {f : (Fin 6 → ℝ) → (Fin 6 → ℝ)}
    (hf : HasFDerivAt f (fderiv ℝ f sStar) sStar) (i : Fin 6) (v : Fin 6 → ℝ) :
    fderiv ℝ f sStar v i = fderiv ℝ (fun s => f s i) sStar v := by
  have hproj : HasFDerivAt (fun y : Fin 6 → ℝ => y i)
      (ContinuousLinearMap.proj i) (f sStar) :=
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 6 => ℝ) i).hasFDerivAt
  have hcomp := hproj.comp sStar hf
  have heq : (fun s => f s i) = (fun y : Fin 6 → ℝ => y i) ∘ f := rfl
  rw [heq, hcomp.fderiv]
  simp [ContinuousLinearMap.comp_apply]

lemma fderiv_sdCart_apply (v : Fin 6 → ℝ) :
    fderiv ℝ sdCart sStar v =
      sdPairCoord
        (secondDiff (fun t => fderiv ℝ (fun s => los obs (keplerIC s) t) sStar v) hSD1)
        (secondDiff (fun t => fderiv ℝ (fun s => los obs (keplerIC s) t) sStar v) hSD2) := by
  have h1 := hasFDerivAt_secondDiff_los hSD1
  have h2 := hasFDerivAt_secondDiff_los hSD2
  have hsd := hasFDerivAt_sdCart
  have hcoord : ∀ i : Fin 6,
      fderiv ℝ sdCart sStar v i = fderiv ℝ (fun s => sdCart s i) sStar v :=
    fun i => fderiv_eval_coord hsd i v
  ext i
  rw [hcoord]
  have hA0 : fderiv ℝ (fun s => sdCart s 0) sStar =
      fderiv ℝ (fun s =>
        (secondDiff (fun t => los obs (keplerIC s) t) hSD1).ofLp 0) sStar :=
    Filter.EventuallyEq.fderiv_eq (Eventually.of_forall fun s => by simp [sdCart, sdPairCoord])
  have hA1 : fderiv ℝ (fun s => sdCart s 1) sStar =
      fderiv ℝ (fun s =>
        (secondDiff (fun t => los obs (keplerIC s) t) hSD1).ofLp 1) sStar :=
    Filter.EventuallyEq.fderiv_eq (Eventually.of_forall fun s => by simp [sdCart, sdPairCoord])
  have hA2 : fderiv ℝ (fun s => sdCart s 2) sStar =
      fderiv ℝ (fun s =>
        (secondDiff (fun t => los obs (keplerIC s) t) hSD1).ofLp 2) sStar :=
    Filter.EventuallyEq.fderiv_eq (Eventually.of_forall fun s => by simp [sdCart, sdPairCoord])
  have hA3 : fderiv ℝ (fun s => sdCart s 3) sStar =
      fderiv ℝ (fun s =>
        (secondDiff (fun t => los obs (keplerIC s) t) hSD2).ofLp 0) sStar :=
    Filter.EventuallyEq.fderiv_eq (Eventually.of_forall fun s => by simp [sdCart, sdPairCoord])
  have hA4 : fderiv ℝ (fun s => sdCart s 4) sStar =
      fderiv ℝ (fun s =>
        (secondDiff (fun t => los obs (keplerIC s) t) hSD2).ofLp 1) sStar :=
    Filter.EventuallyEq.fderiv_eq (Eventually.of_forall fun s => by simp [sdCart, sdPairCoord])
  have hA5 : fderiv ℝ (fun s => sdCart s 5) sStar =
      fderiv ℝ (fun s =>
        (secondDiff (fun t => los obs (keplerIC s) t) hSD2).ofLp 2) sStar :=
    Filter.EventuallyEq.fderiv_eq (Eventually.of_forall fun s => by simp [sdCart, sdPairCoord])
  have i0 : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 := by
    fin_cases i <;> simp
  rcases i0 with rfl | rfl | rfl | rfl | rfl | rfl
  · rw [hA0, fderiv_ofLp_comp h1 0 v, fderiv_secondDiff_los]; simp [sdPairCoord]
  · rw [hA1, fderiv_ofLp_comp h1 1 v, fderiv_secondDiff_los]; simp [sdPairCoord]
  · rw [hA2, fderiv_ofLp_comp h1 2 v, fderiv_secondDiff_los]; simp [sdPairCoord]
  · rw [hA3, fderiv_ofLp_comp h2 0 v, fderiv_secondDiff_los]; simp [sdPairCoord]
  · rw [hA4, fderiv_ofLp_comp h2 1 v, fderiv_secondDiff_los]; simp [sdPairCoord]
  · rw [hA5, fderiv_ofLp_comp h2 2 v, fderiv_secondDiff_los]; simp [sdPairCoord]

lemma sigmaOf_lineJet2 (t : ℝ) : sigmaOf (lineJet 2 t) = 0 :=
  vecDot_lineJet2 t

lemma velNormSq_lineJet2 (t : ℝ) : ‖stateVel (lineJet 2 t)‖ ^ 2 = 2 / 5 := by
  rw [stateVel_lineJet2, ofCoords_norm]
  have hnn : (0 : ℝ) ≤ 0 ^ 2 + (Real.sqrt 10 / 5) ^ 2 + 0 ^ 2 := by positivity
  rw [Real.sq_sqrt hnn]
  field_simp
  rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 10)]
  norm_num

lemma alphaOf_lineJet2 (t : ℝ) :
    alphaOf (lineJet 2 t) = 2 / Real.sqrt ((5 / 2) ^ 2 + t ^ 2) - 2 / 5 := by
  simp [alphaOf, rnorm_lineJet2, velNormSq_lineJet2]

lemma hasDerivAt_alphaOf_lineJet2 :
    HasDerivAt (fun t => alphaOf (lineJet 2 t)) 0 0 := by
  have hinv : HasDerivAt (fun t => (rnorm (lineJet 2 t))⁻¹) 0 0 :=
    hasDerivAt_rnorm_inv_lineJet2
  have h2 : HasDerivAt (fun t => (2 : ℝ) * (rnorm (lineJet 2 t))⁻¹) 0 0 :=
    (hinv.const_mul (2 : ℝ)).congr_deriv (by simp)
  have h := h2.sub_const (2 / 5 : ℝ)
  refine (h.congr_of_eventuallyEq (Eventually.of_forall fun t => ?_)).congr_deriv (by ring)
  simp [alphaOf, rnorm_lineJet2, velNormSq_lineJet2]
  field_simp

lemma eventually_univF_chiOf (t : ℝ) :
    ∀ᶠ s in 𝓝 sStar, univF s (chiOf s t) = t := by
  filter_upwards [eventually_chiOf_eq_chiSmooth t, eventually_univF_chiSmooth t]
    with s hs hsm
  rw [hs, hsm]

def eZ : Vec := ofCoords 0 0 1

def nStar : ℝ := Real.sqrt (8 / 125)

lemma nStar_pos : 0 < nStar := Real.sqrt_pos.2 (by norm_num)

lemma nStar_ne : nStar ≠ 0 := nStar_pos.ne'

lemma hasDerivAt_even_zero {f : ℝ → ℝ} {f' : ℝ}
    (hf : HasDerivAt f f' 0) (heven : ∀ ε, f (-ε) = f ε) : f' = 0 := by
  have hneg : HasDerivAt (fun ε : ℝ => -ε) (-1 : ℝ) 0 := hasDerivAt_neg 0
  have hf0 : HasDerivAt f f' (-(0 : ℝ)) := by
    convert hf
    simp
  have hcomp : HasDerivAt (fun ε => f (-ε)) (f' * (-1)) 0 := hf0.comp 0 hneg
  have hcomp' : HasDerivAt (fun ε => f (-ε)) (-f') 0 :=
    hcomp.congr_deriv (by ring)
  have : HasDerivAt f (-f') 0 :=
    hcomp'.congr_of_eventuallyEq (Eventually.of_forall fun ε => (heven ε).symm)
  linarith [hf.unique this]

lemma rnorm_lineJet2_even (ε : ℝ) :
    rnorm (lineJet 2 (-ε)) = rnorm (lineJet 2 ε) := by
  simp [rnorm_lineJet2]

lemma velNormSq_lineJet5 (ε : ℝ) :
    ‖stateVel (lineJet 5 ε)‖ ^ 2 = 2 / 5 + ε ^ 2 := by
  rw [stateVel_lineJet5, ofCoords_norm]
  have hnn : (0 : ℝ) ≤ 0 ^ 2 + (Real.sqrt 10 / 5) ^ 2 + ε ^ 2 := by positivity
  rw [Real.sq_sqrt hnn]
  have hs : (Real.sqrt 10 / 5) ^ 2 = 2 / 5 := by
    field_simp
    rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 10)]
    norm_num
  rw [hs]
  ring

lemma alphaOf_lineJet5 (ε : ℝ) : alphaOf (lineJet 5 ε) = 2 / 5 - ε ^ 2 := by
  simp [alphaOf, rnorm_lineJet5, velNormSq_lineJet5]
  ring

lemma sigmaOf_lineJet5 (ε : ℝ) : sigmaOf (lineJet 5 ε) = 0 :=
  vecDot_lineJet5 ε

lemma univF_lineJet2_even (χ ε : ℝ) :
    univF (lineJet 2 (-ε)) χ = univF (lineJet 2 ε) χ := by
  simp [univF, alphaOf_lineJet2, rnorm_lineJet2, sigmaOf_lineJet2]

lemma univF_lineJet5_even (χ ε : ℝ) :
    univF (lineJet 5 (-ε)) χ = univF (lineJet 5 ε) χ := by
  simp [univF, alphaOf_lineJet5, rnorm_lineJet5, sigmaOf_lineJet5]

lemma hasDerivAt_pair_lineJet_const (j : Fin 6) (χ : ℝ) (ε : ℝ) :
    HasDerivAt (fun δ => (lineJet j δ, χ)) (Pi.single j (1 : ℝ), (0 : ℝ)) ε := by
  exact (hasDerivAt_lineJet j ε).prodMk (hasDerivAt_const ε χ)

lemma differentiableAt_univF_lineJet (j : Fin 6) (χ : ℝ) :
    DifferentiableAt ℝ (fun ε => univF (lineJet j ε) χ) 0 := by
  have hU : HasFDerivAt (Function.uncurry univF)
      (fderiv ℝ (Function.uncurry univF) (sStar, χ)) (sStar, χ) :=
    hasFDerivAt_uncurry_univF χ
  have hp := hasDerivAt_pair_lineJet_const j χ 0
  have hU' : HasFDerivAt (Function.uncurry univF)
      (fderiv ℝ (Function.uncurry univF) (lineJet j 0, χ)) (lineJet j 0, χ) := by
    rw [lineJet_zero]; exact hU
  exact (hU'.comp_hasDerivAt 0 hp).differentiableAt

lemma hasDerivAt_univF_lineJet2_fixed (χ : ℝ) :
    HasDerivAt (fun ε => univF (lineJet 2 ε) χ) 0 0 := by
  have hf := (differentiableAt_univF_lineJet 2 χ).hasDerivAt
  exact hf.congr_deriv (hasDerivAt_even_zero hf (univF_lineJet2_even χ))

lemma hasDerivAt_univF_lineJet5_fixed (χ : ℝ) :
    HasDerivAt (fun ε => univF (lineJet 5 ε) χ) 0 0 := by
  have hf := (differentiableAt_univF_lineJet 5 χ).hasDerivAt
  exact hf.congr_deriv (hasDerivAt_even_zero hf (univF_lineJet5_even χ))

lemma hasFDerivAt_keplerIC (t : ℝ) :
    HasFDerivAt (fun s => keplerIC s t)
      (fderiv ℝ (fun s => keplerIC s t) sStar) sStar :=
  ((contDiffAt_keplerIC t).differentiableAt (by decide)).hasFDerivAt

lemma hasDerivAt_chiOf_lineJet (j : Fin 6) (t : ℝ) :
    HasDerivAt (fun ε => chiOf (lineJet j ε) t)
      (fderiv ℝ (fun s => chiOf s t) sStar (Pi.single j 1)) 0 := by
  have hf : HasFDerivAt (fun s => chiOf s t)
      (fderiv ℝ (fun s => chiOf s t) sStar) (lineJet j 0) := by
    rw [lineJet_zero]
    exact ((contDiffAt_chiOf t).differentiableAt (by decide)).hasFDerivAt
  exact hf.comp_hasDerivAt 0 (hasDerivAt_lineJet j 0)

lemma tendsto_lineJet (j : Fin 6) : Tendsto (lineJet j) (𝓝 0) (𝓝 sStar) := by
  simpa [lineJet_zero] using (hasDerivAt_lineJet j 0).continuousAt.tendsto

lemma univF_fderiv_inr (χ0 c : ℝ) :
    fderiv ℝ (Function.uncurry univF) (sStar, χ0) (0, c) = (5 / 2) * c := by
  have := congrArg (fun L : ℝ →L[ℝ] ℝ => L c) (fderiv_univF_comp_inr χ0)
  have h : fderiv ℝ (Function.uncurry univF) (sStar, χ0) (0, c) = c * (5 / 2) := by
    simpa [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply,
      ContinuousLinearMap.toSpanSingleton_apply] using this
  rw [h, mul_comm]

lemma hasDerivAt_chiOf_axis {j : Fin 6} (t : ℝ)
    (hfixed : HasDerivAt (fun ε => univF (lineJet j ε) (2 * t / 5)) 0 0) :
    HasDerivAt (fun ε => chiOf (lineJet j ε) t) 0 0 := by
  have hχ := hasDerivAt_chiOf_lineJet j t
  have hF : HasFDerivAt (Function.uncurry univF)
      (fderiv ℝ (Function.uncurry univF) (sStar, 2 * t / 5))
      (sStar, 2 * t / 5) :=
    hasFDerivAt_uncurry_univF (2 * t / 5)
  set χ' := fderiv ℝ (fun s => chiOf s t) sStar (Pi.single j 1)
  have hpath : HasDerivAt (fun ε => (lineJet j ε, chiOf (lineJet j ε) t))
      (Pi.single j (1 : ℝ), χ') 0 :=
    (hasDerivAt_lineJet j 0).prodMk hχ
  have hFpath : HasFDerivAt (Function.uncurry univF)
      (fderiv ℝ (Function.uncurry univF) (lineJet j 0, chiOf (lineJet j 0) t))
      (lineJet j 0, chiOf (lineJet j 0) t) := by
    rw [lineJet_zero, chiOf_sStar]; exact hF
  have hcomp := hFpath.comp_hasDerivAt 0 hpath
  have hid : HasDerivAt (fun ε => univF (lineJet j ε) (chiOf (lineJet j ε) t)) 0 0 := by
    refine (hasDerivAt_const 0 t).congr_of_eventuallyEq ?_
    exact (tendsto_lineJet j).eventually (eventually_univF_chiOf t)
  have huniq := hcomp.unique hid
  have hpair0 := hasDerivAt_pair_lineJet_const j (2 * t / 5) 0
  have hF0 : HasFDerivAt (Function.uncurry univF)
      (fderiv ℝ (Function.uncurry univF) (lineJet j 0, 2 * t / 5))
      (lineJet j 0, 2 * t / 5) := by
    rw [lineJet_zero]; exact hF
  have hcomp0 := hF0.comp_hasDerivAt 0 hpair0
  have h0 := hcomp0.unique hfixed
  have hlin :
      fderiv ℝ (Function.uncurry univF) (sStar, 2 * t / 5) (Pi.single j 1, χ') = 0 := by
    have hpt : (lineJet j 0, chiOf (lineJet j 0) t) = (sStar, 2 * t / 5) := by
      simp [lineJet_zero, chiOf_sStar]
    simpa [hpt, χ'] using huniq
  have hlin0 :
      fderiv ℝ (Function.uncurry univF) (sStar, 2 * t / 5) (Pi.single j 1, (0 : ℝ)) = 0 := by
    have hpt : lineJet j 0 = sStar := lineJet_zero j
    simpa [hpt] using h0
  have hdiff :
      fderiv ℝ (Function.uncurry univF) (sStar, 2 * t / 5) (0, χ') = 0 := by
    have hL :=
      (map_sub (fderiv ℝ (Function.uncurry univF) (sStar, 2 * t / 5))
        (Pi.single j (1 : ℝ), χ') (Pi.single j (1 : ℝ), (0 : ℝ)))
    have hsub : (Pi.single j (1 : ℝ), χ') - (Pi.single j (1 : ℝ), (0 : ℝ))
        = ((0 : Fin 6 → ℝ), χ') := by
      apply Prod.ext
      · simp
      · simp
    rw [← hsub, hL, hlin, hlin0, sub_zero]
  have hmul : (5 / 2 : ℝ) * χ' = 0 := by
    rw [← univF_fderiv_inr (2 * t / 5) χ', hdiff]
  have hχ0 : χ' = 0 := by
    have h52 : (5 / 2 : ℝ) ≠ 0 := by norm_num
    exact (mul_eq_zero.mp hmul).resolve_left h52
  exact hχ.congr_deriv hχ0

lemma hasDerivAt_chiOf_lineJet2 (t : ℝ) :
    HasDerivAt (fun ε => chiOf (lineJet 2 ε) t) 0 0 :=
  hasDerivAt_chiOf_axis t (hasDerivAt_univF_lineJet2_fixed (2 * t / 5))

lemma hasDerivAt_chiOf_lineJet5 (t : ℝ) :
    HasDerivAt (fun ε => chiOf (lineJet 5 ε) t) 0 0 :=
  hasDerivAt_chiOf_axis t (hasDerivAt_univF_lineJet5_fixed (2 * t / 5))

lemma fg_f_lineJet2_even (χ ε : ℝ) :
    fg_f (lineJet 2 (-ε)) χ = fg_f (lineJet 2 ε) χ := by
  simp [fg_f, alphaOf_lineJet2, rnorm_lineJet2]

lemma fg_f_lineJet5_even (χ ε : ℝ) :
    fg_f (lineJet 5 (-ε)) χ = fg_f (lineJet 5 ε) χ := by
  simp [fg_f, alphaOf_lineJet5, rnorm_lineJet5]

lemma fg_g_lineJet2_even (t χ ε : ℝ) :
    fg_g (lineJet 2 (-ε)) t χ = fg_g (lineJet 2 ε) t χ := by
  simp [fg_g, alphaOf_lineJet2]

lemma fg_g_lineJet5_even (t χ ε : ℝ) :
    fg_g (lineJet 5 (-ε)) t χ = fg_g (lineJet 5 ε) t χ := by
  simp [fg_g, alphaOf_lineJet5]

lemma differentiableAt_fg_f_lineJet (j : Fin 6) (χ : ℝ) :
    DifferentiableAt ℝ (fun ε => fg_f (lineJet j ε) χ) 0 := by
  have hU : ContDiffAt ℝ ⊤ (fun p : (Fin 6 → ℝ) × ℝ => fg_f p.1 p.2) (sStar, χ) :=
    contDiffAt_fg_f_unc χ
  have hF : HasFDerivAt (fun p : (Fin 6 → ℝ) × ℝ => fg_f p.1 p.2)
      (fderiv ℝ (fun p : (Fin 6 → ℝ) × ℝ => fg_f p.1 p.2) (sStar, χ)) (sStar, χ) :=
    (hU.differentiableAt (by decide)).hasFDerivAt
  have hp := hasDerivAt_pair_lineJet_const j χ 0
  have hF' : HasFDerivAt (fun p : (Fin 6 → ℝ) × ℝ => fg_f p.1 p.2)
      (fderiv ℝ (fun p : (Fin 6 → ℝ) × ℝ => fg_f p.1 p.2) (lineJet j 0, χ))
      (lineJet j 0, χ) := by
    rw [lineJet_zero]; exact hF
  exact (hF'.comp_hasDerivAt 0 hp).differentiableAt

lemma differentiableAt_fg_g_lineJet (j : Fin 6) (t χ : ℝ) :
    DifferentiableAt ℝ (fun ε => fg_g (lineJet j ε) t χ) 0 := by
  have hU : ContDiffAt ℝ ⊤ (fun p : (Fin 6 → ℝ) × ℝ => fg_g p.1 t p.2) (sStar, χ) :=
    contDiffAt_fg_g_unc t χ
  have hF : HasFDerivAt (fun p : (Fin 6 → ℝ) × ℝ => fg_g p.1 t p.2)
      (fderiv ℝ (fun p : (Fin 6 → ℝ) × ℝ => fg_g p.1 t p.2) (sStar, χ)) (sStar, χ) :=
    (hU.differentiableAt (by decide)).hasFDerivAt
  have hp := hasDerivAt_pair_lineJet_const j χ 0
  have hF' : HasFDerivAt (fun p : (Fin 6 → ℝ) × ℝ => fg_g p.1 t p.2)
      (fderiv ℝ (fun p : (Fin 6 → ℝ) × ℝ => fg_g p.1 t p.2) (lineJet j 0, χ))
      (lineJet j 0, χ) := by
    rw [lineJet_zero]; exact hF
  exact (hF'.comp_hasDerivAt 0 hp).differentiableAt

lemma hasDerivAt_fg_f_lineJet2_fixed (χ : ℝ) :
    HasDerivAt (fun ε => fg_f (lineJet 2 ε) χ) 0 0 := by
  have hf := (differentiableAt_fg_f_lineJet 2 χ).hasDerivAt
  exact hf.congr_deriv (hasDerivAt_even_zero hf (fg_f_lineJet2_even χ))

lemma hasDerivAt_fg_f_lineJet5_fixed (χ : ℝ) :
    HasDerivAt (fun ε => fg_f (lineJet 5 ε) χ) 0 0 := by
  have hf := (differentiableAt_fg_f_lineJet 5 χ).hasDerivAt
  exact hf.congr_deriv (hasDerivAt_even_zero hf (fg_f_lineJet5_even χ))

lemma hasDerivAt_fg_g_lineJet2_fixed (t χ : ℝ) :
    HasDerivAt (fun ε => fg_g (lineJet 2 ε) t χ) 0 0 := by
  have hf := (differentiableAt_fg_g_lineJet 2 t χ).hasDerivAt
  exact hf.congr_deriv (hasDerivAt_even_zero hf (fg_g_lineJet2_even t χ))

lemma hasDerivAt_fg_g_lineJet5_fixed (t χ : ℝ) :
    HasDerivAt (fun ε => fg_g (lineJet 5 ε) t χ) 0 0 := by
  have hf := (differentiableAt_fg_g_lineJet 5 t χ).hasDerivAt
  exact hf.congr_deriv (hasDerivAt_even_zero hf (fg_g_lineJet5_even t χ))

lemma hasDerivAt_fg_f_chiOf_axis {j : Fin 6} (t : ℝ)
    (hχ : HasDerivAt (fun ε => chiOf (lineJet j ε) t) 0 0)
    (hfixed : HasDerivAt (fun ε => fg_f (lineJet j ε) (2 * t / 5)) 0 0) :
    HasDerivAt (fun ε => fg_f (lineJet j ε) (chiOf (lineJet j ε) t)) 0 0 := by
  have hU : ContDiffAt ℝ ⊤ (fun p : (Fin 6 → ℝ) × ℝ => fg_f p.1 p.2)
      (sStar, 2 * t / 5) :=
    contDiffAt_fg_f_unc (2 * t / 5)
  have hF : HasFDerivAt (fun p : (Fin 6 → ℝ) × ℝ => fg_f p.1 p.2)
      (fderiv ℝ (fun p : (Fin 6 → ℝ) × ℝ => fg_f p.1 p.2) (sStar, 2 * t / 5))
      (sStar, 2 * t / 5) :=
    (hU.differentiableAt (by decide)).hasFDerivAt
  have hpath : HasDerivAt (fun ε => (lineJet j ε, chiOf (lineJet j ε) t))
      (Pi.single j (1 : ℝ), (0 : ℝ)) 0 :=
    (hasDerivAt_lineJet j 0).prodMk hχ
  have hFpath : HasFDerivAt (fun p : (Fin 6 → ℝ) × ℝ => fg_f p.1 p.2)
      (fderiv ℝ (fun p : (Fin 6 → ℝ) × ℝ => fg_f p.1 p.2)
        (lineJet j 0, chiOf (lineJet j 0) t))
      (lineJet j 0, chiOf (lineJet j 0) t) := by
    rw [lineJet_zero, chiOf_sStar]; exact hF
  have hcomp := hFpath.comp_hasDerivAt 0 hpath
  have hpair0 := hasDerivAt_pair_lineJet_const j (2 * t / 5) 0
  have hF0 : HasFDerivAt (fun p : (Fin 6 → ℝ) × ℝ => fg_f p.1 p.2)
      (fderiv ℝ (fun p : (Fin 6 → ℝ) × ℝ => fg_f p.1 p.2) (lineJet j 0, 2 * t / 5))
      (lineJet j 0, 2 * t / 5) := by
    rw [lineJet_zero]; exact hF
  have hcomp0 := hF0.comp_hasDerivAt 0 hpair0
  have hpt : chiOf (lineJet j 0) t = 2 * t / 5 := by
    rw [lineJet_zero, chiOf_sStar]
  rw [hpt] at hcomp
  exact hcomp.congr_deriv (hcomp0.unique hfixed)

lemma hasDerivAt_fg_g_chiOf_axis {j : Fin 6} (t : ℝ)
    (hχ : HasDerivAt (fun ε => chiOf (lineJet j ε) t) 0 0)
    (hfixed : HasDerivAt (fun ε => fg_g (lineJet j ε) t (2 * t / 5)) 0 0) :
    HasDerivAt (fun ε => fg_g (lineJet j ε) t (chiOf (lineJet j ε) t)) 0 0 := by
  have hU : ContDiffAt ℝ ⊤ (fun p : (Fin 6 → ℝ) × ℝ => fg_g p.1 t p.2)
      (sStar, 2 * t / 5) :=
    contDiffAt_fg_g_unc t (2 * t / 5)
  have hF : HasFDerivAt (fun p : (Fin 6 → ℝ) × ℝ => fg_g p.1 t p.2)
      (fderiv ℝ (fun p : (Fin 6 → ℝ) × ℝ => fg_g p.1 t p.2) (sStar, 2 * t / 5))
      (sStar, 2 * t / 5) :=
    (hU.differentiableAt (by decide)).hasFDerivAt
  have hpath : HasDerivAt (fun ε => (lineJet j ε, chiOf (lineJet j ε) t))
      (Pi.single j (1 : ℝ), (0 : ℝ)) 0 :=
    (hasDerivAt_lineJet j 0).prodMk hχ
  have hFpath : HasFDerivAt (fun p : (Fin 6 → ℝ) × ℝ => fg_g p.1 t p.2)
      (fderiv ℝ (fun p : (Fin 6 → ℝ) × ℝ => fg_g p.1 t p.2)
        (lineJet j 0, chiOf (lineJet j 0) t))
      (lineJet j 0, chiOf (lineJet j 0) t) := by
    rw [lineJet_zero, chiOf_sStar]; exact hF
  have hcomp := hFpath.comp_hasDerivAt 0 hpath
  have hpair0 := hasDerivAt_pair_lineJet_const j (2 * t / 5) 0
  have hF0 : HasFDerivAt (fun p : (Fin 6 → ℝ) × ℝ => fg_g p.1 t p.2)
      (fderiv ℝ (fun p : (Fin 6 → ℝ) × ℝ => fg_g p.1 t p.2) (lineJet j 0, 2 * t / 5))
      (lineJet j 0, 2 * t / 5) := by
    rw [lineJet_zero]; exact hF
  have hcomp0 := hF0.comp_hasDerivAt 0 hpair0
  have hpt : chiOf (lineJet j 0) t = 2 * t / 5 := by
    rw [lineJet_zero, chiOf_sStar]
  rw [hpt] at hcomp
  exact hcomp.congr_deriv (hcomp0.unique hfixed)

lemma hasDerivAt_fg_f_chiOf_lineJet2 (t : ℝ) :
    HasDerivAt (fun ε => fg_f (lineJet 2 ε) (chiOf (lineJet 2 ε) t)) 0 0 :=
  hasDerivAt_fg_f_chiOf_axis t (hasDerivAt_chiOf_lineJet2 t)
    (hasDerivAt_fg_f_lineJet2_fixed (2 * t / 5))

lemma hasDerivAt_fg_f_chiOf_lineJet5 (t : ℝ) :
    HasDerivAt (fun ε => fg_f (lineJet 5 ε) (chiOf (lineJet 5 ε) t)) 0 0 :=
  hasDerivAt_fg_f_chiOf_axis t (hasDerivAt_chiOf_lineJet5 t)
    (hasDerivAt_fg_f_lineJet5_fixed (2 * t / 5))

lemma hasDerivAt_fg_g_chiOf_lineJet2 (t : ℝ) :
    HasDerivAt (fun ε => fg_g (lineJet 2 ε) t (chiOf (lineJet 2 ε) t)) 0 0 :=
  hasDerivAt_fg_g_chiOf_axis t (hasDerivAt_chiOf_lineJet2 t)
    (hasDerivAt_fg_g_lineJet2_fixed t (2 * t / 5))

lemma hasDerivAt_fg_g_chiOf_lineJet5 (t : ℝ) :
    HasDerivAt (fun ε => fg_g (lineJet 5 ε) t (chiOf (lineJet 5 ε) t)) 0 0 :=
  hasDerivAt_fg_g_chiOf_axis t (hasDerivAt_chiOf_lineJet5 t)
    (hasDerivAt_fg_g_lineJet5_fixed t (2 * t / 5))

lemma hasDerivAt_statePos_lineJet5 :
    HasDerivAt (fun ε => statePos (lineJet 5 ε)) (0 : Vec) 0 := by
  have h := hasDerivAt_const (0 : ℝ) (ofCoords (5 / 2) 0 0)
  exact h.congr_of_eventuallyEq (Eventually.of_forall statePos_lineJet5)

lemma hasDerivAt_stateVel_lineJet5 :
    HasDerivAt (fun ε => stateVel (lineJet 5 ε)) eZ 0 := by
  have h : HasDerivAt (fun ε => ofCoords 0 (Real.sqrt 10 / 5) ε) (ofCoords 0 0 1) 0 :=
    hasDerivAt_coord3 (hasDerivAt_const (0 : ℝ) (0 : ℝ))
      (hasDerivAt_const (0 : ℝ) (Real.sqrt 10 / 5)) (hasDerivAt_id (0 : ℝ))
  have heq : (fun ε => stateVel (lineJet 5 ε)) = fun ε => ofCoords 0 (Real.sqrt 10 / 5) ε :=
    funext stateVel_lineJet5
  rw [heq, eZ]
  exact h

lemma keplerIC_lineJet_apply (j : Fin 6) (ε t : ℝ) :
    keplerIC (lineJet j ε) t =
      fg_f (lineJet j ε) (chiOf (lineJet j ε) t) • statePos (lineJet j ε) +
        fg_g (lineJet j ε) t (chiOf (lineJet j ε) t) • stateVel (lineJet j ε) :=
  rfl

lemma hasDerivAt_keplerIC_lineJet2 (t : ℝ) :
    HasDerivAt (fun ε => keplerIC (lineJet 2 ε) t)
      (Real.cos (nStar * t) • eZ) 0 := by
  have hf := hasDerivAt_fg_f_chiOf_lineJet2 t
  have hg := hasDerivAt_fg_g_chiOf_lineJet2 t
  have hp := hasDerivAt_pos_lineJet2
  have hv := hasDerivAt_vel_lineJet2
  have hsum := (hf.smul hp).add (hg.smul hv)
  have hf0 : fg_f sStar (2 * t / 5) = Real.cos (nStar * t) := by
    rw [nStar, fg_f_sStar]
  have hder :
      (0 : ℝ) • statePos (lineJet 2 0) +
          fg_f (lineJet 2 0) (chiOf (lineJet 2 0) t) • ofCoords 0 0 1 +
          ((0 : ℝ) • stateVel (lineJet 2 0) +
            fg_g (lineJet 2 0) t (chiOf (lineJet 2 0) t) • (0 : Vec))
        = Real.cos (nStar * t) • eZ := by
    simp [lineJet_zero, chiOf_sStar, hf0, eZ]
  refine (hsum.congr_of_eventuallyEq
    (Eventually.of_forall fun ε => keplerIC_lineJet_apply 2 ε t)).congr_deriv ?_
  simpa [lineJet_zero, chiOf_sStar] using hder

lemma hasDerivAt_keplerIC_lineJet5 (t : ℝ) :
    HasDerivAt (fun ε => keplerIC (lineJet 5 ε) t)
      ((Real.sin (nStar * t) / nStar) • eZ) 0 := by
  have hf := hasDerivAt_fg_f_chiOf_lineJet5 t
  have hg := hasDerivAt_fg_g_chiOf_lineJet5 t
  have hp := hasDerivAt_statePos_lineJet5
  have hv := hasDerivAt_stateVel_lineJet5
  have hsum := (hf.smul hp).add (hg.smul hv)
  have hg0 : fg_g sStar t (2 * t / 5) = Real.sin (nStar * t) / nStar := by
    rw [nStar, fg_g_sStar]
  have hder :
      (0 : ℝ) • statePos (lineJet 5 0) +
          fg_f (lineJet 5 0) (chiOf (lineJet 5 0) t) • (0 : Vec) +
          ((0 : ℝ) • stateVel (lineJet 5 0) +
            fg_g (lineJet 5 0) t (chiOf (lineJet 5 0) t) • eZ)
        = (Real.sin (nStar * t) / nStar) • eZ := by
    simp [lineJet_zero, chiOf_sStar, hg0]
  refine (hsum.congr_of_eventuallyEq
    (Eventually.of_forall fun ε => keplerIC_lineJet_apply 5 ε t)).congr_deriv ?_
  simpa [lineJet_zero, chiOf_sStar] using hder

lemma fderiv_keplerIC_ez (t : ℝ) :
    fderiv ℝ (fun s => keplerIC s t) sStar (Pi.single 2 1)
      = Real.cos (nStar * t) • eZ := by
  have hf : HasFDerivAt (fun s => keplerIC s t)
      (fderiv ℝ (fun s => keplerIC s t) sStar) (lineJet 2 0) := by
    rw [lineJet_zero]; exact hasFDerivAt_keplerIC t
  exact (hf.comp_hasDerivAt 0 (hasDerivAt_lineJet 2 0)).unique
    (hasDerivAt_keplerIC_lineJet2 t)

lemma fderiv_keplerIC_evz (t : ℝ) :
    fderiv ℝ (fun s => keplerIC s t) sStar (Pi.single 5 1)
      = (Real.sin (nStar * t) / nStar) • eZ := by
  have hf : HasFDerivAt (fun s => keplerIC s t)
      (fderiv ℝ (fun s => keplerIC s t) sStar) (lineJet 5 0) := by
    rw [lineJet_zero]; exact hasFDerivAt_keplerIC t
  exact (hf.comp_hasDerivAt 0 (hasDerivAt_lineJet 5 0)).unique
    (hasDerivAt_keplerIC_lineJet5 t)

lemma ofCoords_ofLp2 (x y z : ℝ) : (ofCoords x y z).ofLp 2 = z := by
  simp [ofCoords, ofLp_ofCoords]

lemma eZ_ofLp : eZ.ofLp 0 = 0 ∧ eZ.ofLp 1 = 0 ∧ eZ.ofLp 2 = 1 := by
  simp [eZ, ofCoords_ofLp2, ofLp_ofCoords]

lemma circular_ofLp2 (R ω φ t : ℝ) : (circular R ω φ t).ofLp 2 = 0 := by
  simp [circular, ofCoords_ofLp2]

lemma obs_ofLp2 (t : ℝ) : (obs t).ofLp 2 = 0 := circular_ofLp2 _ _ _ _

lemma keplerIC_sStar_ofLp2 (t : ℝ) : (keplerIC sStar t).ofLp 2 = 0 := by
  rw [keplerIC_sStar, circular_ofLp2]

lemma keplerIC_apply_ofLp2 (s : Fin 6 → ℝ) (t : ℝ) :
    (keplerIC s t).ofLp 2 =
      fg_f s (chiOf s t) * s 2 + fg_g s t (chiOf s t) * s 5 := by
  simp [keplerIC, statePos, stateVel, ofCoords, PiLp.smul_apply, PiLp.add_apply,
    smul_eq_mul, ofLp_ofCoords]

lemma lineJet_coord (j : Fin 6) (ε : ℝ) (i : Fin 6) :
    lineJet j ε i = sStar i + if i = j then ε else 0 := by
  simp [lineJet, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply]

lemma lineJet_z_of_ne (j : Fin 6) (hj : j ≠ 2) (ε : ℝ) : lineJet j ε 2 = 0 := by
  rw [lineJet_coord]
  simp [sStar, hj.symm]

lemma lineJet_vz_of_ne (j : Fin 6) (hj : j ≠ 5) (ε : ℝ) : lineJet j ε 5 = 0 := by
  rw [lineJet_coord]
  simp [sStar, hj.symm]

lemma keplerIC_inplane_z (j : Fin 6) (hj2 : j ≠ 2) (hj5 : j ≠ 5) (ε t : ℝ) :
    (keplerIC (lineJet j ε) t).ofLp 2 = 0 := by
  rw [keplerIC_apply_ofLp2, lineJet_z_of_ne j hj2, lineJet_vz_of_ne j hj5]
  ring

lemma fderiv_keplerIC_inplane_z (j : Fin 6) (hj2 : j ≠ 2) (hj5 : j ≠ 5) (t : ℝ) :
    (fderiv ℝ (fun s => keplerIC s t) sStar (Pi.single j 1)).ofLp 2 = 0 := by
  have hf : HasFDerivAt (fun s => keplerIC s t)
      (fderiv ℝ (fun s => keplerIC s t) sStar) (lineJet j 0) := by
    rw [lineJet_zero]; exact hasFDerivAt_keplerIC t
  have hcomp := hf.comp_hasDerivAt 0 (hasDerivAt_lineJet j 0)
  have hz : HasDerivAt (fun ε => (keplerIC (lineJet j ε) t).ofLp 2) 0 0 := by
    have hconst : HasDerivAt (fun _ : ℝ => (0 : ℝ)) 0 0 := hasDerivAt_const _ _
    exact hconst.congr_of_eventuallyEq
      (Eventually.of_forall fun ε => keplerIC_inplane_z j hj2 hj5 ε t)
  have hL : HasFDerivAt (fun w : Vec => w.ofLp 2) (clm_ofLp 2)
      (keplerIC (lineJet j 0) t) :=
    (clm_ofLp 2).hasFDerivAt
  have hcoord := hL.comp_hasDerivAt 0 hcomp
  have : (fderiv ℝ (fun s => keplerIC s t) sStar (Pi.single j 1)).ofLp 2 = 0 :=
    hcoord.unique hz
  exact this

def rhoStar (t : ℝ) : ℝ := ‖keplerIC sStar t - obs t‖

lemma rhoStar_pos (t : ℝ) : 0 < rhoStar t :=
  norm_pos_iff.mpr (sub_ne_zero.mpr (keplerIC_sStar_obs_ne t))

lemma rhoStar_ne (t : ℝ) : rhoStar t ≠ 0 := (rhoStar_pos t).ne'

lemma kepler_obs_ofLp2 (t : ℝ) : (keplerIC sStar t - obs t).ofLp 2 = 0 := by
  simp [PiLp.sub_apply, keplerIC_sStar_ofLp2, obs_ofLp2]

lemma inner_kepler_obs_eZ (t : ℝ) :
    ⟪keplerIC sStar t - obs t, eZ⟫ = 0 := by
  rw [← vecDot_eq_inner]
  simp [vecDot, eZ, ofLp_ofCoords, Fin.sum_univ_three]
  simp [keplerIC_sStar_ofLp2, obs_ofLp2]

lemma hasDerivAt_kepler_obs_lineJet2 (t : ℝ) :
    HasDerivAt (fun ε => keplerIC (lineJet 2 ε) t - obs t)
      (Real.cos (nStar * t) • eZ) 0 :=
  (hasDerivAt_keplerIC_lineJet2 t).sub_const (obs t)

lemma hasDerivAt_kepler_obs_lineJet5 (t : ℝ) :
    HasDerivAt (fun ε => keplerIC (lineJet 5 ε) t - obs t)
      ((Real.sin (nStar * t) / nStar) • eZ) 0 :=
  (hasDerivAt_keplerIC_lineJet5 t).sub_const (obs t)

lemma hasDerivAt_norm_vec {f : ℝ → Vec} {f' : Vec} {x : ℝ}
    (hf : HasDerivAt f f' x) (hne : f x ≠ 0) :
    HasDerivAt (fun t => ‖f t‖) (⟪f x, f'⟫ / ‖f x‖) x := by
  have hne' : ‖f x‖ ≠ 0 := norm_ne_zero_iff.mpr hne
  have hsq' := hf.norm_sq
  have hpos : 0 < ‖f x‖ ^ 2 := sq_pos_of_ne_zero hne'
  have hsqrt : HasDerivAt (fun u : ℝ => Real.sqrt u)
      ((1 : ℝ) / (2 * Real.sqrt (‖f x‖ ^ 2))) (‖f x‖ ^ 2) :=
    Real.hasDerivAt_sqrt hpos.ne'
  have hcomp := hsqrt.comp x hsq'
  have hnn : 0 ≤ ‖f x‖ := norm_nonneg _
  refine (hcomp.congr_of_eventuallyEq (Eventually.of_forall fun t => ?_)).congr_deriv ?_
  · simpa using Real.sqrt_sq (norm_nonneg (f t))
  rw [Real.sqrt_sq hnn]
  ring

lemma hasDerivAt_rho_lineJet2 (t : ℝ) :
    HasDerivAt (fun ε => ‖keplerIC (lineJet 2 ε) t - obs t‖) 0 0 := by
  have hf := hasDerivAt_kepler_obs_lineJet2 t
  have hne : keplerIC (lineJet 2 0) t - obs t ≠ 0 := by
    rw [lineJet_zero]; exact sub_ne_zero.mpr (keplerIC_sStar_obs_ne t)
  have h := hasDerivAt_norm_vec hf hne
  have hin : ⟪keplerIC (lineJet 2 0) t - obs t, Real.cos (nStar * t) • eZ⟫ = 0 := by
    rw [lineJet_zero, inner_smul_right, inner_kepler_obs_eZ, mul_zero]
  exact h.congr_deriv (by simp [hin])

lemma hasDerivAt_rho_lineJet5 (t : ℝ) :
    HasDerivAt (fun ε => ‖keplerIC (lineJet 5 ε) t - obs t‖) 0 0 := by
  have hf := hasDerivAt_kepler_obs_lineJet5 t
  have hne : keplerIC (lineJet 5 0) t - obs t ≠ 0 := by
    rw [lineJet_zero]; exact sub_ne_zero.mpr (keplerIC_sStar_obs_ne t)
  have h := hasDerivAt_norm_vec hf hne
  have hin :
      ⟪keplerIC (lineJet 5 0) t - obs t, (Real.sin (nStar * t) / nStar) • eZ⟫ = 0 := by
    rw [lineJet_zero, inner_smul_right, inner_kepler_obs_eZ, mul_zero]
  exact h.congr_deriv (by simp [hin])

lemma los_kepler_apply (s : Fin 6 → ℝ) (t : ℝ) :
    los obs (keplerIC s) t =
      ‖keplerIC s t - obs t‖⁻¹ • (keplerIC s t - obs t) :=
  rfl

lemma hasDerivAt_los_lineJet2 (t : ℝ) :
    HasDerivAt (fun ε => los obs (keplerIC (lineJet 2 ε)) t)
      ((Real.cos (nStar * t) / rhoStar t) • eZ) 0 := by
  have hr := hasDerivAt_rho_lineJet2 t
  have hg := hasDerivAt_kepler_obs_lineJet2 t
  have hne : ‖keplerIC (lineJet 2 0) t - obs t‖ ≠ 0 := by
    rw [lineJet_zero]; exact rhoStar_ne t
  have hinv : HasDerivAt (fun ε => ‖keplerIC (lineJet 2 ε) t - obs t‖⁻¹) 0 0 := by
    have := hr.inv hne
    exact this.congr_deriv (by simp)
  have hsmul := hinv.smul hg
  have hval :
      (0 : ℝ) • (keplerIC (lineJet 2 0) t - obs t)
          + ‖keplerIC (lineJet 2 0) t - obs t‖⁻¹ • (Real.cos (nStar * t) • eZ)
        = (Real.cos (nStar * t) / rhoStar t) • eZ := by
    simp [lineJet_zero, rhoStar, smul_smul, div_eq_inv_mul]
  refine (hsmul.congr_of_eventuallyEq
    (Eventually.of_forall fun ε => los_kepler_apply (lineJet 2 ε) t)).congr_deriv ?_
  simpa using hval

lemma hasDerivAt_los_lineJet5 (t : ℝ) :
    HasDerivAt (fun ε => los obs (keplerIC (lineJet 5 ε)) t)
      (((Real.sin (nStar * t) / nStar) / rhoStar t) • eZ) 0 := by
  have hr := hasDerivAt_rho_lineJet5 t
  have hg := hasDerivAt_kepler_obs_lineJet5 t
  have hne : ‖keplerIC (lineJet 5 0) t - obs t‖ ≠ 0 := by
    rw [lineJet_zero]; exact rhoStar_ne t
  have hinv : HasDerivAt (fun ε => ‖keplerIC (lineJet 5 ε) t - obs t‖⁻¹) 0 0 := by
    have := hr.inv hne
    exact this.congr_deriv (by simp)
  have hsmul := hinv.smul hg
  have hval :
      (0 : ℝ) • (keplerIC (lineJet 5 0) t - obs t)
          + ‖keplerIC (lineJet 5 0) t - obs t‖⁻¹ •
            ((Real.sin (nStar * t) / nStar) • eZ)
        = (((Real.sin (nStar * t) / nStar) / rhoStar t) • eZ) := by
    simp [lineJet_zero, rhoStar, smul_smul, div_eq_inv_mul]
  refine (hsmul.congr_of_eventuallyEq
    (Eventually.of_forall fun ε => los_kepler_apply (lineJet 5 ε) t)).congr_deriv ?_
  simpa using hval

lemma fderiv_los_keplerIC_ez (t : ℝ) :
    fderiv ℝ (fun s => los obs (keplerIC s) t) sStar (Pi.single 2 1)
      = (Real.cos (nStar * t) / rhoStar t) • eZ := by
  have hf : HasFDerivAt (fun s => los obs (keplerIC s) t)
      (fderiv ℝ (fun s => los obs (keplerIC s) t) sStar) (lineJet 2 0) := by
    rw [lineJet_zero]; exact hasFDerivAt_los_keplerIC t
  exact (hf.comp_hasDerivAt 0 (hasDerivAt_lineJet 2 0)).unique
    (hasDerivAt_los_lineJet2 t)

lemma fderiv_los_keplerIC_evz (t : ℝ) :
    fderiv ℝ (fun s => los obs (keplerIC s) t) sStar (Pi.single 5 1)
      = ((Real.sin (nStar * t) / nStar) / rhoStar t) • eZ := by
  have hf : HasFDerivAt (fun s => los obs (keplerIC s) t)
      (fderiv ℝ (fun s => los obs (keplerIC s) t) sStar) (lineJet 5 0) := by
    rw [lineJet_zero]; exact hasFDerivAt_los_keplerIC t
  exact (hf.comp_hasDerivAt 0 (hasDerivAt_lineJet 5 0)).unique
    (hasDerivAt_los_lineJet5 t)

lemma secondDiff_smul_eZ (φ : ℝ → ℝ) (h : ℝ) :
    secondDiff (fun t => φ t • eZ) h = (φ 0 - 2 * φ h + φ (2 * h)) • eZ := by
  ext i
  simp [secondDiff, PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  ring

def phiZ (t : ℝ) : ℝ := Real.cos (nStar * t) / rhoStar t

def phiVz (t : ℝ) : ℝ := (Real.sin (nStar * t) / nStar) / rhoStar t

lemma fderiv_secondDiff_los_ez (h : ℝ) :
    secondDiff (fun t => fderiv ℝ (fun s => los obs (keplerIC s) t) sStar
      (Pi.single 2 1)) h
      = (phiZ 0 - 2 * phiZ h + phiZ (2 * h)) • eZ := by
  have heq : (fun t => fderiv ℝ (fun s => los obs (keplerIC s) t) sStar (Pi.single 2 1))
      = fun t => phiZ t • eZ :=
    funext fun t => by simp [fderiv_los_keplerIC_ez, phiZ]
  rw [heq, secondDiff_smul_eZ]

lemma fderiv_secondDiff_los_evz (h : ℝ) :
    secondDiff (fun t => fderiv ℝ (fun s => los obs (keplerIC s) t) sStar
      (Pi.single 5 1)) h
      = (phiVz 0 - 2 * phiVz h + phiVz (2 * h)) • eZ := by
  have heq : (fun t => fderiv ℝ (fun s => los obs (keplerIC s) t) sStar (Pi.single 5 1))
      = fun t => phiVz t • eZ :=
    funext fun t => by simp [fderiv_los_keplerIC_evz, phiVz]
  rw [heq, secondDiff_smul_eZ]

lemma sdPairCoord_smul_eZ (a b : ℝ) :
    sdPairCoord (a • eZ) (b • eZ) = ![0, 0, a, 0, 0, b] := by
  simp [sdPairCoord, eZ, ofLp_ofCoords, PiLp.smul_apply, smul_eq_mul]

lemma fderiv_sdCart_ez :
    fderiv ℝ sdCart sStar (Pi.single 2 1) =
      ![0, 0, phiZ 0 - 2 * phiZ hSD1 + phiZ (2 * hSD1),
        0, 0, phiZ 0 - 2 * phiZ hSD2 + phiZ (2 * hSD2)] := by
  rw [fderiv_sdCart_apply, fderiv_secondDiff_los_ez, fderiv_secondDiff_los_ez,
    sdPairCoord_smul_eZ]

lemma fderiv_sdCart_evz :
    fderiv ℝ sdCart sStar (Pi.single 5 1) =
      ![0, 0, phiVz 0 - 2 * phiVz hSD1 + phiVz (2 * hSD1),
        0, 0, phiVz 0 - 2 * phiVz hSD2 + phiVz (2 * hSD2)] := by
  rw [fderiv_sdCart_apply, fderiv_secondDiff_los_evz, fderiv_secondDiff_los_evz,
    sdPairCoord_smul_eZ]

def deltaPhi (φ : ℝ → ℝ) (h : ℝ) : ℝ := φ 0 - 2 * φ h + φ (2 * h)

lemma fderiv_sdCart_ez' :
    fderiv ℝ sdCart sStar (Pi.single 2 1) =
      ![0, 0, deltaPhi phiZ hSD1, 0, 0, deltaPhi phiZ hSD2] :=
  fderiv_sdCart_ez

lemma fderiv_sdCart_evz' :
    fderiv ℝ sdCart sStar (Pi.single 5 1) =
      ![0, 0, deltaPhi phiVz hSD1, 0, 0, deltaPhi phiVz hSD2] :=
  fderiv_sdCart_evz

def zBlk : Matrix (Fin 2) (Fin 2) ℝ :=
  !![deltaPhi phiZ hSD1, deltaPhi phiVz hSD1;
     deltaPhi phiZ hSD2, deltaPhi phiVz hSD2]

lemma zBlk_det_eq :
    zBlk.det = deltaPhi phiZ hSD1 * deltaPhi phiVz hSD2
      - deltaPhi phiVz hSD1 * deltaPhi phiZ hSD2 := by
  simp [zBlk, Matrix.det_fin_two]

lemma nStar_sq : nStar ^ 2 = 8 / 125 :=
  Real.sq_sqrt (by norm_num)

lemma nStar_gt_lo : (252 / 1000 : ℝ) < nStar := by
  have hsq : (252 / 1000 : ℝ) ^ 2 < nStar ^ 2 := by
    rw [nStar_sq]; norm_num
  exact lt_of_pow_lt_pow_left₀ 2 (le_of_lt nStar_pos) hsq

lemma nStar_lt_hi : nStar < (253 / 1000 : ℝ) := by
  have hsq : nStar ^ 2 < (253 / 1000 : ℝ) ^ 2 := by
    rw [nStar_sq]; norm_num
  exact lt_of_pow_lt_pow_left₀ 2 (by norm_num) hsq

lemma nStar_lt_one : nStar < 1 :=
  nStar_lt_hi.trans (by norm_num)

lemma circular_ofLp0 (R ω φ t : ℝ) :
    (circular R ω φ t).ofLp 0 = R * Real.cos (ω * t + φ) := by
  simp [circular, ofLp_ofCoords]

lemma circular_ofLp1 (R ω φ t : ℝ) :
    (circular R ω φ t).ofLp 1 = R * Real.sin (ω * t + φ) := by
  simp [circular, ofLp_ofCoords]

lemma keplerIC_sStar_ofLp01 (t : ℝ) :
    (keplerIC sStar t).ofLp 0 = (5 / 2) * Real.cos (nStar * t) ∧
    (keplerIC sStar t).ofLp 1 = (5 / 2) * Real.sin (nStar * t) := by
  rw [keplerIC_sStar, nStar]
  constructor <;> simp [circular_ofLp0, circular_ofLp1]

lemma obs_ofLp01 (t : ℝ) :
    (obs t).ofLp 0 = Real.cos t ∧ (obs t).ofLp 1 = Real.sin t := by
  simp [obs, circular_ofLp0, circular_ofLp1]

lemma rhoStar_sq_coords (t : ℝ) :
    rhoStar t ^ 2 =
      ((5 / 2) * Real.cos (nStar * t) - Real.cos t) ^ 2 +
        ((5 / 2) * Real.sin (nStar * t) - Real.sin t) ^ 2 := by
  have hx := keplerIC_sStar_ofLp01 t
  have he := obs_ofLp01 t
  have hz0 := keplerIC_sStar_ofLp2 t
  have hez := obs_ofLp2 t
  unfold rhoStar
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
  simp [Fin.sum_univ_three, PiLp.sub_apply, hx.1, hx.2, he.1, he.2, hz0, hez]

lemma rhoStar_sq_trig (t : ℝ) :
    rhoStar t ^ 2 =
      (29 / 4 : ℝ) -
        5 * (Real.cos (nStar * t) * Real.cos t +
          Real.sin (nStar * t) * Real.sin t) := by
  rw [rhoStar_sq_coords]
  set cn := Real.cos (nStar * t)
  set sn := Real.sin (nStar * t)
  set c := Real.cos t
  set s := Real.sin t
  have hc : cn ^ 2 + sn ^ 2 = 1 := Real.cos_sq_add_sin_sq _
  have he : c ^ 2 + s ^ 2 = 1 := Real.cos_sq_add_sin_sq _
  calc
    (5 / 2 * cn - c) ^ 2 + (5 / 2 * sn - s) ^ 2
        = (25 / 4) * cn ^ 2 - 5 * cn * c + c ^ 2
          + (25 / 4) * sn ^ 2 - 5 * sn * s + s ^ 2 := by ring
    _ = (25 / 4) * (cn ^ 2 + sn ^ 2) + (c ^ 2 + s ^ 2)
          - 5 * (cn * c + sn * s) := by ring
    _ = (25 / 4) * 1 + 1 - 5 * (cn * c + sn * s) := by rw [hc, he]
    _ = 29 / 4 - 5 * (cn * c + sn * s) := by ring

lemma rhoStar_sq_cos (t : ℝ) :
    rhoStar t ^ 2 = (29 / 4 : ℝ) - 5 * Real.cos ((nStar - 1) * t) := by
  rw [rhoStar_sq_trig]
  have htrig :
      Real.cos (nStar * t) * Real.cos t + Real.sin (nStar * t) * Real.sin t
        = Real.cos ((nStar - 1) * t) := by
    have : (nStar - 1) * t = nStar * t - t := by ring
    rw [this, Real.cos_sub]
  rw [htrig]

lemma rhoStar_zero : rhoStar 0 = 3 / 2 := by
  have hsq : rhoStar 0 ^ 2 = (9 / 4 : ℝ) := by
    rw [rhoStar_sq_cos]; simp; norm_num
  have hnn : 0 ≤ rhoStar 0 := norm_nonneg _
  have : rhoStar 0 = Real.sqrt (9 / 4 : ℝ) := by
    rw [← Real.sqrt_sq hnn, hsq]
  rw [this, show (9 / 4 : ℝ) = (3 / 2 : ℝ) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]

lemma phiZ_zero : phiZ 0 = 2 / 3 := by
  simp [phiZ, rhoStar_zero]

lemma phiVz_zero : phiVz 0 = 0 := by
  simp [phiVz]

lemma abs_nStar_div4_le_one : |nStar / 4| ≤ 1 := by
  rw [abs_of_nonneg (div_nonneg nStar_pos.le (by norm_num))]
  linarith [nStar_lt_one]

lemma abs_nStar_div2_le_one : |nStar / 2| ≤ 1 := by
  rw [abs_of_nonneg (div_nonneg nStar_pos.le (by norm_num))]
  linarith [nStar_lt_one]

lemma abs_nStar_le_one : |nStar| ≤ 1 := by
  rw [abs_of_nonneg nStar_pos.le]
  exact nStar_lt_one.le

lemma sin_cubic_mono {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) (hy : y ≤ 1) :
    x - x ^ 3 / 6 ≤ y - y ^ 3 / 6 := by
  have hx1 : x ≤ 1 := hxy.trans hy
  have hy0 : 0 ≤ y := hx.trans hxy
  have hx2 : x ^ 2 ≤ 1 := by nlinarith
  have hy2 : y ^ 2 ≤ 1 := by nlinarith
  have hxy1 : x * y ≤ 1 := mul_le_one₀ hx1 hy0 hy
  have hdiff : (y - y ^ 3 / 6) - (x - x ^ 3 / 6)
      = (y - x) * (1 - (x ^ 2 + x * y + y ^ 2) / 6) := by ring
  nlinarith [sub_nonneg.mpr hxy]

lemma cos_interval_of_abs {x aLo aHi : ℝ}
    (habs : |x| ≤ 1) (ha0 : 0 ≤ aLo) (hlo : aLo ≤ |x|) (hhi : |x| ≤ aHi) :
    (1 : ℝ) - aHi ^ 2 / 2 - aHi ^ 4 * (5 / 96) ≤ Real.cos x ∧
      Real.cos x ≤ (1 : ℝ) - aLo ^ 2 / 2 + aHi ^ 4 * (5 / 96) := by
  have hb := Real.cos_bound habs
  have hrem : |x| ^ 4 * (5 / 96) ≤ aHi ^ 4 * (5 / 96) :=
    mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (abs_nonneg _) hhi 4) (by norm_num)
  have hx2lo : aLo ^ 2 ≤ x ^ 2 := by
    have : aLo ^ 2 ≤ |x| ^ 2 := pow_le_pow_left₀ ha0 hlo 2
    rwa [sq_abs] at this
  have hx2hi : x ^ 2 ≤ aHi ^ 2 := by
    have : |x| ^ 2 ≤ aHi ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hhi 2
    rwa [sq_abs] at this
  have h1 := (abs_le.mp hb).1
  have h2 := (abs_le.mp hb).2
  constructor <;> linarith

lemma sin_interval {x xLo xHi : ℝ}
    (hx0 : 0 ≤ xLo) (hlo : xLo ≤ x) (hhi : x ≤ xHi) (h1 : xHi ≤ 1) :
    xLo - xLo ^ 3 / 6 - xHi ^ 5 / 100 ≤ Real.sin x ∧
      Real.sin x ≤ xHi - xHi ^ 3 / 6 + xHi ^ 5 / 100 := by
  have hxnn : 0 ≤ x := hx0.trans hlo
  have habs : |x| ≤ 1 := by
    rw [abs_of_nonneg hxnn]; exact hhi.trans h1
  have hb := Real.sin_bound habs
  have hrem : |x| ^ 5 / 100 ≤ xHi ^ 5 / 100 := by
    have : |x| ≤ xHi := by rwa [abs_of_nonneg hxnn]
    exact div_le_div_of_nonneg_right
      (pow_le_pow_left₀ (abs_nonneg _) this 5) (by norm_num)
  have hp' : xLo - xLo ^ 3 / 6 ≤ x - x ^ 3 / 6 :=
    sin_cubic_mono hx0 hlo (hhi.trans h1)
  have hp'' : x - x ^ 3 / 6 ≤ xHi - xHi ^ 3 / 6 :=
    sin_cubic_mono hxnn hhi h1
  have h1' := (abs_le.mp hb).1
  have h2' := (abs_le.mp hb).2
  constructor <;> linarith

lemma abs_nm1_mul_nonneg (t : ℝ) (ht : 0 ≤ t) :
    |(nStar - 1) * t| = (1 - nStar) * t := by
  have : (nStar - 1) * t ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr nStar_lt_one.le) ht
  rw [abs_of_nonpos this]; ring

lemma nStar_div4_bounds :
    (252 / 4000 : ℝ) < nStar / 4 ∧ nStar / 4 < (253 / 4000 : ℝ) := by
  constructor <;> linarith [nStar_gt_lo, nStar_lt_hi]

lemma nStar_div2_bounds :
    (252 / 2000 : ℝ) < nStar / 2 ∧ nStar / 2 < (253 / 2000 : ℝ) := by
  constructor <;> linarith [nStar_gt_lo, nStar_lt_hi]

lemma one_sub_nStar_div4_bounds :
    (747 / 4000 : ℝ) < (1 - nStar) / 4 ∧ (1 - nStar) / 4 < (748 / 4000 : ℝ) := by
  constructor <;> linarith [nStar_gt_lo, nStar_lt_hi]

lemma one_sub_nStar_div2_bounds :
    (747 / 2000 : ℝ) < (1 - nStar) / 2 ∧ (1 - nStar) / 2 < (748 / 2000 : ℝ) := by
  constructor <;> linarith [nStar_gt_lo, nStar_lt_hi]

lemma one_sub_nStar_bounds :
    (747 / 1000 : ℝ) < 1 - nStar ∧ 1 - nStar < (748 / 1000 : ℝ) := by
  constructor <;> linarith [nStar_gt_lo, nStar_lt_hi]

lemma cos_nStar_div4_bounds :
    (499 / 500 : ℝ) - (253 / 4000 : ℝ) ^ 4 * (5 / 96) ≤ Real.cos (nStar / 4) ∧
      Real.cos (nStar / 4) ≤ (499 / 500 : ℝ) + (253 / 4000 : ℝ) ^ 4 * (5 / 96) := by
  have hb := Real.cos_bound abs_nStar_div4_le_one
  have hmid : (1 : ℝ) - (nStar / 4) ^ 2 / 2 = 499 / 500 := by
    have : (nStar / 4) ^ 2 = nStar ^ 2 / 16 := by field_simp; ring
    rw [this, nStar_sq]; field_simp; norm_num
  have hrem : |nStar / 4| ^ 4 * (5 / 96) ≤ (253 / 4000 : ℝ) ^ 4 * (5 / 96) := by
    have : |nStar / 4| ≤ (253 / 4000 : ℝ) := by
      rw [abs_of_nonneg (div_nonneg nStar_pos.le (by norm_num))]
      exact nStar_div4_bounds.2.le
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (abs_nonneg _) this 4) (by norm_num)
  constructor <;> linarith [(abs_le.mp hb).1, (abs_le.mp hb).2]

lemma cos_nStar_div2_bounds :
    (124 / 125 : ℝ) - (253 / 2000 : ℝ) ^ 4 * (5 / 96) ≤ Real.cos (nStar / 2) ∧
      Real.cos (nStar / 2) ≤ (124 / 125 : ℝ) + (253 / 2000 : ℝ) ^ 4 * (5 / 96) := by
  have hb := Real.cos_bound abs_nStar_div2_le_one
  have hmid : (1 : ℝ) - (nStar / 2) ^ 2 / 2 = 124 / 125 := by
    have : (nStar / 2) ^ 2 = nStar ^ 2 / 4 := by field_simp; ring
    rw [this, nStar_sq]; field_simp; norm_num
  have hrem : |nStar / 2| ^ 4 * (5 / 96) ≤ (253 / 2000 : ℝ) ^ 4 * (5 / 96) := by
    have : |nStar / 2| ≤ (253 / 2000 : ℝ) := by
      rw [abs_of_nonneg (div_nonneg nStar_pos.le (by norm_num))]
      exact nStar_div2_bounds.2.le
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (abs_nonneg _) this 4) (by norm_num)
  constructor <;> linarith [(abs_le.mp hb).1, (abs_le.mp hb).2]

lemma cos_nStar_bounds :
    (121 / 125 : ℝ) - (253 / 1000 : ℝ) ^ 4 * (5 / 96) ≤ Real.cos nStar ∧
      Real.cos nStar ≤ (121 / 125 : ℝ) + (253 / 1000 : ℝ) ^ 4 * (5 / 96) := by
  have hb := Real.cos_bound abs_nStar_le_one
  have hmid : (1 : ℝ) - nStar ^ 2 / 2 = 121 / 125 := by
    rw [nStar_sq]; field_simp; norm_num
  have hrem : |nStar| ^ 4 * (5 / 96) ≤ (253 / 1000 : ℝ) ^ 4 * (5 / 96) := by
    have : |nStar| ≤ (253 / 1000 : ℝ) := by
      rw [abs_of_nonneg nStar_pos.le]; exact nStar_lt_hi.le
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (abs_nonneg _) this 4) (by norm_num)
  constructor <;> linarith [(abs_le.mp hb).1, (abs_le.mp hb).2]

lemma sin_nStar_div4_bounds :
    (252 / 4000 : ℝ) - (252 / 4000 : ℝ) ^ 3 / 6 - (253 / 4000 : ℝ) ^ 5 / 100
      ≤ Real.sin (nStar / 4) ∧
      Real.sin (nStar / 4)
        ≤ (253 / 4000 : ℝ) - (253 / 4000 : ℝ) ^ 3 / 6 + (253 / 4000 : ℝ) ^ 5 / 100 :=
  sin_interval (by norm_num) nStar_div4_bounds.1.le nStar_div4_bounds.2.le (by norm_num)

lemma sin_nStar_div2_bounds :
    (252 / 2000 : ℝ) - (252 / 2000 : ℝ) ^ 3 / 6 - (253 / 2000 : ℝ) ^ 5 / 100
      ≤ Real.sin (nStar / 2) ∧
      Real.sin (nStar / 2)
        ≤ (253 / 2000 : ℝ) - (253 / 2000 : ℝ) ^ 3 / 6 + (253 / 2000 : ℝ) ^ 5 / 100 :=
  sin_interval (by norm_num) nStar_div2_bounds.1.le nStar_div2_bounds.2.le (by norm_num)

lemma sin_nStar_bounds :
    (252 / 1000 : ℝ) - (252 / 1000 : ℝ) ^ 3 / 6 - (253 / 1000 : ℝ) ^ 5 / 100
      ≤ Real.sin nStar ∧
      Real.sin nStar
        ≤ (253 / 1000 : ℝ) - (253 / 1000 : ℝ) ^ 3 / 6 + (253 / 1000 : ℝ) ^ 5 / 100 :=
  sin_interval (by norm_num) nStar_gt_lo.le nStar_lt_hi.le (by norm_num)

lemma cos_nm1_div4_bounds :
    (1 : ℝ) - (748 / 4000 : ℝ) ^ 2 / 2 - (748 / 4000 : ℝ) ^ 4 * (5 / 96)
      ≤ Real.cos ((nStar - 1) * (1 / 4)) ∧
      Real.cos ((nStar - 1) * (1 / 4))
        ≤ (1 : ℝ) - (747 / 4000 : ℝ) ^ 2 / 2 + (748 / 4000 : ℝ) ^ 4 * (5 / 96) := by
  have hx : |(nStar - 1) * (1 / 4)| = (1 - nStar) / 4 := by
    simpa [div_eq_mul_inv] using abs_nm1_mul_nonneg (1 / 4) (by norm_num)
  have habs : |(nStar - 1) * (1 / 4)| ≤ 1 := by rw [hx]; linarith [nStar_gt_lo]
  refine cos_interval_of_abs habs (by norm_num) ?_ ?_
  · rw [hx]; exact one_sub_nStar_div4_bounds.1.le
  · rw [hx]; exact one_sub_nStar_div4_bounds.2.le

lemma cos_nm1_div2_bounds :
    (1 : ℝ) - (748 / 2000 : ℝ) ^ 2 / 2 - (748 / 2000 : ℝ) ^ 4 * (5 / 96)
      ≤ Real.cos ((nStar - 1) * (1 / 2)) ∧
      Real.cos ((nStar - 1) * (1 / 2))
        ≤ (1 : ℝ) - (747 / 2000 : ℝ) ^ 2 / 2 + (748 / 2000 : ℝ) ^ 4 * (5 / 96) := by
  have hx : |(nStar - 1) * (1 / 2)| = (1 - nStar) / 2 := by
    simpa [div_eq_mul_inv] using abs_nm1_mul_nonneg (1 / 2) (by norm_num)
  have habs : |(nStar - 1) * (1 / 2)| ≤ 1 := by rw [hx]; linarith [nStar_gt_lo]
  refine cos_interval_of_abs habs (by norm_num) ?_ ?_
  · rw [hx]; exact one_sub_nStar_div2_bounds.1.le
  · rw [hx]; exact one_sub_nStar_div2_bounds.2.le

lemma cos_nm1_one_bounds :
    (1 : ℝ) - (748 / 1000 : ℝ) ^ 2 / 2 - (748 / 1000 : ℝ) ^ 4 * (5 / 96)
      ≤ Real.cos (nStar - 1) ∧
      Real.cos (nStar - 1)
        ≤ (1 : ℝ) - (747 / 1000 : ℝ) ^ 2 / 2 + (748 / 1000 : ℝ) ^ 4 * (5 / 96) := by
  have hx : |nStar - 1| = 1 - nStar := by
    rw [abs_of_nonpos (sub_nonpos.mpr nStar_lt_one.le), neg_sub]
  have habs : |nStar - 1| ≤ 1 := by rw [hx]; linarith [nStar_gt_lo]
  refine cos_interval_of_abs habs (by norm_num) ?_ ?_
  · rw [hx]; exact one_sub_nStar_bounds.1.le
  · rw [hx]; exact one_sub_nStar_bounds.2.le

lemma rhoStar_sq_div4_bounds :
    (29 / 4 : ℝ) - 5 * ((1 : ℝ) - (747 / 4000 : ℝ) ^ 2 / 2 + (748 / 4000 : ℝ) ^ 4 * (5 / 96))
      ≤ rhoStar (1 / 4) ^ 2 ∧
      rhoStar (1 / 4) ^ 2
        ≤ (29 / 4 : ℝ) - 5 * ((1 : ℝ) - (748 / 4000 : ℝ) ^ 2 / 2 - (748 / 4000 : ℝ) ^ 4 * (5 / 96)) := by
  rw [rhoStar_sq_cos]; constructor <;> linarith [cos_nm1_div4_bounds.1, cos_nm1_div4_bounds.2]

lemma rhoStar_sq_div2_bounds :
    (29 / 4 : ℝ) - 5 * ((1 : ℝ) - (747 / 2000 : ℝ) ^ 2 / 2 + (748 / 2000 : ℝ) ^ 4 * (5 / 96))
      ≤ rhoStar (1 / 2) ^ 2 ∧
      rhoStar (1 / 2) ^ 2
        ≤ (29 / 4 : ℝ) - 5 * ((1 : ℝ) - (748 / 2000 : ℝ) ^ 2 / 2 - (748 / 2000 : ℝ) ^ 4 * (5 / 96)) := by
  rw [rhoStar_sq_cos]; constructor <;> linarith [cos_nm1_div2_bounds.1, cos_nm1_div2_bounds.2]

lemma rhoStar_sq_one_bounds :
    (29 / 4 : ℝ) - 5 * ((1 : ℝ) - (747 / 1000 : ℝ) ^ 2 / 2 + (748 / 1000 : ℝ) ^ 4 * (5 / 96))
      ≤ rhoStar 1 ^ 2 ∧
      rhoStar 1 ^ 2
        ≤ (29 / 4 : ℝ) - 5 * ((1 : ℝ) - (748 / 1000 : ℝ) ^ 2 / 2 - (748 / 1000 : ℝ) ^ 4 * (5 / 96)) := by
  have : (nStar - 1) * (1 : ℝ) = nStar - 1 := by ring
  rw [rhoStar_sq_cos, this]
  constructor <;> linarith [cos_nm1_one_bounds.1, cos_nm1_one_bounds.2]

lemma abs_rhoStar (t : ℝ) : |rhoStar t| = rhoStar t :=
  abs_of_nonneg (norm_nonneg _)

lemma le_rho_of_sq {a t : ℝ} (ha : 0 ≤ a) (hsq : a ^ 2 ≤ rhoStar t ^ 2) :
    a ≤ rhoStar t := by
  have := sq_le_sq.mp hsq
  rwa [abs_of_nonneg ha, abs_rhoStar t] at this

lemma rho_of_sq_le {a t : ℝ} (ha : 0 ≤ a) (hsq : rhoStar t ^ 2 ≤ a ^ 2) :
    rhoStar t ≤ a := by
  have := sq_le_sq.mp hsq
  rwa [abs_rhoStar t, abs_of_nonneg ha] at this

lemma rhoStar_div4_bounds :
    (764341 / 500000 : ℝ) ≤ rhoStar (1 / 4) ∧
      rhoStar (1 / 4) ≤ (191121 / 125000 : ℝ) := by
  have hr := rhoStar_sq_div4_bounds
  constructor
  · refine le_rho_of_sq (by norm_num) (le_trans ?_ hr.1)
    norm_num
  · refine rho_of_sq_le (by norm_num) (le_trans hr.2 ?_)
    norm_num

lemma rhoStar_div2_bounds :
    (402621 / 250000 : ℝ) ≤ rhoStar (1 / 2) ∧
      rhoStar (1 / 2) ≤ (322787 / 200000 : ℝ) := by
  have hr := rhoStar_sq_div2_bounds
  constructor
  · refine le_rho_of_sq (by norm_num) (le_trans ?_ hr.1)
    norm_num
  · refine rho_of_sq_le (by norm_num) (le_trans hr.2 ?_)
    norm_num

lemma rhoStar_one_bounds :
    (1887723 / 1000000 : ℝ) ≤ rhoStar 1 ∧
      rhoStar 1 ≤ (965697 / 500000 : ℝ) := by
  have hr := rhoStar_sq_one_bounds
  constructor
  · refine le_rho_of_sq (by norm_num) (le_trans ?_ hr.1)
    norm_num
  · refine rho_of_sq_le (by norm_num) (le_trans hr.2 ?_)
    norm_num

lemma div_bounds {nLo nHi dLo dHi n d : ℝ}
    (hn0 : 0 ≤ nLo) (hd0 : 0 < dLo)
    (hnl : nLo ≤ n) (hnh : n ≤ nHi) (hdl : dLo ≤ d) (hdh : d ≤ dHi) :
    nLo / dHi ≤ n / d ∧ n / d ≤ nHi / dLo := by
  have hd : 0 < d := hd0.trans_le hdl
  have hdHi : 0 < dHi := hd.trans_le hdh
  constructor
  · rw [div_le_div_iff₀ hdHi hd]; nlinarith
  · rw [div_le_div_iff₀ hd hd0]; nlinarith

lemma phiZ_apply (t : ℝ) : phiZ t = Real.cos (nStar * t) / rhoStar t := rfl

lemma phiVz_apply (t : ℝ) :
    phiVz t = Real.sin (nStar * t) / (nStar * rhoStar t) := by
  simp [phiVz, div_div, mul_comm]

lemma phiZ_div4_bounds :
    ((499 / 500 : ℝ) - (253 / 4000 : ℝ) ^ 4 * (5 / 96)) / (191121 / 125000)
      ≤ phiZ (1 / 4) ∧
      phiZ (1 / 4)
        ≤ ((499 / 500 : ℝ) + (253 / 4000 : ℝ) ^ 4 * (5 / 96)) / (764341 / 500000) := by
  rw [phiZ_apply, show nStar * (1 / 4) = nStar / 4 by ring]
  refine div_bounds ?_ (by norm_num) cos_nStar_div4_bounds.1 cos_nStar_div4_bounds.2
    rhoStar_div4_bounds.1 rhoStar_div4_bounds.2
  linarith [cos_nStar_div4_bounds.1]

lemma phiZ_div2_bounds :
    ((124 / 125 : ℝ) - (253 / 2000 : ℝ) ^ 4 * (5 / 96)) / (322787 / 200000)
      ≤ phiZ (1 / 2) ∧
      phiZ (1 / 2)
        ≤ ((124 / 125 : ℝ) + (253 / 2000 : ℝ) ^ 4 * (5 / 96)) / (402621 / 250000) := by
  rw [phiZ_apply, show nStar * (1 / 2) = nStar / 2 by ring]
  refine div_bounds ?_ (by norm_num) cos_nStar_div2_bounds.1 cos_nStar_div2_bounds.2
    rhoStar_div2_bounds.1 rhoStar_div2_bounds.2
  linarith [cos_nStar_div2_bounds.1]

lemma phiZ_one_bounds :
    ((121 / 125 : ℝ) - (253 / 1000 : ℝ) ^ 4 * (5 / 96)) / (965697 / 500000)
      ≤ phiZ 1 ∧
      phiZ 1
        ≤ ((121 / 125 : ℝ) + (253 / 1000 : ℝ) ^ 4 * (5 / 96)) / (1887723 / 1000000) := by
  rw [phiZ_apply, mul_one]
  refine div_bounds ?_ (by norm_num) cos_nStar_bounds.1 cos_nStar_bounds.2
    rhoStar_one_bounds.1 rhoStar_one_bounds.2
  linarith [cos_nStar_bounds.1]

lemma phiVz_div4_bounds :
    ((252 / 4000 : ℝ) - (252 / 4000 : ℝ) ^ 3 / 6 - (253 / 4000 : ℝ) ^ 5 / 100)
        / ((253 / 1000 : ℝ) * (191121 / 125000))
      ≤ phiVz (1 / 4) ∧
      phiVz (1 / 4)
        ≤ ((253 / 4000 : ℝ) - (253 / 4000 : ℝ) ^ 3 / 6 + (253 / 4000 : ℝ) ^ 5 / 100)
          / ((252 / 1000 : ℝ) * (764341 / 500000)) := by
  rw [phiVz_apply, show nStar * (1 / 4) = nStar / 4 by ring]
  have hdLo : (0 : ℝ) < (252 / 1000) * (764341 / 500000) := by norm_num
  have hn0 : (0 : ℝ)
      ≤ (252 / 4000 : ℝ) - (252 / 4000 : ℝ) ^ 3 / 6 - (253 / 4000 : ℝ) ^ 5 / 100 := by
    norm_num
  have hden_lo : (252 / 1000 : ℝ) * (764341 / 500000) ≤ nStar * rhoStar (1 / 4) :=
    mul_le_mul nStar_gt_lo.le rhoStar_div4_bounds.1 (by norm_num) nStar_pos.le
  have hden_hi : nStar * rhoStar (1 / 4) ≤ (253 / 1000 : ℝ) * (191121 / 125000) :=
    mul_le_mul nStar_lt_hi.le rhoStar_div4_bounds.2 (norm_nonneg _) (by norm_num)
  exact div_bounds hn0 (by norm_num) sin_nStar_div4_bounds.1 sin_nStar_div4_bounds.2
    hden_lo hden_hi

lemma phiVz_div2_bounds :
    ((252 / 2000 : ℝ) - (252 / 2000 : ℝ) ^ 3 / 6 - (253 / 2000 : ℝ) ^ 5 / 100)
        / ((253 / 1000 : ℝ) * (322787 / 200000))
      ≤ phiVz (1 / 2) ∧
      phiVz (1 / 2)
        ≤ ((253 / 2000 : ℝ) - (253 / 2000 : ℝ) ^ 3 / 6 + (253 / 2000 : ℝ) ^ 5 / 100)
          / ((252 / 1000 : ℝ) * (402621 / 250000)) := by
  rw [phiVz_apply, show nStar * (1 / 2) = nStar / 2 by ring]
  have hn0 : (0 : ℝ)
      ≤ (252 / 2000 : ℝ) - (252 / 2000 : ℝ) ^ 3 / 6 - (253 / 2000 : ℝ) ^ 5 / 100 := by
    norm_num
  have hden_lo : (252 / 1000 : ℝ) * (402621 / 250000) ≤ nStar * rhoStar (1 / 2) :=
    mul_le_mul nStar_gt_lo.le rhoStar_div2_bounds.1 (by norm_num) nStar_pos.le
  have hden_hi : nStar * rhoStar (1 / 2) ≤ (253 / 1000 : ℝ) * (322787 / 200000) :=
    mul_le_mul nStar_lt_hi.le rhoStar_div2_bounds.2 (norm_nonneg _) (by norm_num)
  exact div_bounds hn0 (by norm_num) sin_nStar_div2_bounds.1 sin_nStar_div2_bounds.2
    hden_lo hden_hi

lemma phiVz_one_bounds :
    ((252 / 1000 : ℝ) - (252 / 1000 : ℝ) ^ 3 / 6 - (253 / 1000 : ℝ) ^ 5 / 100)
        / ((253 / 1000 : ℝ) * (965697 / 500000))
      ≤ phiVz 1 ∧
      phiVz 1
        ≤ ((253 / 1000 : ℝ) - (253 / 1000 : ℝ) ^ 3 / 6 + (253 / 1000 : ℝ) ^ 5 / 100)
          / ((252 / 1000 : ℝ) * (1887723 / 1000000)) := by
  rw [phiVz_apply, mul_one]
  have hn0 : (0 : ℝ)
      ≤ (252 / 1000 : ℝ) - (252 / 1000 : ℝ) ^ 3 / 6 - (253 / 1000 : ℝ) ^ 5 / 100 := by
    norm_num
  have hden_lo : (252 / 1000 : ℝ) * (1887723 / 1000000) ≤ nStar * rhoStar 1 :=
    mul_le_mul nStar_gt_lo.le rhoStar_one_bounds.1 (by norm_num) nStar_pos.le
  have hden_hi : nStar * rhoStar 1 ≤ (253 / 1000 : ℝ) * (965697 / 500000) :=
    mul_le_mul nStar_lt_hi.le rhoStar_one_bounds.2 (norm_nonneg _) (by norm_num)
  exact div_bounds hn0 (by norm_num) sin_nStar_bounds.1 sin_nStar_bounds.2
    hden_lo hden_hi

lemma deltaPhi_phiZ_hSD1 :
    deltaPhi phiZ hSD1 = (2 / 3 : ℝ) - 2 * phiZ (1 / 4) + phiZ (1 / 2) := by
  unfold deltaPhi hSD1; rw [phiZ_zero]; norm_num

lemma deltaPhi_phiZ_hSD2 :
    deltaPhi phiZ hSD2 = (2 / 3 : ℝ) - 2 * phiZ (1 / 2) + phiZ 1 := by
  unfold deltaPhi hSD2; rw [phiZ_zero]; norm_num

lemma deltaPhi_phiVz_hSD1 :
    deltaPhi phiVz hSD1 = -2 * phiVz (1 / 4) + phiVz (1 / 2) := by
  unfold deltaPhi hSD1; rw [phiVz_zero]; norm_num

lemma deltaPhi_phiVz_hSD2 :
    deltaPhi phiVz hSD2 = -2 * phiVz (1 / 2) + phiVz 1 := by
  unfold deltaPhi hSD2; rw [phiVz_zero]; norm_num

lemma zBlk_det_pos : 0 < zBlk.det := by
  rw [zBlk_det_eq, deltaPhi_phiZ_hSD1, deltaPhi_phiZ_hSD2,
    deltaPhi_phiVz_hSD1, deltaPhi_phiVz_hSD2]
  have hz14 := phiZ_div4_bounds
  have hz12 := phiZ_div2_bounds
  have hz1 := phiZ_one_bounds
  have hv14 := phiVz_div4_bounds
  have hv12 := phiVz_div2_bounds
  have hv1 := phiVz_one_bounds
  have hpos : (0 : ℝ) < 7 / 10000 := by norm_num
  nlinarith [hpos]

lemma zBlk_det_ne : zBlk.det ≠ 0 := zBlk_det_pos.ne'

/-- In-plane Cartesian axes `(x,y,vx,vy)`. -/
def inPlane : Fin 4 → Fin 6 := ![0, 1, 3, 4]

/-- In-plane second-difference coordinates `(Δx₁,Δy₁,Δx₂,Δy₂)`. -/
def inPlaneOut : Fin 4 → Fin 6 := ![0, 1, 3, 4]

/-- In-plane 4×4 block of `D sdCart` at `sStar`. Numeric det ~ 3.79e-7. -/
def xyBlk : Matrix (Fin 4) (Fin 4) ℝ :=
  Matrix.of fun i j =>
    fderiv ℝ sdCart sStar (Pi.single (inPlane j) 1) (inPlaneOut i)

def eX : Vec := ofCoords 1 0 0
def eY : Vec := ofCoords 0 1 0

/-- Circular-Kepler STM radial LVLH coordinate, inertial ICs. -/
def stmRad (t dx dy dvx dvy : ℝ) : ℝ :=
  (2 - Real.cos (nStar * t)) * dx + Real.sin (nStar * t) * dy
    + Real.sin (nStar * t) / nStar * dvx
    + 2 * (1 - Real.cos (nStar * t)) / nStar * dvy

/-- Circular-Kepler STM along-track LVLH coordinate, inertial ICs. -/
def stmTan (t dx dy dvx dvy : ℝ) : ℝ :=
  (2 * Real.sin (nStar * t) - 3 * nStar * t) * dx
    + (2 * Real.cos (nStar * t) - 1) * dy
    - 2 * (1 - Real.cos (nStar * t)) / nStar * dvx
    + (4 * Real.sin (nStar * t) - 3 * nStar * t) / nStar * dvy

def erOf (t : ℝ) : Vec :=
  ofCoords (Real.cos (nStar * t)) (Real.sin (nStar * t)) 0

def ethOf (t : ℝ) : Vec :=
  ofCoords (-Real.sin (nStar * t)) (Real.cos (nStar * t)) 0

def stmInertial (t dx dy dvx dvy : ℝ) : Vec :=
  stmRad t dx dy dvx dvy • erOf t + stmTan t dx dy dvx dvy • ethOf t

def stmCol (j : Fin 4) (t : ℝ) : Vec :=
  match j with
  | ⟨0, _⟩ => stmInertial t 1 0 0 0
  | ⟨1, _⟩ => stmInertial t 0 1 0 0
  | ⟨2, _⟩ => stmInertial t 0 0 1 0
  | ⟨3, _⟩ => stmInertial t 0 0 0 1

def uStar (t : ℝ) : Vec := (rhoStar t)⁻¹ • (keplerIC sStar t - obs t)

/-- First-order los variation from an in-plane inertial displacement. -/
def dlosSTM (t : ℝ) (dr : Vec) : Vec :=
  (rhoStar t)⁻¹ • (dr - ⟪uStar t, dr⟫ • uStar t)

def dlosCol (j : Fin 4) (t : ℝ) : Vec := dlosSTM t (stmCol j t)

def xyBlkSTM : Matrix (Fin 4) (Fin 4) ℝ :=
  Matrix.of fun i j =>
    let w1 := dlosCol j 0 - (2 : ℝ) • dlosCol j hSD1 + dlosCol j (2 * hSD1)
    let w2 := dlosCol j 0 - (2 : ℝ) • dlosCol j hSD2 + dlosCol j (2 * hSD2)
    match i with
    | ⟨0, _⟩ => w1.ofLp 0
    | ⟨1, _⟩ => w1.ofLp 1
    | ⟨2, _⟩ => w2.ofLp 0
    | ⟨3, _⟩ => w2.ofLp 1

lemma inPlane_apply :
    inPlane 0 = 0 ∧ inPlane 1 = 1 ∧ inPlane 2 = 3 ∧ inPlane 3 = 4 := by
  simp [inPlane]

lemma inPlaneOut_apply :
    inPlaneOut 0 = 0 ∧ inPlaneOut 1 = 1 ∧ inPlaneOut 2 = 3 ∧ inPlaneOut 3 = 4 := by
  simp [inPlaneOut]

lemma velNormSq_lineJet0 (ε : ℝ) :
    ‖stateVel (lineJet 0 ε)‖ ^ 2 = 2 / 5 := by
  rw [stateVel_lineJet0, ofCoords_norm]
  have hnn : (0 : ℝ) ≤ 0 ^ 2 + (Real.sqrt 10 / 5) ^ 2 + 0 ^ 2 := by positivity
  rw [Real.sq_sqrt hnn]
  field_simp
  rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 10)]
  norm_num

lemma sigmaOf_lineJet0 (ε : ℝ) : sigmaOf (lineJet 0 ε) = 0 := by
  simp [sigmaOf, vecDot, statePos_lineJet0, stateVel_lineJet0, ofLp_ofCoords,
    Fin.sum_univ_three]

lemma alphaOf_lineJet0 {ε : ℝ} (hε : -5 / 2 < ε) :
    alphaOf (lineJet 0 ε) = 2 / (5 / 2 + ε) - 2 / 5 := by
  simp [alphaOf, rnorm_lineJet0 hε, velNormSq_lineJet0]

lemma one_sub_alpha_r_lineJet0 {ε : ℝ} (hε : -5 / 2 < ε) :
    1 - alphaOf (lineJet 0 ε) * rnorm (lineJet 0 ε) = (2 / 5) * ε := by
  have hr : rnorm (lineJet 0 ε) = 5 / 2 + ε := rnorm_lineJet0 hε
  have hden : 5 / 2 + ε ≠ 0 := by linarith
  rw [alphaOf_lineJet0 hε, hr]
  calc
    1 - (2 / (5 / 2 + ε) - 2 / 5) * (5 / 2 + ε)
        = 1 - (2 / (5 / 2 + ε) * (5 / 2 + ε) - (2 / 5) * (5 / 2 + ε)) := by
          ring
    _ = 1 - (2 - (2 / 5) * (5 / 2 + ε)) := by
          rw [div_mul_cancel₀ (2 : ℝ) hden]
    _ = (2 / 5) * (5 / 2 + ε) - 1 := by ring
    _ = (2 / 5) * ε := by ring

lemma univF_lineJet0 (ε χ : ℝ) (hε : -5 / 2 < ε) :
    univF (lineJet 0 ε) χ =
      (2 / 5) * ε * χ ^ 3 * stumpffS (alphaOf (lineJet 0 ε) * χ ^ 2)
        + (5 / 2 + ε) * χ := by
  rw [univF, sigmaOf_lineJet0, one_sub_alpha_r_lineJet0 hε, rnorm_lineJet0 hε]
  ring

lemma continuousAt_alphaOf_lineJet0 :
    ContinuousAt (fun ε => alphaOf (lineJet 0 ε)) 0 := by
  have hnhds : ∀ᶠ ε : ℝ in 𝓝 0, -5 / 2 < ε :=
    eventually_gt_nhds (by norm_num : (-5 / 2 : ℝ) < 0)
  have hclosed : ContinuousAt (fun ε : ℝ => 2 / (5 / 2 + ε) - 2 / 5) 0 := by
    have hden : ContinuousAt (fun ε : ℝ => 5 / 2 + ε) 0 :=
      continuousAt_const.add continuousAt_id
    have hinv : ContinuousAt (fun ε : ℝ => (5 / 2 + ε)⁻¹) 0 :=
      ContinuousAt.inv₀ hden (by norm_num)
    exact (hinv.const_mul (2 : ℝ)).sub_const (2 / 5)
  exact hclosed.congr (hnhds.mono fun ε hε => (alphaOf_lineJet0 hε).symm)

lemma eventually_alpha_lineJet0_nonneg (χ : ℝ) :
    ∀ᶠ ε : ℝ in 𝓝 0, 0 ≤ alphaOf (lineJet 0 ε) * χ ^ 2 := by
  have : ∀ᶠ ε : ℝ in 𝓝 0, -1 / 4 < ε ∧ ε < 1 / 4 :=
    eventually_and.2 ⟨eventually_gt_nhds (by norm_num), eventually_lt_nhds (by norm_num)⟩
  refine this.mono fun ε ⟨hlo, hhi⟩ => ?_
  have hε : -5 / 2 < ε := by linarith
  rw [alphaOf_lineJet0 hε]
  have hpos : 0 < 2 / (5 / 2 + ε) - 2 / 5 := by
    have hr : 0 < 5 / 2 + ε := by linarith
    have hlt : 5 / 2 + ε < 11 / 4 := by linarith
    have : 2 / (11 / 4 : ℝ) < 2 / (5 / 2 + ε) :=
      (div_lt_div_iff_of_pos_left (by norm_num : (0 : ℝ) < 2) (by positivity) hr).mpr hlt
    have hconv : 2 / (11 / 4 : ℝ) = (8 / 11 : ℝ) := by norm_num
    linarith
  exact mul_nonneg hpos.le (sq_nonneg _)

lemma continuousAt_stumpffS_alpha_lineJet0 (χ : ℝ) :
    ContinuousAt (fun ε => stumpffS (alphaOf (lineJet 0 ε) * χ ^ 2)) 0 := by
  have hmul : ContinuousAt (fun ε => alphaOf (lineJet 0 ε) * χ ^ 2) 0 :=
    continuousAt_alphaOf_lineJet0.mul_const _
  have hcongr :
      (fun ε => stumpffS (alphaOf (lineJet 0 ε) * χ ^ 2)) =ᶠ[𝓝 0]
        fun ε => sbar (Real.sqrt (alphaOf (lineJet 0 ε) * χ ^ 2)) :=
    (eventually_alpha_lineJet0_nonneg χ).mono fun ε hz => stumpffS_eq_sbar hz
  have hinner : ContinuousAt (fun ε => sbar (Real.sqrt (alphaOf (lineJet 0 ε) * χ ^ 2))) 0 :=
    (continuous_sbar.comp Real.continuous_sqrt).continuousAt.comp hmul
  exact hinner.congr hcongr.symm

lemma hasDerivAt_mul_continuousAt {g : ℝ → ℝ} {y : ℝ}
    (hg : ContinuousAt g 0) (hy : g 0 = y) :
    HasDerivAt (fun ε => ε * g ε) y 0 := by
  rw [hasDerivAt_iff_tendsto_slope]
  have ht : Tendsto g (𝓝[≠] (0 : ℝ)) (𝓝 y) := by
    simpa [hy] using hg.tendsto.mono_left nhdsWithin_le_nhds
  refine ht.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have hne : ε ≠ 0 := by
    simpa [Set.mem_compl_iff, Set.mem_singleton_iff] using hε
  simp [slope, hne]


lemma alphaOf_lineJet0_zero : alphaOf (lineJet 0 0) = 2 / 5 := by
  rw [lineJet_zero, alphaOf_sStar]

lemma hasDerivAt_univF_lineJet0_fixed (χ : ℝ) :
    HasDerivAt (fun ε => univF (lineJet 0 ε) χ)
      ((2 / 5) * χ ^ 3 * stumpffS ((2 / 5) * χ ^ 2) + χ) 0 := by
  have hnhds : ∀ᶠ ε : ℝ in 𝓝 0, -5 / 2 < ε := eventually_lineJet0_pos
  have hg : ContinuousAt
      (fun ε => (2 / 5) * χ ^ 3 * stumpffS (alphaOf (lineJet 0 ε) * χ ^ 2)) 0 :=
    (continuousAt_stumpffS_alpha_lineJet0 χ).const_mul _
  have hy :
      (2 / 5) * χ ^ 3 * stumpffS (alphaOf (lineJet 0 0) * χ ^ 2)
        = (2 / 5) * χ ^ 3 * stumpffS ((2 / 5) * χ ^ 2) := by
    rw [alphaOf_lineJet0_zero]
  have hmul := hasDerivAt_mul_continuousAt hg hy
  have hadd : HasDerivAt (fun ε : ℝ => (5 / 2 + ε) * χ) χ 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).const_add (5 / 2)).mul_const χ
  have hsum := hmul.add hadd
  have heq : (fun ε => univF (lineJet 0 ε) χ) =ᶠ[𝓝 0]
      fun ε => ε * ((2 / 5) * χ ^ 3 * stumpffS (alphaOf (lineJet 0 ε) * χ ^ 2))
        + (5 / 2 + ε) * χ := by
    filter_upwards [hnhds] with ε hε
    rw [univF_lineJet0 ε χ hε]
    ring
  have hsum' : HasDerivAt
      (fun ε => ε * ((2 / 5) * χ ^ 3 * stumpffS (alphaOf (lineJet 0 ε) * χ ^ 2))
        + (5 / 2 + ε) * χ)
      ((2 / 5) * χ ^ 3 * stumpffS ((2 / 5) * χ ^ 2) + χ) 0 :=
    (hsum.congr_deriv (by ring))
  exact hsum'.congr_of_eventuallyEq heq

/-- IFT along an axis: `χ' = -F_ε / (5/2)` at the circular solution. -/
lemma hasDerivAt_chiOf_axis_gen {j : Fin 6} (t : ℝ) {Fε : ℝ}
    (hfixed : HasDerivAt (fun ε => univF (lineJet j ε) (2 * t / 5)) Fε 0) :
    HasDerivAt (fun ε => chiOf (lineJet j ε) t) (-(2 / 5) * Fε) 0 := by
  have hχ := hasDerivAt_chiOf_lineJet j t
  have hF : HasFDerivAt (Function.uncurry univF)
      (fderiv ℝ (Function.uncurry univF) (sStar, 2 * t / 5))
      (sStar, 2 * t / 5) :=
    hasFDerivAt_uncurry_univF (2 * t / 5)
  set χ' := fderiv ℝ (fun s => chiOf s t) sStar (Pi.single j 1)
  have hpath : HasDerivAt (fun ε => (lineJet j ε, chiOf (lineJet j ε) t))
      (Pi.single j (1 : ℝ), χ') 0 :=
    (hasDerivAt_lineJet j 0).prodMk hχ
  have hFpath : HasFDerivAt (Function.uncurry univF)
      (fderiv ℝ (Function.uncurry univF) (lineJet j 0, chiOf (lineJet j 0) t))
      (lineJet j 0, chiOf (lineJet j 0) t) := by
    rw [lineJet_zero, chiOf_sStar]; exact hF
  have hcomp := hFpath.comp_hasDerivAt 0 hpath
  have hid : HasDerivAt (fun ε => univF (lineJet j ε) (chiOf (lineJet j ε) t)) 0 0 := by
    refine (hasDerivAt_const 0 t).congr_of_eventuallyEq ?_
    exact (tendsto_lineJet j).eventually (eventually_univF_chiOf t)
  have huniq := hcomp.unique hid
  have hpair0 := hasDerivAt_pair_lineJet_const j (2 * t / 5) 0
  have hF0 : HasFDerivAt (Function.uncurry univF)
      (fderiv ℝ (Function.uncurry univF) (lineJet j 0, 2 * t / 5))
      (lineJet j 0, 2 * t / 5) := by
    rw [lineJet_zero]; exact hF
  have hcomp0 := hF0.comp_hasDerivAt 0 hpair0
  have h0 := hcomp0.unique hfixed
  have hlin :
      fderiv ℝ (Function.uncurry univF) (sStar, 2 * t / 5) (Pi.single j 1, χ') = 0 := by
    have hpt : (lineJet j 0, chiOf (lineJet j 0) t) = (sStar, 2 * t / 5) := by
      simp [lineJet_zero, chiOf_sStar]
    simpa [hpt, χ'] using huniq
  have hlin0 :
      fderiv ℝ (Function.uncurry univF) (sStar, 2 * t / 5) (Pi.single j 1, (0 : ℝ))
        = Fε := by
    have hpt : lineJet j 0 = sStar := lineJet_zero j
    simpa [hpt] using h0
  have hdiff :
      fderiv ℝ (Function.uncurry univF) (sStar, 2 * t / 5) (0, χ') = -Fε := by
    have hL :=
      (map_sub (fderiv ℝ (Function.uncurry univF) (sStar, 2 * t / 5))
        (Pi.single j (1 : ℝ), χ') (Pi.single j (1 : ℝ), (0 : ℝ)))
    have hsub : (Pi.single j (1 : ℝ), χ') - (Pi.single j (1 : ℝ), (0 : ℝ))
        = ((0 : Fin 6 → ℝ), χ') := by
      apply Prod.ext
      · simp
      · simp
    have : fderiv ℝ (Function.uncurry univF) (sStar, 2 * t / 5) (0, χ')
        = 0 - Fε := by
      rw [← hsub, hL, hlin, hlin0]
    linarith
  have hmul : (5 / 2 : ℝ) * χ' = -Fε := by
    rw [← univF_fderiv_inr (2 * t / 5) χ', hdiff]
  have hχeq : χ' = -(2 / 5) * Fε := by
    have h52 : (5 / 2 : ℝ) ≠ 0 := by norm_num
    field_simp [h52] at hmul
    linarith
  exact hχ.congr_deriv hχeq

def Fε_lineJet0 (χ : ℝ) : ℝ :=
  (2 / 5) * χ ^ 3 * stumpffS ((2 / 5) * χ ^ 2) + χ

lemma hasDerivAt_chiOf_lineJet0 (t : ℝ) :
    HasDerivAt (fun ε => chiOf (lineJet 0 ε) t)
      (-(2 / 5) * Fε_lineJet0 (2 * t / 5)) 0 :=
  hasDerivAt_chiOf_axis_gen t (hasDerivAt_univF_lineJet0_fixed (2 * t / 5))

lemma Fε_lineJet0_sStar (t : ℝ) :
    Fε_lineJet0 (2 * t / 5) =
      (2 / 5) * (t - Real.sin (nStar * t) / nStar) + (2 * t / 5) := by
  unfold Fε_lineJet0
  have hg : (2 * t / 5) ^ 3 * stumpffS (alphaOf sStar * (2 * t / 5) ^ 2)
      = t - Real.sin (nStar * t) / nStar := by
    have h := fg_g_sStar t
    -- fg_g sStar t (2t/5) = t - χ³ S = sin(nt)/n
    have h' : t - (2 * t / 5) ^ 3 * stumpffS (alphaOf sStar * (2 * t / 5) ^ 2)
        = Real.sin (nStar * t) / nStar := by
      simpa [fg_g, nStar] using h
    linarith
  have hz : alphaOf sStar * (2 * t / 5) ^ 2 = (2 / 5) * (2 * t / 5) ^ 2 := by
    rw [alphaOf_sStar]
  have : (2 * t / 5) ^ 3 * stumpffS ((2 / 5) * (2 * t / 5) ^ 2)
      = t - Real.sin (nStar * t) / nStar := by
    simpa [hz] using hg
  calc
    (2 / 5) * (2 * t / 5) ^ 3 * stumpffS ((2 / 5) * (2 * t / 5) ^ 2) + (2 * t / 5)
        = (2 / 5) * ((2 * t / 5) ^ 3 * stumpffS ((2 / 5) * (2 * t / 5) ^ 2))
          + (2 * t / 5) := by ring
    _ = (2 / 5) * (t - Real.sin (nStar * t) / nStar) + (2 * t / 5) := by
          rw [this]


lemma sigmaOf_lineJet1 (ε : ℝ) :
    sigmaOf (lineJet 1 ε) = ε * (Real.sqrt 10 / 5) := by
  simp [sigmaOf, vecDot, statePos_lineJet1, stateVel_lineJet1, ofLp_ofCoords,
    Fin.sum_univ_three]

lemma velNormSq_lineJet1 (ε : ℝ) : ‖stateVel (lineJet 1 ε)‖ ^ 2 = 2 / 5 :=
  velNormSq_lineJet0 ε ▸ (by
    have h : stateVel (lineJet 1 ε) = stateVel (lineJet 0 ε) := by
      simp [stateVel_lineJet1, stateVel_lineJet0]
    rw [h])

lemma alphaOf_lineJet1 (ε : ℝ) :
    alphaOf (lineJet 1 ε) = 2 / rnorm (lineJet 1 ε) - 2 / 5 := by
  simp [alphaOf, velNormSq_lineJet1]

lemma rnorm_lineJet1_even (ε : ℝ) :
    rnorm (lineJet 1 (-ε)) = rnorm (lineJet 1 ε) := by
  simp [rnorm_lineJet1]

lemma continuousAt_alphaOf_lineJet1 :
    ContinuousAt (fun ε => alphaOf (lineJet 1 ε)) 0 := by
  have hr : ContinuousAt (fun ε => rnorm (lineJet 1 ε)) 0 :=
    hasDerivAt_rnorm_lineJet1.continuousAt
  have hinv : ContinuousAt (fun ε => (2 : ℝ) / rnorm (lineJet 1 ε)) 0 := by
    refine continuousAt_const.div hr ?_
    have : rnorm (lineJet 1 0) = 5 / 2 := by
      rw [rnorm_lineJet1]; norm_num [Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 5 / 2)]
    rw [this]; norm_num
  have hclosed : ContinuousAt (fun ε : ℝ => 2 / rnorm (lineJet 1 ε) - 2 / 5) 0 :=
    hinv.sub_const (2 / 5)
  exact hclosed.congr (Eventually.of_forall fun ε => (alphaOf_lineJet1 ε).symm)

lemma eventually_alpha_lineJet1_nonneg (χ : ℝ) :
    ∀ᶠ ε : ℝ in 𝓝 0, 0 ≤ alphaOf (lineJet 1 ε) * χ ^ 2 := by
  have hα : ContinuousAt (fun ε => alphaOf (lineJet 1 ε)) 0 :=
    continuousAt_alphaOf_lineJet1
  have hα0 : 0 < alphaOf (lineJet 1 0) := by
    rw [lineJet_zero, alphaOf_sStar]; norm_num
  have hpos : ∀ᶠ ε : ℝ in 𝓝 0, 0 < alphaOf (lineJet 1 ε) :=
    hα.tendsto.eventually (Ioi_mem_nhds hα0)
  exact hpos.mono fun ε h => mul_nonneg h.le (sq_nonneg _)

lemma continuousAt_stumpffC_alpha_lineJet1 (χ : ℝ) :
    ContinuousAt (fun ε => stumpffC (alphaOf (lineJet 1 ε) * χ ^ 2)) 0 := by
  have hmul : ContinuousAt (fun ε => alphaOf (lineJet 1 ε) * χ ^ 2) 0 :=
    continuousAt_alphaOf_lineJet1.mul_const _
  have hcongr :
      (fun ε => stumpffC (alphaOf (lineJet 1 ε) * χ ^ 2)) =ᶠ[𝓝 0]
        fun ε => cbar (Real.sqrt (alphaOf (lineJet 1 ε) * χ ^ 2)) :=
    (eventually_alpha_lineJet1_nonneg χ).mono fun ε hz => stumpffC_eq_cbar hz
  have hinner :
      ContinuousAt (fun ε => cbar (Real.sqrt (alphaOf (lineJet 1 ε) * χ ^ 2))) 0 :=
    (continuous_cbar.comp Real.continuous_sqrt).continuousAt.comp hmul
  exact hinner.congr hcongr.symm

lemma univF_odd_lineJet1 (ε χ : ℝ) :
    univF (lineJet 1 ε) χ
      - ((1 - alphaOf (lineJet 1 ε) * rnorm (lineJet 1 ε)) * χ ^ 3
          * stumpffS (alphaOf (lineJet 1 ε) * χ ^ 2)
        + rnorm (lineJet 1 ε) * χ)
      = ε * ((Real.sqrt 10 / 5) * χ ^ 2 *
          stumpffC (alphaOf (lineJet 1 ε) * χ ^ 2)) := by
  simp [univF, sigmaOf_lineJet1]
  ring

lemma rest_lineJet1_even (ε χ : ℝ) :
    (1 - alphaOf (lineJet 1 (-ε)) * rnorm (lineJet 1 (-ε))) * χ ^ 3
        * stumpffS (alphaOf (lineJet 1 (-ε)) * χ ^ 2)
      + rnorm (lineJet 1 (-ε)) * χ
      = (1 - alphaOf (lineJet 1 ε) * rnorm (lineJet 1 ε)) * χ ^ 3
          * stumpffS (alphaOf (lineJet 1 ε) * χ ^ 2)
        + rnorm (lineJet 1 ε) * χ := by
  rw [alphaOf_lineJet1 (-ε), alphaOf_lineJet1 ε, rnorm_lineJet1_even]

lemma hasDerivAt_univF_lineJet1_fixed (χ : ℝ) :
    HasDerivAt (fun ε => univF (lineJet 1 ε) χ)
      ((Real.sqrt 10 / 5) * χ ^ 2 * stumpffC ((2 / 5) * χ ^ 2)) 0 := by
  have hg : ContinuousAt
      (fun ε => (Real.sqrt 10 / 5) * χ ^ 2 *
        stumpffC (alphaOf (lineJet 1 ε) * χ ^ 2)) 0 :=
    (continuousAt_stumpffC_alpha_lineJet1 χ).const_mul _
  have hy :
      (Real.sqrt 10 / 5) * χ ^ 2 * stumpffC (alphaOf (lineJet 1 0) * χ ^ 2)
        = (Real.sqrt 10 / 5) * χ ^ 2 * stumpffC ((2 / 5) * χ ^ 2) := by
    rw [lineJet_zero, alphaOf_sStar]
  have hodd := hasDerivAt_mul_continuousAt hg hy
  have hf := (differentiableAt_univF_lineJet 1 χ).hasDerivAt
  have hrest0 : HasDerivAt
      (fun ε => univF (lineJet 1 ε) χ
        - ε * ((Real.sqrt 10 / 5) * χ ^ 2 *
            stumpffC (alphaOf (lineJet 1 ε) * χ ^ 2)))
      (deriv (fun ε => univF (lineJet 1 ε) χ) 0
        - (Real.sqrt 10 / 5) * χ ^ 2 * stumpffC ((2 / 5) * χ ^ 2)) 0 :=
    hf.sub hodd
  have hrestFun :
      (fun ε => univF (lineJet 1 ε) χ
        - ε * ((Real.sqrt 10 / 5) * χ ^ 2 *
            stumpffC (alphaOf (lineJet 1 ε) * χ ^ 2)))
      = fun ε =>
        (1 - alphaOf (lineJet 1 ε) * rnorm (lineJet 1 ε)) * χ ^ 3
          * stumpffS (alphaOf (lineJet 1 ε) * χ ^ 2)
        + rnorm (lineJet 1 ε) * χ := by
    funext ε; linarith [univF_odd_lineJet1 ε χ]
  have hrest1 : HasDerivAt
      (fun ε =>
        (1 - alphaOf (lineJet 1 ε) * rnorm (lineJet 1 ε)) * χ ^ 3
          * stumpffS (alphaOf (lineJet 1 ε) * χ ^ 2)
        + rnorm (lineJet 1 ε) * χ)
      (deriv (fun ε => univF (lineJet 1 ε) χ) 0
        - (Real.sqrt 10 / 5) * χ ^ 2 * stumpffC ((2 / 5) * χ ^ 2)) 0 := by
    rw [← hrestFun]; exact hrest0
  have hzero :
      deriv (fun ε => univF (lineJet 1 ε) χ) 0
        - (Real.sqrt 10 / 5) * χ ^ 2 * stumpffC ((2 / 5) * χ ^ 2) = 0 :=
    hasDerivAt_even_zero hrest1 (fun ε => rest_lineJet1_even ε χ)
  exact hf.congr_deriv (by linarith [hzero])

lemma hasDerivAt_chiOf_lineJet1 (t : ℝ) :
    HasDerivAt (fun ε => chiOf (lineJet 1 ε) t)
      (-(2 / 5) * ((Real.sqrt 10 / 5) * (2 * t / 5) ^ 2 *
        stumpffC ((2 / 5) * (2 * t / 5) ^ 2))) 0 :=
  hasDerivAt_chiOf_axis_gen t (hasDerivAt_univF_lineJet1_fixed (2 * t / 5))

lemma sigmaOf_lineJet3 (ε : ℝ) : sigmaOf (lineJet 3 ε) = (5 / 2) * ε :=
  vecDot_lineJet3 ε

lemma velNormSq_lineJet3 (ε : ℝ) :
    ‖stateVel (lineJet 3 ε)‖ ^ 2 = ε ^ 2 + 2 / 5 := by
  rw [stateVel_lineJet3, ofCoords_norm]
  have hnn : (0 : ℝ) ≤ ε ^ 2 + (Real.sqrt 10 / 5) ^ 2 + 0 ^ 2 := by positivity
  rw [Real.sq_sqrt hnn]
  have hs : (Real.sqrt 10 / 5) ^ 2 = 2 / 5 := by
    field_simp
    rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 10)]
    norm_num
  rw [hs]
  ring

lemma alphaOf_lineJet3 (ε : ℝ) : alphaOf (lineJet 3 ε) = 2 / 5 - ε ^ 2 := by
  simp [alphaOf, rnorm_lineJet3, velNormSq_lineJet3]
  ring

lemma one_sub_alpha_r_lineJet3 (ε : ℝ) :
    1 - alphaOf (lineJet 3 ε) * rnorm (lineJet 3 ε) = (5 / 2) * ε ^ 2 := by
  rw [alphaOf_lineJet3, rnorm_lineJet3]
  ring

lemma univF_odd_lineJet3 (ε χ : ℝ) :
    univF (lineJet 3 ε) χ
      - ((1 - alphaOf (lineJet 3 ε) * rnorm (lineJet 3 ε)) * χ ^ 3
          * stumpffS (alphaOf (lineJet 3 ε) * χ ^ 2)
        + rnorm (lineJet 3 ε) * χ)
      = ε * ((5 / 2) * χ ^ 2 * stumpffC (alphaOf (lineJet 3 ε) * χ ^ 2)) := by
  simp [univF, sigmaOf_lineJet3]
  ring

lemma rest_lineJet3_even (ε χ : ℝ) :
    (1 - alphaOf (lineJet 3 (-ε)) * rnorm (lineJet 3 (-ε))) * χ ^ 3
        * stumpffS (alphaOf (lineJet 3 (-ε)) * χ ^ 2)
      + rnorm (lineJet 3 (-ε)) * χ
      = (1 - alphaOf (lineJet 3 ε) * rnorm (lineJet 3 ε)) * χ ^ 3
          * stumpffS (alphaOf (lineJet 3 ε) * χ ^ 2)
        + rnorm (lineJet 3 ε) * χ := by
  simp [alphaOf_lineJet3, rnorm_lineJet3]

lemma continuousAt_alphaOf_lineJet3 :
    ContinuousAt (fun ε => alphaOf (lineJet 3 ε)) 0 := by
  have h : ContinuousAt (fun ε : ℝ => 2 / 5 - ε ^ 2) 0 := by fun_prop
  exact h.congr (Eventually.of_forall fun ε => (alphaOf_lineJet3 ε).symm)

lemma eventually_alpha_lineJet3_nonneg (χ : ℝ) :
    ∀ᶠ ε : ℝ in 𝓝 0, 0 ≤ alphaOf (lineJet 3 ε) * χ ^ 2 := by
  have hα : ContinuousAt (fun ε => alphaOf (lineJet 3 ε)) 0 :=
    continuousAt_alphaOf_lineJet3
  have hα0 : 0 < alphaOf (lineJet 3 0) := by
    rw [lineJet_zero, alphaOf_sStar]; norm_num
  have hpos : ∀ᶠ ε : ℝ in 𝓝 0, 0 < alphaOf (lineJet 3 ε) :=
    hα.tendsto.eventually (Ioi_mem_nhds hα0)
  exact hpos.mono fun ε h => mul_nonneg h.le (sq_nonneg _)

lemma continuousAt_stumpffC_alpha_lineJet3 (χ : ℝ) :
    ContinuousAt (fun ε => stumpffC (alphaOf (lineJet 3 ε) * χ ^ 2)) 0 := by
  have hmul : ContinuousAt (fun ε => alphaOf (lineJet 3 ε) * χ ^ 2) 0 :=
    continuousAt_alphaOf_lineJet3.mul_const _
  have hcongr :
      (fun ε => stumpffC (alphaOf (lineJet 3 ε) * χ ^ 2)) =ᶠ[𝓝 0]
        fun ε => cbar (Real.sqrt (alphaOf (lineJet 3 ε) * χ ^ 2)) :=
    (eventually_alpha_lineJet3_nonneg χ).mono fun ε hz => stumpffC_eq_cbar hz
  have hinner :
      ContinuousAt (fun ε => cbar (Real.sqrt (alphaOf (lineJet 3 ε) * χ ^ 2))) 0 :=
    (continuous_cbar.comp Real.continuous_sqrt).continuousAt.comp hmul
  exact hinner.congr hcongr.symm

lemma hasDerivAt_univF_lineJet3_fixed (χ : ℝ) :
    HasDerivAt (fun ε => univF (lineJet 3 ε) χ)
      ((5 / 2) * χ ^ 2 * stumpffC ((2 / 5) * χ ^ 2)) 0 := by
  have hg : ContinuousAt
      (fun ε => (5 / 2) * χ ^ 2 * stumpffC (alphaOf (lineJet 3 ε) * χ ^ 2)) 0 :=
    (continuousAt_stumpffC_alpha_lineJet3 χ).const_mul _
  have hy :
      (5 / 2) * χ ^ 2 * stumpffC (alphaOf (lineJet 3 0) * χ ^ 2)
        = (5 / 2) * χ ^ 2 * stumpffC ((2 / 5) * χ ^ 2) := by
    rw [lineJet_zero, alphaOf_sStar]
  have hodd := hasDerivAt_mul_continuousAt hg hy
  have hf := (differentiableAt_univF_lineJet 3 χ).hasDerivAt
  have hrest0 : HasDerivAt
      (fun ε => univF (lineJet 3 ε) χ
        - ε * ((5 / 2) * χ ^ 2 * stumpffC (alphaOf (lineJet 3 ε) * χ ^ 2)))
      (deriv (fun ε => univF (lineJet 3 ε) χ) 0
        - (5 / 2) * χ ^ 2 * stumpffC ((2 / 5) * χ ^ 2)) 0 :=
    hf.sub hodd
  have hrestFun :
      (fun ε => univF (lineJet 3 ε) χ
        - ε * ((5 / 2) * χ ^ 2 * stumpffC (alphaOf (lineJet 3 ε) * χ ^ 2)))
      = fun ε =>
        (1 - alphaOf (lineJet 3 ε) * rnorm (lineJet 3 ε)) * χ ^ 3
          * stumpffS (alphaOf (lineJet 3 ε) * χ ^ 2)
        + rnorm (lineJet 3 ε) * χ := by
    funext ε; linarith [univF_odd_lineJet3 ε χ]
  have hrest1 : HasDerivAt
      (fun ε =>
        (1 - alphaOf (lineJet 3 ε) * rnorm (lineJet 3 ε)) * χ ^ 3
          * stumpffS (alphaOf (lineJet 3 ε) * χ ^ 2)
        + rnorm (lineJet 3 ε) * χ)
      (deriv (fun ε => univF (lineJet 3 ε) χ) 0
        - (5 / 2) * χ ^ 2 * stumpffC ((2 / 5) * χ ^ 2)) 0 := by
    rw [← hrestFun]; exact hrest0
  have hzero :
      deriv (fun ε => univF (lineJet 3 ε) χ) 0
        - (5 / 2) * χ ^ 2 * stumpffC ((2 / 5) * χ ^ 2) = 0 :=
    hasDerivAt_even_zero hrest1 (fun ε => rest_lineJet3_even ε χ)
  exact hf.congr_deriv (by linarith [hzero])

lemma hasDerivAt_chiOf_lineJet3 (t : ℝ) :
    HasDerivAt (fun ε => chiOf (lineJet 3 ε) t)
      (-(2 / 5) * ((5 / 2) * (2 * t / 5) ^ 2 *
        stumpffC ((2 / 5) * (2 * t / 5) ^ 2))) 0 :=
  hasDerivAt_chiOf_axis_gen t (hasDerivAt_univF_lineJet3_fixed (2 * t / 5))

lemma sigmaOf_lineJet4 (ε : ℝ) : sigmaOf (lineJet 4 ε) = 0 :=
  vecDot_lineJet4 ε

lemma velNormSq_lineJet4 (ε : ℝ) :
    ‖stateVel (lineJet 4 ε)‖ ^ 2 =
      2 / 5 + 2 * (Real.sqrt 10 / 5) * ε + ε ^ 2 := by
  rw [stateVel_lineJet4, ofCoords_norm]
  have hnn : (0 : ℝ) ≤ 0 ^ 2 + (Real.sqrt 10 / 5 + ε) ^ 2 + 0 ^ 2 := by positivity
  rw [Real.sq_sqrt hnn]
  have hs : Real.sqrt 10 ^ 2 = 10 := Real.sq_sqrt (by norm_num)
  ring_nf
  rw [hs]
  ring

lemma alphaOf_lineJet4 (ε : ℝ) :
    alphaOf (lineJet 4 ε) =
      2 / 5 - 2 * (Real.sqrt 10 / 5) * ε - ε ^ 2 := by
  simp [alphaOf, rnorm_lineJet4, velNormSq_lineJet4]
  ring

lemma one_sub_alpha_r_lineJet4 (ε : ℝ) :
    1 - alphaOf (lineJet 4 ε) * rnorm (lineJet 4 ε) =
      Real.sqrt 10 * ε + (5 / 2) * ε ^ 2 := by
  rw [alphaOf_lineJet4, rnorm_lineJet4]
  ring

lemma univF_lineJet4 (ε χ : ℝ) :
    univF (lineJet 4 ε) χ =
      (Real.sqrt 10 * ε + (5 / 2) * ε ^ 2) * χ ^ 3
        * stumpffS (alphaOf (lineJet 4 ε) * χ ^ 2)
        + (5 / 2) * χ := by
  rw [univF, sigmaOf_lineJet4, one_sub_alpha_r_lineJet4, rnorm_lineJet4]
  ring

lemma continuousAt_alphaOf_lineJet4 :
    ContinuousAt (fun ε => alphaOf (lineJet 4 ε)) 0 := by
  have h : ContinuousAt
      (fun ε : ℝ => 2 / 5 - 2 * (Real.sqrt 10 / 5) * ε - ε ^ 2) 0 := by fun_prop
  exact h.congr (Eventually.of_forall fun ε => (alphaOf_lineJet4 ε).symm)

lemma eventually_alpha_lineJet4_nonneg (χ : ℝ) :
    ∀ᶠ ε : ℝ in 𝓝 0, 0 ≤ alphaOf (lineJet 4 ε) * χ ^ 2 := by
  have hα : ContinuousAt (fun ε => alphaOf (lineJet 4 ε)) 0 :=
    continuousAt_alphaOf_lineJet4
  have hα0 : 0 < alphaOf (lineJet 4 0) := by
    rw [lineJet_zero, alphaOf_sStar]; norm_num
  have hpos : ∀ᶠ ε : ℝ in 𝓝 0, 0 < alphaOf (lineJet 4 ε) :=
    hα.tendsto.eventually (Ioi_mem_nhds hα0)
  exact hpos.mono fun ε h => mul_nonneg h.le (sq_nonneg _)

lemma continuousAt_stumpffS_alpha_lineJet4 (χ : ℝ) :
    ContinuousAt (fun ε => stumpffS (alphaOf (lineJet 4 ε) * χ ^ 2)) 0 := by
  have hmul : ContinuousAt (fun ε => alphaOf (lineJet 4 ε) * χ ^ 2) 0 :=
    continuousAt_alphaOf_lineJet4.mul_const _
  have hcongr :
      (fun ε => stumpffS (alphaOf (lineJet 4 ε) * χ ^ 2)) =ᶠ[𝓝 0]
        fun ε => sbar (Real.sqrt (alphaOf (lineJet 4 ε) * χ ^ 2)) :=
    (eventually_alpha_lineJet4_nonneg χ).mono fun ε hz => stumpffS_eq_sbar hz
  have hinner :
      ContinuousAt (fun ε => sbar (Real.sqrt (alphaOf (lineJet 4 ε) * χ ^ 2))) 0 :=
    (continuous_sbar.comp Real.continuous_sqrt).continuousAt.comp hmul
  exact hinner.congr hcongr.symm

lemma hasDerivAt_sq_mul_continuousAt {g : ℝ → ℝ}
    (hg : ContinuousAt g 0) :
    HasDerivAt (fun ε => ε ^ 2 * g ε) 0 0 := by
  have hεg : ContinuousAt (fun ε => ε * g ε) 0 :=
    continuousAt_id.mul hg
  have hy : (fun ε => ε * g ε) 0 = 0 := by simp
  have h := hasDerivAt_mul_continuousAt hεg hy
  refine h.congr_of_eventuallyEq (Eventually.of_forall fun ε => ?_)
  ring

lemma hasDerivAt_univF_lineJet4_fixed (χ : ℝ) :
    HasDerivAt (fun ε => univF (lineJet 4 ε) χ)
      (Real.sqrt 10 * χ ^ 3 * stumpffS ((2 / 5) * χ ^ 2)) 0 := by
  have hg : ContinuousAt
      (fun ε => Real.sqrt 10 * χ ^ 3 *
        stumpffS (alphaOf (lineJet 4 ε) * χ ^ 2)) 0 :=
    (continuousAt_stumpffS_alpha_lineJet4 χ).const_mul _
  have hy :
      Real.sqrt 10 * χ ^ 3 * stumpffS (alphaOf (lineJet 4 0) * χ ^ 2)
        = Real.sqrt 10 * χ ^ 3 * stumpffS ((2 / 5) * χ ^ 2) := by
    rw [lineJet_zero, alphaOf_sStar]
  have hlin := hasDerivAt_mul_continuousAt hg hy
  have hsqg : ContinuousAt
      (fun ε => (5 / 2) * χ ^ 3 * stumpffS (alphaOf (lineJet 4 ε) * χ ^ 2)) 0 :=
    (continuousAt_stumpffS_alpha_lineJet4 χ).const_mul _
  have hsq := hasDerivAt_sq_mul_continuousAt hsqg
  have hconst : HasDerivAt (fun _ : ℝ => (5 / 2 : ℝ) * χ) 0 0 :=
    hasDerivAt_const _ _
  have hsum := (hlin.add hsq).add hconst
  have heq : (fun ε => univF (lineJet 4 ε) χ) =ᶠ[𝓝 0]
      fun ε =>
        ε * (Real.sqrt 10 * χ ^ 3 * stumpffS (alphaOf (lineJet 4 ε) * χ ^ 2))
          + ε ^ 2 * ((5 / 2) * χ ^ 3 * stumpffS (alphaOf (lineJet 4 ε) * χ ^ 2))
          + (5 / 2) * χ := by
    refine Eventually.of_forall fun ε => ?_
    convert univF_lineJet4 ε χ using 1
    ring
  exact (hsum.congr_deriv (by ring)).congr_of_eventuallyEq heq

lemma hasDerivAt_chiOf_lineJet4 (t : ℝ) :
    HasDerivAt (fun ε => chiOf (lineJet 4 ε) t)
      (-(2 / 5) * (Real.sqrt 10 * (2 * t / 5) ^ 3 *
        stumpffS ((2 / 5) * (2 * t / 5) ^ 2))) 0 :=
  hasDerivAt_chiOf_axis_gen t (hasDerivAt_univF_lineJet4_fixed (2 * t / 5))

lemma omegaChi : Real.sqrt 10 / 5 = nStar * (5 / 2) := by
  rw [nStar, meanMotion_eq]
  ring

lemma fg_f_sStar_chi (χ : ℝ) :
    fg_f sStar χ = Real.cos ((Real.sqrt 10 / 5) * χ) := by
  have h := fg_f_sStar (5 / 2 * χ)
  have hχ : 2 * (5 / 2 * χ) / 5 = χ := by ring
  rw [hχ] at h
  rw [h]
  have heq : Real.sqrt (8 / 125) * (5 / 2 * χ) = (Real.sqrt 10 / 5) * χ := by
    calc
      Real.sqrt (8 / 125) * (5 / 2 * χ)
          = nStar * (5 / 2 * χ) := by rw [nStar]
      _ = (nStar * (5 / 2)) * χ := by ring
      _ = (Real.sqrt 10 / 5) * χ := by rw [← omegaChi]
  rw [heq]

lemma fg_g_sStar_chi (t χ : ℝ) :
    fg_g sStar t χ =
      t - (5 / 2) * χ + Real.sin ((Real.sqrt 10 / 5) * χ) / nStar := by
  have h := fg_g_sStar (5 / 2 * χ)
  have hχ : 2 * (5 / 2 * χ) / 5 = χ := by ring
  rw [hχ] at h
  have heq : Real.sqrt (8 / 125) * (5 / 2 * χ) = (Real.sqrt 10 / 5) * χ := by
    calc
      Real.sqrt (8 / 125) * (5 / 2 * χ)
          = nStar * (5 / 2 * χ) := by rw [nStar]
      _ = (nStar * (5 / 2)) * χ := by ring
      _ = (Real.sqrt 10 / 5) * χ := by rw [← omegaChi]
  have : fg_g sStar (5 / 2 * χ) χ =
      (5 / 2) * χ - χ ^ 3 * stumpffS (alphaOf sStar * χ ^ 2) := rfl
  have hS : χ ^ 3 * stumpffS (alphaOf sStar * χ ^ 2) =
      (5 / 2) * χ - Real.sin ((Real.sqrt 10 / 5) * χ) / nStar := by
    rw [this] at h
    rw [heq, show Real.sqrt (8 / 125) = nStar from rfl] at h
    linarith [h]
  simp [fg_g]
  linarith [hS]

lemma hasDerivAt_omega_mul (χ : ℝ) :
    HasDerivAt (fun ξ : ℝ => (Real.sqrt 10 / 5) * ξ) (Real.sqrt 10 / 5) χ := by
  simpa using (hasDerivAt_id χ).const_mul (Real.sqrt 10 / 5)

lemma hasDerivAt_fg_f_sStar (χ : ℝ) :
    HasDerivAt (fun ξ => fg_f sStar ξ)
      (-Real.sin ((Real.sqrt 10 / 5) * χ) * (Real.sqrt 10 / 5)) χ := by
  have heq : (fun ξ => fg_f sStar ξ) = fun ξ => Real.cos ((Real.sqrt 10 / 5) * ξ) :=
    funext fg_f_sStar_chi
  rw [heq]
  exact ((Real.hasDerivAt_cos ((Real.sqrt 10 / 5) * χ)).comp χ
    (hasDerivAt_omega_mul χ)).congr_deriv (by ring)

lemma hasDerivAt_fg_g_sStar (t χ : ℝ) :
    HasDerivAt (fun ξ => fg_g sStar t ξ)
      (-(5 / 2) + Real.cos ((Real.sqrt 10 / 5) * χ) * (Real.sqrt 10 / 5) / nStar) χ := by
  have heq :
      (fun ξ => fg_g sStar t ξ) =
        (fun ξ => t - (5 / 2) * ξ) +
          fun ξ => Real.sin ((Real.sqrt 10 / 5) * ξ) / nStar := by
    funext ξ
    simp [fg_g_sStar_chi t ξ, Pi.add_apply]
  rw [heq]
  have h52 : HasDerivAt (fun ξ : ℝ => ξ * (5 / 2)) (5 / 2) χ := by
    simpa using (hasDerivAt_id χ).mul_const (5 / 2 : ℝ)
  have hid : HasDerivAt (fun ξ : ℝ => t - ξ * (5 / 2)) (-(5 / 2)) χ :=
    ((hasDerivAt_const χ t).sub h52).congr_deriv (by ring)
  have hid' : HasDerivAt (fun ξ : ℝ => t - (5 / 2) * ξ) (-(5 / 2)) χ :=
    hid.congr_of_eventuallyEq (Eventually.of_forall fun ξ => by ring)
  have hsin := (Real.hasDerivAt_sin ((Real.sqrt 10 / 5) * χ)).comp χ
    (hasDerivAt_omega_mul χ)
  have hdiv : HasDerivAt
      (fun ξ => Real.sin ((Real.sqrt 10 / 5) * ξ) / nStar)
      (Real.cos ((Real.sqrt 10 / 5) * χ) * (Real.sqrt 10 / 5) / nStar) χ :=
    (hsin.div_const nStar).congr_deriv (by ring)
  exact hid'.add hdiv

lemma fderiv_uncurry_fg_f_inr (χ0 c : ℝ) :
    fderiv ℝ (fun p : (Fin 6 → ℝ) × ℝ => fg_f p.1 p.2) (sStar, χ0) (0, c) =
      c * deriv (fun ξ => fg_f sStar ξ) χ0 := by
  have hF : HasFDerivAt (fun p : (Fin 6 → ℝ) × ℝ => fg_f p.1 p.2)
      (fderiv ℝ (fun p : (Fin 6 → ℝ) × ℝ => fg_f p.1 p.2) (sStar, χ0))
      (sStar, χ0) :=
    ((contDiffAt_fg_f_unc χ0).differentiableAt (by decide)).hasFDerivAt
  have hpath : HasDerivAt (fun ξ : ℝ => (sStar, ξ)) ((0 : Fin 6 → ℝ), (1 : ℝ)) χ0 :=
    (hasDerivAt_const χ0 sStar).prodMk (hasDerivAt_id χ0)
  have hcomp := hF.comp_hasDerivAt χ0 hpath
  have huniq := hcomp.unique (hasDerivAt_fg_f_sStar χ0)
  have hlin1 :
      fderiv ℝ (fun p : (Fin 6 → ℝ) × ℝ => fg_f p.1 p.2) (sStar, χ0) (0, 1)
        = deriv (fun ξ => fg_f sStar ξ) χ0 := by
    rw [(hasDerivAt_fg_f_sStar χ0).deriv]
    simpa using huniq
  have hmap :=
    map_smul (fderiv ℝ (fun p : (Fin 6 → ℝ) × ℝ => fg_f p.1 p.2) (sStar, χ0)) c
      ((0 : Fin 6 → ℝ), (1 : ℝ))
  have hsc : (c : ℝ) • ((0 : Fin 6 → ℝ), (1 : ℝ)) = ((0 : Fin 6 → ℝ), c) := by
    simp [Prod.smul_def]
  rw [← hsc, hmap, hlin1, smul_eq_mul]

lemma fderiv_uncurry_fg_g_inr (t χ0 c : ℝ) :
    fderiv ℝ (fun p : (Fin 6 → ℝ) × ℝ => fg_g p.1 t p.2) (sStar, χ0) (0, c) =
      c * deriv (fun ξ => fg_g sStar t ξ) χ0 := by
  have hF : HasFDerivAt (fun p : (Fin 6 → ℝ) × ℝ => fg_g p.1 t p.2)
      (fderiv ℝ (fun p : (Fin 6 → ℝ) × ℝ => fg_g p.1 t p.2) (sStar, χ0))
      (sStar, χ0) :=
    ((contDiffAt_fg_g_unc t χ0).differentiableAt (by decide)).hasFDerivAt
  have hpath : HasDerivAt (fun ξ : ℝ => (sStar, ξ)) ((0 : Fin 6 → ℝ), (1 : ℝ)) χ0 :=
    (hasDerivAt_const χ0 sStar).prodMk (hasDerivAt_id χ0)
  have hcomp := hF.comp_hasDerivAt χ0 hpath
  have huniq := hcomp.unique (hasDerivAt_fg_g_sStar t χ0)
  have hlin1 :
      fderiv ℝ (fun p : (Fin 6 → ℝ) × ℝ => fg_g p.1 t p.2) (sStar, χ0) (0, 1)
        = deriv (fun ξ => fg_g sStar t ξ) χ0 := by
    rw [(hasDerivAt_fg_g_sStar t χ0).deriv]
    simpa using huniq
  have hmap :=
    map_smul (fderiv ℝ (fun p : (Fin 6 → ℝ) × ℝ => fg_g p.1 t p.2) (sStar, χ0)) c
      ((0 : Fin 6 → ℝ), (1 : ℝ))
  have hsc : (c : ℝ) • ((0 : Fin 6 → ℝ), (1 : ℝ)) = ((0 : Fin 6 → ℝ), c) := by
    simp [Prod.smul_def]
  rw [← hsc, hmap, hlin1, smul_eq_mul]

lemma hasDerivAt_fg_f_chiOf_gen {j : Fin 6} (t : ℝ) {Ff χ' : ℝ}
    (hχ : HasDerivAt (fun ε => chiOf (lineJet j ε) t) χ' 0)
    (hfixed : HasDerivAt (fun ε => fg_f (lineJet j ε) (2 * t / 5)) Ff 0) :
    HasDerivAt (fun ε => fg_f (lineJet j ε) (chiOf (lineJet j ε) t))
      (Ff + χ' * deriv (fun ξ => fg_f sStar ξ) (2 * t / 5)) 0 := by
  have hU : ContDiffAt ℝ ⊤ (fun p : (Fin 6 → ℝ) × ℝ => fg_f p.1 p.2)
      (sStar, 2 * t / 5) :=
    contDiffAt_fg_f_unc (2 * t / 5)
  have hF : HasFDerivAt (fun p : (Fin 6 → ℝ) × ℝ => fg_f p.1 p.2)
      (fderiv ℝ (fun p : (Fin 6 → ℝ) × ℝ => fg_f p.1 p.2) (sStar, 2 * t / 5))
      (sStar, 2 * t / 5) :=
    (hU.differentiableAt (by decide)).hasFDerivAt
  have hpath : HasDerivAt (fun ε => (lineJet j ε, chiOf (lineJet j ε) t))
      (Pi.single j (1 : ℝ), χ') 0 :=
    (hasDerivAt_lineJet j 0).prodMk hχ
  have hFpath : HasFDerivAt (fun p : (Fin 6 → ℝ) × ℝ => fg_f p.1 p.2)
      (fderiv ℝ (fun p : (Fin 6 → ℝ) × ℝ => fg_f p.1 p.2)
        (lineJet j 0, chiOf (lineJet j 0) t))
      (lineJet j 0, chiOf (lineJet j 0) t) := by
    rw [lineJet_zero, chiOf_sStar]; exact hF
  have hcomp := hFpath.comp_hasDerivAt 0 hpath
  have hpair0 := hasDerivAt_pair_lineJet_const j (2 * t / 5) 0
  have hF0 : HasFDerivAt (fun p : (Fin 6 → ℝ) × ℝ => fg_f p.1 p.2)
      (fderiv ℝ (fun p : (Fin 6 → ℝ) × ℝ => fg_f p.1 p.2) (lineJet j 0, 2 * t / 5))
      (lineJet j 0, 2 * t / 5) := by
    rw [lineJet_zero]; exact hF
  have hcomp0 := hF0.comp_hasDerivAt 0 hpair0
  have hpt : (lineJet j 0, chiOf (lineJet j 0) t) = (sStar, 2 * t / 5) := by
    simp [lineJet_zero, chiOf_sStar]
  have hlin :
      fderiv ℝ (fun p : (Fin 6 → ℝ) × ℝ => fg_f p.1 p.2) (sStar, 2 * t / 5)
        (Pi.single j 1, χ')
        = Ff + χ' * deriv (fun ξ => fg_f sStar ξ) (2 * t / 5) := by
    have hL :=
      map_add (fderiv ℝ (fun p : (Fin 6 → ℝ) × ℝ => fg_f p.1 p.2) (sStar, 2 * t / 5))
        (Pi.single j (1 : ℝ), (0 : ℝ)) (0, χ')
    have hadd : (Pi.single j (1 : ℝ), (0 : ℝ)) + ((0 : Fin 6 → ℝ), χ')
        = (Pi.single j (1 : ℝ), χ') := by
      apply Prod.ext <;> simp
    have h0 :
        fderiv ℝ (fun p : (Fin 6 → ℝ) × ℝ => fg_f p.1 p.2) (sStar, 2 * t / 5)
          (Pi.single j 1, (0 : ℝ)) = Ff := by
      have hpt0 : lineJet j 0 = sStar := lineJet_zero j
      simpa [hpt0] using hcomp0.unique hfixed
    have hinr := fderiv_uncurry_fg_f_inr (2 * t / 5) χ'
    rw [← hadd, hL, h0, hinr]
  rw [hpt] at hcomp
  exact hcomp.congr_deriv hlin

lemma hasDerivAt_fg_g_chiOf_gen {j : Fin 6} (t : ℝ) {Fg χ' : ℝ}
    (hχ : HasDerivAt (fun ε => chiOf (lineJet j ε) t) χ' 0)
    (hfixed : HasDerivAt (fun ε => fg_g (lineJet j ε) t (2 * t / 5)) Fg 0) :
    HasDerivAt (fun ε => fg_g (lineJet j ε) t (chiOf (lineJet j ε) t))
      (Fg + χ' * deriv (fun ξ => fg_g sStar t ξ) (2 * t / 5)) 0 := by
  have hU : ContDiffAt ℝ ⊤ (fun p : (Fin 6 → ℝ) × ℝ => fg_g p.1 t p.2)
      (sStar, 2 * t / 5) :=
    contDiffAt_fg_g_unc t (2 * t / 5)
  have hF : HasFDerivAt (fun p : (Fin 6 → ℝ) × ℝ => fg_g p.1 t p.2)
      (fderiv ℝ (fun p : (Fin 6 → ℝ) × ℝ => fg_g p.1 t p.2) (sStar, 2 * t / 5))
      (sStar, 2 * t / 5) :=
    (hU.differentiableAt (by decide)).hasFDerivAt
  have hpath : HasDerivAt (fun ε => (lineJet j ε, chiOf (lineJet j ε) t))
      (Pi.single j (1 : ℝ), χ') 0 :=
    (hasDerivAt_lineJet j 0).prodMk hχ
  have hFpath : HasFDerivAt (fun p : (Fin 6 → ℝ) × ℝ => fg_g p.1 t p.2)
      (fderiv ℝ (fun p : (Fin 6 → ℝ) × ℝ => fg_g p.1 t p.2)
        (lineJet j 0, chiOf (lineJet j 0) t))
      (lineJet j 0, chiOf (lineJet j 0) t) := by
    rw [lineJet_zero, chiOf_sStar]; exact hF
  have hcomp := hFpath.comp_hasDerivAt 0 hpath
  have hpair0 := hasDerivAt_pair_lineJet_const j (2 * t / 5) 0
  have hF0 : HasFDerivAt (fun p : (Fin 6 → ℝ) × ℝ => fg_g p.1 t p.2)
      (fderiv ℝ (fun p : (Fin 6 → ℝ) × ℝ => fg_g p.1 t p.2) (lineJet j 0, 2 * t / 5))
      (lineJet j 0, 2 * t / 5) := by
    rw [lineJet_zero]; exact hF
  have hcomp0 := hF0.comp_hasDerivAt 0 hpair0
  have hpt : (lineJet j 0, chiOf (lineJet j 0) t) = (sStar, 2 * t / 5) := by
    simp [lineJet_zero, chiOf_sStar]
  have hlin :
      fderiv ℝ (fun p : (Fin 6 → ℝ) × ℝ => fg_g p.1 t p.2) (sStar, 2 * t / 5)
        (Pi.single j 1, χ')
        = Fg + χ' * deriv (fun ξ => fg_g sStar t ξ) (2 * t / 5) := by
    have hL :=
      map_add (fderiv ℝ (fun p : (Fin 6 → ℝ) × ℝ => fg_g p.1 t p.2) (sStar, 2 * t / 5))
        (Pi.single j (1 : ℝ), (0 : ℝ)) (0, χ')
    have hadd : (Pi.single j (1 : ℝ), (0 : ℝ)) + ((0 : Fin 6 → ℝ), χ')
        = (Pi.single j (1 : ℝ), χ') := by
      apply Prod.ext <;> simp
    have h0 :
        fderiv ℝ (fun p : (Fin 6 → ℝ) × ℝ => fg_g p.1 t p.2) (sStar, 2 * t / 5)
          (Pi.single j 1, (0 : ℝ)) = Fg := by
      have hpt0 : lineJet j 0 = sStar := lineJet_zero j
      simpa [hpt0] using hcomp0.unique hfixed
    have hinr := fderiv_uncurry_fg_g_inr t (2 * t / 5) χ'
    rw [← hadd, hL, h0, hinr]
  rw [hpt] at hcomp
  exact hcomp.congr_deriv hlin

lemma fg_f_lineJet1_even (χ ε : ℝ) :
    fg_f (lineJet 1 (-ε)) χ = fg_f (lineJet 1 ε) χ := by
  simp [fg_f, alphaOf_lineJet1, rnorm_lineJet1]

lemma fg_g_lineJet1_even (t χ ε : ℝ) :
    fg_g (lineJet 1 (-ε)) t χ = fg_g (lineJet 1 ε) t χ := by
  simp [fg_g, alphaOf_lineJet1, rnorm_lineJet1]

lemma hasDerivAt_fg_f_lineJet1_fixed (χ : ℝ) :
    HasDerivAt (fun ε => fg_f (lineJet 1 ε) χ) 0 0 := by
  have hf := (differentiableAt_fg_f_lineJet 1 χ).hasDerivAt
  exact hf.congr_deriv (hasDerivAt_even_zero hf (fg_f_lineJet1_even χ))

lemma hasDerivAt_fg_g_lineJet1_fixed (t χ : ℝ) :
    HasDerivAt (fun ε => fg_g (lineJet 1 ε) t χ) 0 0 := by
  have hf := (differentiableAt_fg_g_lineJet 1 t χ).hasDerivAt
  exact hf.congr_deriv (hasDerivAt_even_zero hf (fg_g_lineJet1_even t χ))

lemma fg_f_lineJet3_even (χ ε : ℝ) :
    fg_f (lineJet 3 (-ε)) χ = fg_f (lineJet 3 ε) χ := by
  simp [fg_f, alphaOf_lineJet3, rnorm_lineJet3]

lemma fg_g_lineJet3_even (t χ ε : ℝ) :
    fg_g (lineJet 3 (-ε)) t χ = fg_g (lineJet 3 ε) t χ := by
  simp [fg_g, alphaOf_lineJet3]

lemma hasDerivAt_fg_f_lineJet3_fixed (χ : ℝ) :
    HasDerivAt (fun ε => fg_f (lineJet 3 ε) χ) 0 0 := by
  have hf := (differentiableAt_fg_f_lineJet 3 χ).hasDerivAt
  exact hf.congr_deriv (hasDerivAt_even_zero hf (fg_f_lineJet3_even χ))

lemma hasDerivAt_fg_g_lineJet3_fixed (t χ : ℝ) :
    HasDerivAt (fun ε => fg_g (lineJet 3 ε) t χ) 0 0 := by
  have hf := (differentiableAt_fg_g_lineJet 3 t χ).hasDerivAt
  exact hf.congr_deriv (hasDerivAt_even_zero hf (fg_g_lineJet3_even t χ))

lemma hasDerivAt_pos_lineJet3 :
    HasDerivAt (fun ε => statePos (lineJet 3 ε)) (0 : Vec) 0 := by
  have h := hasDerivAt_const (0 : ℝ) (ofCoords (5 / 2) 0 0)
  exact h.congr_of_eventuallyEq (Eventually.of_forall statePos_lineJet3)

lemma hasDerivAt_vel_lineJet3 :
    HasDerivAt (fun ε => stateVel (lineJet 3 ε)) eX 0 := by
  have h : HasDerivAt (fun ε => ofCoords ε (Real.sqrt 10 / 5) 0) (ofCoords 1 0 0) 0 :=
    hasDerivAt_coord3 (hasDerivAt_id (0 : ℝ))
      (hasDerivAt_const (0 : ℝ) (Real.sqrt 10 / 5)) (hasDerivAt_const (0 : ℝ) (0 : ℝ))
  have heq : (fun ε => stateVel (lineJet 3 ε)) = fun ε => ofCoords ε (Real.sqrt 10 / 5) 0 :=
    funext stateVel_lineJet3
  rw [heq, eX]
  exact h

lemma hasDerivAt_pos_lineJet0 :
    HasDerivAt (fun ε => statePos (lineJet 0 ε)) eX 0 := by
  have h : HasDerivAt (fun ε => ofCoords (5 / 2 + ε) 0 0) (ofCoords 1 0 0) 0 :=
    hasDerivAt_coord3 ((hasDerivAt_id (0 : ℝ)).const_add (5 / 2))
      (hasDerivAt_const (0 : ℝ) (0 : ℝ)) (hasDerivAt_const (0 : ℝ) (0 : ℝ))
  have heq : (fun ε => statePos (lineJet 0 ε)) = fun ε => ofCoords (5 / 2 + ε) 0 0 :=
    funext statePos_lineJet0
  rw [heq, eX]
  exact h.congr_deriv (by simp)

lemma hasDerivAt_vel_lineJet0 :
    HasDerivAt (fun ε => stateVel (lineJet 0 ε)) (0 : Vec) 0 := by
  have h := hasDerivAt_const (0 : ℝ) (ofCoords 0 (Real.sqrt 10 / 5) 0)
  exact h.congr_of_eventuallyEq (Eventually.of_forall stateVel_lineJet0)

lemma hasDerivAt_pos_lineJet4 :
    HasDerivAt (fun ε => statePos (lineJet 4 ε)) (0 : Vec) 0 := by
  have h := hasDerivAt_const (0 : ℝ) (ofCoords (5 / 2) 0 0)
  exact h.congr_of_eventuallyEq (Eventually.of_forall statePos_lineJet4)

lemma hasDerivAt_vel_lineJet4 :
    HasDerivAt (fun ε => stateVel (lineJet 4 ε)) eY 0 := by
  have h : HasDerivAt (fun ε => ofCoords 0 (Real.sqrt 10 / 5 + ε) 0) (ofCoords 0 1 0) 0 :=
    hasDerivAt_coord3 (hasDerivAt_const (0 : ℝ) (0 : ℝ))
      ((hasDerivAt_id (0 : ℝ)).const_add (Real.sqrt 10 / 5))
      (hasDerivAt_const (0 : ℝ) (0 : ℝ))
  have heq : (fun ε => stateVel (lineJet 4 ε)) =
      fun ε => ofCoords 0 (Real.sqrt 10 / 5 + ε) 0 :=
    funext stateVel_lineJet4
  rw [heq, eY]
  exact h

lemma sqrt_two_div_five : Real.sqrt (2 / 5) = Real.sqrt 10 / 5 := by
  have hnn : (0 : ℝ) ≤ Real.sqrt 10 / 5 := by positivity
  refine (Real.sqrt_eq_iff_mul_self_eq (by norm_num) hnn).2 ?_
  field_simp
  rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 10)]
  norm_num

lemma omega_mul_chi_sStar (t : ℝ) :
    (Real.sqrt 10 / 5) * (2 * t / 5) = nStar * t := by
  rw [omegaChi]
  ring

lemma chiSq_C_sStar (t : ℝ) :
    (2 * t / 5) ^ 2 * stumpffC ((2 / 5) * (2 * t / 5) ^ 2) =
      (5 / 2) * (1 - Real.cos (nStar * t)) := by
  have hα : (0 : ℝ) < 2 / 5 := by norm_num
  have h := chiSq_mul_stumpffC (χ := 2 * t / 5) hα
  have harg : Real.sqrt (2 / 5) * (2 * t / 5) = nStar * t := by
    rw [sqrt_two_div_five, omega_mul_chi_sStar]
  rw [h, harg]
  field_simp

lemma chiCube_S_sStar (t : ℝ) :
    (2 * t / 5) ^ 3 * stumpffS ((2 / 5) * (2 * t / 5) ^ 2) =
      t - Real.sin (nStar * t) / nStar := by
  have h := fg_g_sStar t
  have : t - (2 * t / 5) ^ 3 * stumpffS (alphaOf sStar * (2 * t / 5) ^ 2)
      = Real.sin (nStar * t) / nStar := by
    simpa [fg_g, nStar] using h
  have hz : alphaOf sStar * (2 * t / 5) ^ 2 = (2 / 5) * (2 * t / 5) ^ 2 := by
    rw [alphaOf_sStar]
  linarith [this, (by rw [hz] : (2 * t / 5) ^ 3 *
    stumpffS (alphaOf sStar * (2 * t / 5) ^ 2) =
      (2 * t / 5) ^ 3 * stumpffS ((2 / 5) * (2 * t / 5) ^ 2))]

lemma deriv_fg_f_sStar_at (t : ℝ) :
    deriv (fun ξ => fg_f sStar ξ) (2 * t / 5) =
      -Real.sin (nStar * t) * (Real.sqrt 10 / 5) := by
  rw [(hasDerivAt_fg_f_sStar (2 * t / 5)).deriv, omega_mul_chi_sStar]

lemma deriv_fg_g_sStar_at (t : ℝ) :
    deriv (fun ξ => fg_g sStar t ξ) (2 * t / 5) =
      (5 / 2) * (Real.cos (nStar * t) - 1) := by
  have h := (hasDerivAt_fg_g_sStar t (2 * t / 5)).deriv
  rw [h, omega_mul_chi_sStar]
  have hn := nStar_ne
  have hquot : (Real.sqrt 10 / 5) / nStar = 5 / 2 := by
    have hω := omegaChi
    field_simp [hn] at hω ⊢
    linarith [hω]
  calc
    -(5 / 2) + Real.cos (nStar * t) * (Real.sqrt 10 / 5) / nStar
        = -(5 / 2) + Real.cos (nStar * t) * ((Real.sqrt 10 / 5) / nStar) := by
          ring
    _ = -(5 / 2) + Real.cos (nStar * t) * (5 / 2) := by rw [hquot]
    _ = (5 / 2) * (Real.cos (nStar * t) - 1) := by ring

lemma inv_nStar : (1 / nStar) = 5 * Real.sqrt 10 / 4 := by
  have hn := nStar_ne
  rw [nStar, meanMotion_eq]
  have hs : Real.sqrt 10 ≠ 0 := Real.sqrt_ne_zero'.2 (by norm_num)
  field_simp [hn, hs]
  ring_nf
  simp [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 10)]
  norm_num

lemma five_sqrt10_div4 : (25 / 4) * (Real.sqrt 10 / 5) = 1 / nStar := by
  rw [inv_nStar]
  have hs : Real.sqrt 10 ≠ 0 := Real.sqrt_ne_zero'.2 (by norm_num)
  field_simp [hs]
  ring

lemma nStar_mul_sqrt10 : nStar * Real.sqrt 10 = 4 / 5 := by
  rw [nStar, meanMotion_eq]
  have hs : Real.sqrt 10 ≠ 0 := Real.sqrt_ne_zero'.2 (by norm_num)
  field_simp [hs]
  ring_nf
  simp [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 10)]
  norm_num

lemma chiPrime_lineJet3 (t : ℝ) :
    -(2 / 5) * ((5 / 2) * (2 * t / 5) ^ 2 * stumpffC ((2 / 5) * (2 * t / 5) ^ 2)) =
      -(5 / 2) * (1 - Real.cos (nStar * t)) := by
  have h := chiSq_C_sStar t
  calc
    -(2 / 5) * ((5 / 2) * (2 * t / 5) ^ 2 * stumpffC ((2 / 5) * (2 * t / 5) ^ 2))
        = -((2 * t / 5) ^ 2 * stumpffC ((2 / 5) * (2 * t / 5) ^ 2)) := by ring
    _ = -((5 / 2) * (1 - Real.cos (nStar * t))) := by rw [h]
    _ = -(5 / 2) * (1 - Real.cos (nStar * t)) := by ring

lemma hasDerivAt_chiOf_lineJet3' (t : ℝ) :
    HasDerivAt (fun ε => chiOf (lineJet 3 ε) t)
      (-(5 / 2) * (1 - Real.cos (nStar * t))) 0 :=
  (hasDerivAt_chiOf_lineJet3 t).congr_deriv (chiPrime_lineJet3 t)

lemma hasDerivAt_fg_f_chiOf_lineJet3 (t : ℝ) :
    HasDerivAt (fun ε => fg_f (lineJet 3 ε) (chiOf (lineJet 3 ε) t))
      ((5 / 2) * (1 - Real.cos (nStar * t)) * Real.sin (nStar * t) *
        (Real.sqrt 10 / 5)) 0 := by
  have h := hasDerivAt_fg_f_chiOf_gen t (hasDerivAt_chiOf_lineJet3' t)
    (hasDerivAt_fg_f_lineJet3_fixed (2 * t / 5))
  refine h.congr_deriv ?_
  rw [deriv_fg_f_sStar_at]
  ring

lemma hasDerivAt_fg_g_chiOf_lineJet3 (t : ℝ) :
    HasDerivAt (fun ε => fg_g (lineJet 3 ε) t (chiOf (lineJet 3 ε) t))
      ((25 / 4) * (1 - Real.cos (nStar * t)) ^ 2) 0 := by
  have h := hasDerivAt_fg_g_chiOf_gen t (hasDerivAt_chiOf_lineJet3' t)
    (hasDerivAt_fg_g_lineJet3_fixed t (2 * t / 5))
  refine h.congr_deriv ?_
  rw [deriv_fg_g_sStar_at]
  ring

lemma fg_f_sStar_n (t : ℝ) : fg_f sStar (2 * t / 5) = Real.cos (nStar * t) := by
  rw [nStar, fg_f_sStar]

lemma fg_g_sStar_n (t : ℝ) :
    fg_g sStar t (2 * t / 5) = Real.sin (nStar * t) / nStar := by
  rw [nStar, fg_g_sStar]

lemma stmInertial_ofCoords (t dx dy dvx dvy : ℝ) :
    stmInertial t dx dy dvx dvy =
      ofCoords
        (stmRad t dx dy dvx dvy * Real.cos (nStar * t)
          - stmTan t dx dy dvx dvy * Real.sin (nStar * t))
        (stmRad t dx dy dvx dvy * Real.sin (nStar * t)
          + stmTan t dx dy dvx dvy * Real.cos (nStar * t))
        0 := by
  simp [stmInertial, erOf, ethOf, ofCoords_smul, ofCoords_add]
  ring

lemma stmCol_dvx (t : ℝ) :
    stmCol 2 t =
      ofCoords
        (Real.sin (nStar * t) / nStar * Real.cos (nStar * t)
          + 2 * (1 - Real.cos (nStar * t)) * Real.sin (nStar * t) / nStar)
        (Real.sin (nStar * t) / nStar * Real.sin (nStar * t)
          - 2 * (1 - Real.cos (nStar * t)) * Real.cos (nStar * t) / nStar)
        0 := by
  simp [stmCol, stmInertial_ofCoords, stmRad, stmTan]
  ring

lemma axis3_vec_eq_stm (t : ℝ) :
    ((5 / 2) * (1 - Real.cos (nStar * t)) * Real.sin (nStar * t) *
        (Real.sqrt 10 / 5)) • ofCoords (5 / 2) 0 0 +
      ((25 / 4) * (1 - Real.cos (nStar * t)) ^ 2) • ofCoords 0 (Real.sqrt 10 / 5) 0 +
        (Real.sin (nStar * t) / nStar) • ofCoords 1 0 0
      = stmCol 2 t := by
  rw [ofCoords_smul, ofCoords_smul, ofCoords_smul, ofCoords_add, ofCoords_add,
    stmCol_dvx]
  apply (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).injective
  ext i
  fin_cases i
  · simp [ofCoords]
    have hn := nStar_ne
    have hs : Real.sqrt 10 ≠ 0 := Real.sqrt_ne_zero'.2 (by norm_num)
    have hns := nStar_mul_sqrt10
    field_simp [hn, hs]
    have : 5 * nStar * (1 - Real.cos (nStar * t)) * Real.sqrt 10
        = 5 * (4 / 5) * (1 - Real.cos (nStar * t)) := by
      calc
        5 * nStar * (1 - Real.cos (nStar * t)) * Real.sqrt 10
            = 5 * (nStar * Real.sqrt 10) * (1 - Real.cos (nStar * t)) := by ring
        _ = 5 * (4 / 5) * (1 - Real.cos (nStar * t)) := by rw [hns]
    rw [this]
    ring
  · simp [ofCoords]
    have hn := nStar_ne
    have hs : Real.sqrt 10 ≠ 0 := Real.sqrt_ne_zero'.2 (by norm_num)
    have hns := nStar_mul_sqrt10
    field_simp [hn, hs]
    have : 25 * nStar * (1 - Real.cos (nStar * t)) ^ 2 * Real.sqrt 10
        = 25 * (4 / 5) * (1 - Real.cos (nStar * t)) ^ 2 := by
      calc
        25 * nStar * (1 - Real.cos (nStar * t)) ^ 2 * Real.sqrt 10
            = 25 * (nStar * Real.sqrt 10) * (1 - Real.cos (nStar * t)) ^ 2 := by ring
        _ = 25 * (4 / 5) * (1 - Real.cos (nStar * t)) ^ 2 := by rw [hns]
    rw [this]
    have hsc : Real.sin (nStar * t) ^ 2 = 1 - Real.cos (nStar * t) ^ 2 := by
      linarith [Real.sin_sq_add_cos_sq (nStar * t)]
    rw [hsc]
    ring
  · simp [ofCoords]

lemma hasDerivAt_keplerIC_lineJet3 (t : ℝ) :
    HasDerivAt (fun ε => keplerIC (lineJet 3 ε) t) (stmCol 2 t) 0 := by
  have hf := hasDerivAt_fg_f_chiOf_lineJet3 t
  have hg := hasDerivAt_fg_g_chiOf_lineJet3 t
  have hp := hasDerivAt_pos_lineJet3
  have hv := hasDerivAt_vel_lineJet3
  have hsum := (hf.smul hp).add (hg.smul hv)
  have hf0 := fg_f_sStar_n t
  have hg0 := fg_g_sStar_n t
  have hvec :
      ((5 / 2) * (1 - Real.cos (nStar * t)) * Real.sin (nStar * t) *
            (Real.sqrt 10 / 5)) • statePos (lineJet 3 0) +
          fg_f (lineJet 3 0) (chiOf (lineJet 3 0) t) • (0 : Vec) +
          (((25 / 4) * (1 - Real.cos (nStar * t)) ^ 2) • stateVel (lineJet 3 0) +
            fg_g (lineJet 3 0) t (chiOf (lineJet 3 0) t) • eX)
        = stmCol 2 t := by
    simp [lineJet_zero, chiOf_sStar, hf0, hg0, sStar_pos, sStar_vel, eX, smul_zero]
    have h := axis3_vec_eq_stm t
    convert h using 1
    abel
  refine (hsum.congr_of_eventuallyEq
    (Eventually.of_forall fun ε => keplerIC_lineJet_apply 3 ε t)).congr_deriv ?_
  have hgoal :
      ((5 / 2) * (1 - Real.cos (nStar * t)) * Real.sin (nStar * t) *
            (Real.sqrt 10 / 5)) • statePos (lineJet 3 0) +
          fg_f (lineJet 3 0) (chiOf (lineJet 3 0) t) • (0 : Vec) +
          (fg_g (lineJet 3 0) t (chiOf (lineJet 3 0) t) • eX +
            ((25 / 4) * (1 - Real.cos (nStar * t)) ^ 2) • stateVel (lineJet 3 0))
        = stmCol 2 t := by
    simp [lineJet_zero, chiOf_sStar] at hvec ⊢
    convert hvec using 1
    abel
  simpa [lineJet_zero, chiOf_sStar] using hgoal

lemma chiPrime_lineJet1' (t : ℝ) :
    -(2 / 5) * ((Real.sqrt 10 / 5) * (2 * t / 5) ^ 2 *
        stumpffC ((2 / 5) * (2 * t / 5) ^ 2)) =
      -(Real.sqrt 10 / 5) * (1 - Real.cos (nStar * t)) := by
  have h := chiSq_C_sStar t
  calc
    -(2 / 5) * ((Real.sqrt 10 / 5) * (2 * t / 5) ^ 2 *
          stumpffC ((2 / 5) * (2 * t / 5) ^ 2))
        = -((2 / 5) * (Real.sqrt 10 / 5) *
            ((2 * t / 5) ^ 2 * stumpffC ((2 / 5) * (2 * t / 5) ^ 2))) := by ring
    _ = -((2 / 5) * (Real.sqrt 10 / 5) *
            ((5 / 2) * (1 - Real.cos (nStar * t)))) := by rw [h]
    _ = -(Real.sqrt 10 / 5) * (1 - Real.cos (nStar * t)) := by ring

lemma hasDerivAt_chiOf_lineJet1' (t : ℝ) :
    HasDerivAt (fun ε => chiOf (lineJet 1 ε) t)
      (-(Real.sqrt 10 / 5) * (1 - Real.cos (nStar * t))) 0 :=
  (hasDerivAt_chiOf_lineJet1 t).congr_deriv (chiPrime_lineJet1' t)

lemma sqrt10_div5_sq : (Real.sqrt 10 / 5) ^ 2 = 2 / 5 := by
  field_simp
  rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 10)]
  norm_num

lemma hasDerivAt_fg_f_chiOf_lineJet1 (t : ℝ) :
    HasDerivAt (fun ε => fg_f (lineJet 1 ε) (chiOf (lineJet 1 ε) t))
      ((2 / 5) * Real.sin (nStar * t) * (1 - Real.cos (nStar * t))) 0 := by
  have h := hasDerivAt_fg_f_chiOf_gen t (hasDerivAt_chiOf_lineJet1' t)
    (hasDerivAt_fg_f_lineJet1_fixed (2 * t / 5))
  refine h.congr_deriv ?_
  rw [deriv_fg_f_sStar_at]
  calc
    0 + (-(Real.sqrt 10 / 5) * (1 - Real.cos (nStar * t))) *
          (-Real.sin (nStar * t) * (Real.sqrt 10 / 5))
        = (Real.sqrt 10 / 5) ^ 2 * Real.sin (nStar * t) *
            (1 - Real.cos (nStar * t)) := by ring
    _ = (2 / 5) * Real.sin (nStar * t) * (1 - Real.cos (nStar * t)) := by
          rw [sqrt10_div5_sq]

lemma hasDerivAt_fg_g_chiOf_lineJet1 (t : ℝ) :
    HasDerivAt (fun ε => fg_g (lineJet 1 ε) t (chiOf (lineJet 1 ε) t))
      ((Real.sqrt 10 / 2) * (1 - Real.cos (nStar * t)) ^ 2) 0 := by
  have h := hasDerivAt_fg_g_chiOf_gen t (hasDerivAt_chiOf_lineJet1' t)
    (hasDerivAt_fg_g_lineJet1_fixed t (2 * t / 5))
  refine h.congr_deriv ?_
  rw [deriv_fg_g_sStar_at]
  ring

lemma stmCol_dy (t : ℝ) :
    stmCol 1 t =
      ofCoords
        (Real.sin (nStar * t) * (1 - Real.cos (nStar * t)))
        (1 - Real.cos (nStar * t) + Real.cos (nStar * t) ^ 2)
        0 := by
  have h := stmInertial_ofCoords t 0 1 0 0
  simp [stmCol, stmRad, stmTan] at h ⊢
  rw [h]
  apply (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).injective
  ext i
  fin_cases i
  · simp [ofCoords]; ring
  · simp [ofCoords]
    have hsc := Real.sin_sq_add_cos_sq (nStar * t)
    linarith [hsc]
  · simp [ofCoords]

lemma axis1_vec_eq_stm (t : ℝ) :
    ((2 / 5) * Real.sin (nStar * t) * (1 - Real.cos (nStar * t))) •
        ofCoords (5 / 2) 0 0 +
      Real.cos (nStar * t) • ofCoords 0 1 0 +
        ((Real.sqrt 10 / 2) * (1 - Real.cos (nStar * t)) ^ 2) •
          ofCoords 0 (Real.sqrt 10 / 5) 0
      = stmCol 1 t := by
  rw [ofCoords_smul, ofCoords_smul, ofCoords_smul, ofCoords_add, ofCoords_add,
    stmCol_dy]
  apply (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).injective
  ext i
  fin_cases i
  · simp [ofCoords]; ring
  · simp [ofCoords]
    have hs : Real.sqrt 10 ≠ 0 := Real.sqrt_ne_zero'.2 (by norm_num)
    field_simp [hs]
    rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 10)]
    ring
  · simp [ofCoords]

lemma hasDerivAt_keplerIC_lineJet1 (t : ℝ) :
    HasDerivAt (fun ε => keplerIC (lineJet 1 ε) t) (stmCol 1 t) 0 := by
  have hf := hasDerivAt_fg_f_chiOf_lineJet1 t
  have hg := hasDerivAt_fg_g_chiOf_lineJet1 t
  have hp := hasDerivAt_pos_lineJet1
  have hv := hasDerivAt_vel_lineJet1
  have hsum := (hf.smul hp).add (hg.smul hv)
  have hf0 := fg_f_sStar_n t
  refine (hsum.congr_of_eventuallyEq
    (Eventually.of_forall fun ε => keplerIC_lineJet_apply 1 ε t)).congr_deriv ?_
  simp [lineJet_zero, chiOf_sStar, hf0, sStar_pos, sStar_vel, smul_zero]
  have h := axis1_vec_eq_stm t
  convert h using 1
  abel


lemma eventually_alphaOf_lineJet0_pos :
    ∀ᶠ ε : ℝ in 𝓝 0, 0 < alphaOf (lineJet 0 ε) := by
  have hα0 : 0 < alphaOf (lineJet 0 0) := by
    rw [lineJet_zero, alphaOf_sStar]; norm_num
  exact continuousAt_alphaOf_lineJet0.tendsto.eventually (Ioi_mem_nhds hα0)

lemma eventually_alphaOf_lineJet4_pos :
    ∀ᶠ ε : ℝ in 𝓝 0, 0 < alphaOf (lineJet 4 ε) := by
  have hα0 : 0 < alphaOf (lineJet 4 0) := by
    rw [lineJet_zero, alphaOf_sStar]; norm_num
  exact continuousAt_alphaOf_lineJet4.tendsto.eventually (Ioi_mem_nhds hα0)


lemma hasDerivAt_alphaOf_lineJet0 :
    HasDerivAt (fun ε => alphaOf (lineJet 0 ε)) (-(8 / 25)) 0 := by
  have hden : HasDerivAt (fun ε : ℝ => 5 / 2 + ε) (1 : ℝ) 0 :=
    (hasDerivAt_id (0 : ℝ)).const_add (5 / 2)
  have hinv : HasDerivAt (fun ε : ℝ => (5 / 2 + ε)⁻¹) (-(4 / 25)) 0 := by
    have h0 : (5 / 2 + (0 : ℝ)) ≠ 0 := by norm_num
    exact (hden.inv h0).congr_deriv (by norm_num)
  have h2 : HasDerivAt (fun ε : ℝ => (2 : ℝ) * (5 / 2 + ε)⁻¹) (-(8 / 25)) 0 :=
    (hinv.const_mul (2 : ℝ)).congr_deriv (by ring)
  have hclosed : HasDerivAt (fun ε : ℝ => 2 / (5 / 2 + ε) - 2 / 5) (-(8 / 25)) 0 := by
    simpa [div_eq_mul_inv] using h2.sub_const (2 / 5)
  refine hclosed.congr_of_eventuallyEq ?_
  filter_upwards [eventually_lineJet0_pos] with ε hε
  simpa using alphaOf_lineJet0 hε

lemma sqrt10_sq_val : Real.sqrt 10 ^ 2 = 10 :=
  Real.sq_sqrt (by norm_num)

lemma sqrt_alpha_deriv0_eval :
    (1 / (2 * (Real.sqrt 10 / 5))) * (-(8 / 25)) = -(2 * Real.sqrt 10 / 25) := by
  have hs : Real.sqrt 10 ≠ 0 := Real.sqrt_ne_zero'.2 (by norm_num)
  field_simp [hs]
  ring_nf
  simp only [← pow_two, sqrt10_sq_val]
  ring

lemma hasDerivAt_sqrt_alpha_lineJet0 :
    HasDerivAt (fun ε => Real.sqrt (alphaOf (lineJet 0 ε)))
      (-(2 * Real.sqrt 10 / 25)) 0 := by
  have hα0 : 0 < alphaOf (lineJet 0 0) := by
    rw [lineJet_zero, alphaOf_sStar]; norm_num
  have h := (Real.hasDerivAt_sqrt hα0.ne').comp 0 hasDerivAt_alphaOf_lineJet0
  refine h.congr_deriv ?_
  rw [lineJet_zero, alphaOf_sStar, sqrt_two_div_five]
  exact sqrt_alpha_deriv0_eval

lemma alpha_r_lineJet0 {ε : ℝ} (hε : -5 / 2 < ε) :
    alphaOf (lineJet 0 ε) * rnorm (lineJet 0 ε) = 1 - (2 / 5) * ε := by
  linarith [one_sub_alpha_r_lineJet0 hε]

lemma fg_f_lineJet0_ell {ε χ : ℝ} (hα : 0 < alphaOf (lineJet 0 ε))
    (hε : -5 / 2 < ε) :
    fg_f (lineJet 0 ε) χ =
      1 - (1 - Real.cos (Real.sqrt (alphaOf (lineJet 0 ε)) * χ)) /
        (1 - (2 / 5) * ε) := by
  rw [fg_f_ell hα, alpha_r_lineJet0 hε]

lemma fg_g_lineJet0_ell {ε t χ : ℝ} (hα : 0 < alphaOf (lineJet 0 ε)) :
    fg_g (lineJet 0 ε) t χ =
      t - χ / alphaOf (lineJet 0 ε) +
        Real.sin (Real.sqrt (alphaOf (lineJet 0 ε)) * χ) /
          (alphaOf (lineJet 0 ε) * Real.sqrt (alphaOf (lineJet 0 ε))) := by
  have h := fg_g_ell (s := lineJet 0 ε) (t := t) (chi := χ) hα
  simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using h

lemma sqrt_alpha_lineJet0_zero :
    Real.sqrt (alphaOf (lineJet 0 0)) = Real.sqrt 10 / 5 := by
  rw [lineJet_zero, alphaOf_sStar, sqrt_two_div_five]

lemma hasDerivAt_one_sub_two_fifths :
    HasDerivAt (fun ε : ℝ => 1 - (2 / 5) * ε) (-(2 / 5)) 0 := by
  have h := ((hasDerivAt_id (0 : ℝ)).const_mul (2 / 5 : ℝ)).const_sub (1 : ℝ)
  refine (h.congr_of_eventuallyEq (Eventually.of_forall fun ε => by simp [id])).congr_deriv ?_
  ring

lemma hasDerivAt_fg_f_lineJet0_fixed (χ : ℝ) :
    HasDerivAt (fun ε => fg_f (lineJet 0 ε) χ)
      ((2 * Real.sqrt 10 / 25) * χ *
        Real.sin ((Real.sqrt 10 / 5) * χ)
        - (2 / 5) * (1 - Real.cos ((Real.sqrt 10 / 5) * χ))) 0 := by
  have hψ := hasDerivAt_sqrt_alpha_lineJet0
  have hψχ : HasDerivAt
      (fun ε => Real.sqrt (alphaOf (lineJet 0 ε)) * χ)
      ((-(2 * Real.sqrt 10 / 25)) * χ) 0 :=
    hψ.mul_const χ
  have hω : Real.sqrt (alphaOf (lineJet 0 0)) * χ = (Real.sqrt 10 / 5) * χ := by
    rw [sqrt_alpha_lineJet0_zero]
  have hcos : HasDerivAt
      (fun ε => Real.cos (Real.sqrt (alphaOf (lineJet 0 ε)) * χ))
      (-Real.sin ((Real.sqrt 10 / 5) * χ) * ((-(2 * Real.sqrt 10 / 25)) * χ)) 0 := by
    have h := (Real.hasDerivAt_cos (Real.sqrt (alphaOf (lineJet 0 0)) * χ)).comp 0 hψχ
    exact h.congr_deriv (by rw [hω])
  have hnum : HasDerivAt
      (fun ε => 1 - Real.cos (Real.sqrt (alphaOf (lineJet 0 ε)) * χ))
      (Real.sin ((Real.sqrt 10 / 5) * χ) * ((-(2 * Real.sqrt 10 / 25)) * χ)) 0 := by
    exact ((hasDerivAt_const (0 : ℝ) (1 : ℝ)).sub hcos).congr_deriv (by ring)
  have hden := hasDerivAt_one_sub_two_fifths
  have hden0 : (1 - (2 / 5) * (0 : ℝ)) ≠ 0 := by norm_num
  have hdiv := hnum.div hden hden0
  have hclosed : HasDerivAt
      (fun ε =>
        1 - (1 - Real.cos (Real.sqrt (alphaOf (lineJet 0 ε)) * χ)) /
          (1 - (2 / 5) * ε))
      ((2 * Real.sqrt 10 / 25) * χ *
        Real.sin ((Real.sqrt 10 / 5) * χ)
        - (2 / 5) * (1 - Real.cos ((Real.sqrt 10 / 5) * χ))) 0 := by
    have h1 := (hasDerivAt_const (0 : ℝ) (1 : ℝ)).sub hdiv
    refine h1.congr_deriv ?_
    have hnum0 : 1 - Real.cos (Real.sqrt (alphaOf (lineJet 0 0)) * χ) =
        1 - Real.cos ((Real.sqrt 10 / 5) * χ) := by rw [sqrt_alpha_lineJet0_zero]
    simp [hnum0]
    ring
  refine hclosed.congr_of_eventuallyEq ?_
  filter_upwards [eventually_alphaOf_lineJet0_pos, eventually_lineJet0_pos]
    with ε hα hε
  exact fg_f_lineJet0_ell hα hε

lemma hasDerivAt_inv_alpha_lineJet0 :
    HasDerivAt (fun ε => (alphaOf (lineJet 0 ε))⁻¹) 2 0 := by
  have hα0 : alphaOf (lineJet 0 0) ≠ 0 := by
    rw [lineJet_zero, alphaOf_sStar]; norm_num
  refine (hasDerivAt_alphaOf_lineJet0.inv hα0).congr_deriv ?_
  rw [lineJet_zero, alphaOf_sStar]
  norm_num

lemma psi3_sStar : (Real.sqrt 10 / 5) ^ 3 = 2 * Real.sqrt 10 / 25 := by
  have hsq := sqrt10_sq_val
  calc
    (Real.sqrt 10 / 5) ^ 3
        = Real.sqrt 10 ^ 3 / 125 := by ring
    _ = Real.sqrt 10 ^ 2 * Real.sqrt 10 / 125 := by ring
    _ = 10 * Real.sqrt 10 / 125 := by rw [hsq]
    _ = 2 * Real.sqrt 10 / 25 := by ring

lemma psi3_sStar_sq : ((Real.sqrt 10 / 5) ^ 3) ^ 2 = (8 : ℝ) / 125 := by
  rw [psi3_sStar]
  have hs : Real.sqrt 10 ≠ 0 := Real.sqrt_ne_zero'.2 (by norm_num)
  field_simp [hs]
  rw [sqrt10_sq_val]
  ring

lemma hasDerivAt_pow3_sqrt_alpha_lineJet0 :
    HasDerivAt (fun ε => Real.sqrt (alphaOf (lineJet 0 ε)) ^ 3)
      (-(12 * Real.sqrt 10 / 125)) 0 := by
  have hψ := hasDerivAt_sqrt_alpha_lineJet0
  have h := (hasDerivAt_pow 3 (Real.sqrt (alphaOf (lineJet 0 0)))).comp 0 hψ
  refine h.congr_deriv ?_
  rw [sqrt_alpha_lineJet0_zero, sqrt10_div5_sq]
  ring

lemma sin_div_psi3_deriv0 (χ : ℝ) :
    (Real.cos ((Real.sqrt 10 / 5) * χ) * (-(2 * Real.sqrt 10 / 25) * χ) *
        (Real.sqrt 10 / 5) ^ 3
      - Real.sin ((Real.sqrt 10 / 5) * χ) * (-(12 * Real.sqrt 10 / 125))) /
      ((Real.sqrt 10 / 5) ^ 3) ^ 2
      = -χ * Real.cos ((Real.sqrt 10 / 5) * χ)
        + (3 * Real.sqrt 10 / 2) * Real.sin ((Real.sqrt 10 / 5) * χ) := by
  rw [psi3_sStar]
  have hden : (2 * Real.sqrt 10 / 25) ^ 2 = (8 : ℝ) / 125 := by
    have hs : Real.sqrt 10 ≠ 0 := Real.sqrt_ne_zero'.2 (by norm_num)
    field_simp [hs]
    rw [sqrt10_sq_val]
    ring
  rw [hden]
  have hs : Real.sqrt 10 ≠ 0 := Real.sqrt_ne_zero'.2 (by norm_num)
  field_simp [hs]
  ring_nf
  simp only [sqrt10_sq_val]
  ring

lemma hasDerivAt_fg_g_lineJet0_fixed (t χ : ℝ) :
    HasDerivAt (fun ε => fg_g (lineJet 0 ε) t χ)
      (-(2 : ℝ) * χ - χ * Real.cos ((Real.sqrt 10 / 5) * χ)
        + (3 * Real.sqrt 10 / 2) * Real.sin ((Real.sqrt 10 / 5) * χ)) 0 := by
  have hψ := hasDerivAt_sqrt_alpha_lineJet0
  have hψχ : HasDerivAt
      (fun ε => Real.sqrt (alphaOf (lineJet 0 ε)) * χ)
      ((-(2 * Real.sqrt 10 / 25)) * χ) 0 :=
    hψ.mul_const χ
  have hω : Real.sqrt (alphaOf (lineJet 0 0)) * χ = (Real.sqrt 10 / 5) * χ := by
    rw [sqrt_alpha_lineJet0_zero]
  have hsin : HasDerivAt
      (fun ε => Real.sin (Real.sqrt (alphaOf (lineJet 0 ε)) * χ))
      (Real.cos ((Real.sqrt 10 / 5) * χ) * ((-(2 * Real.sqrt 10 / 25)) * χ)) 0 := by
    exact ((Real.hasDerivAt_sin (Real.sqrt (alphaOf (lineJet 0 0)) * χ)).comp 0 hψχ).congr_deriv
      (by rw [hω])
  have hψ3 := hasDerivAt_pow3_sqrt_alpha_lineJet0
  have hψ30 : Real.sqrt (alphaOf (lineJet 0 0)) ^ 3 ≠ 0 := by
    rw [sqrt_alpha_lineJet0_zero]
    exact pow_ne_zero 3 (div_ne_zero (Real.sqrt_ne_zero'.2 (by norm_num)) (by norm_num))
  have hquot := hsin.div hψ3 hψ30
  have hinv := hasDerivAt_inv_alpha_lineJet0
  have hχα : HasDerivAt (fun ε => χ * (alphaOf (lineJet 0 ε))⁻¹) (2 * χ) 0 :=
    (hinv.const_mul χ).congr_deriv (by ring)
  have hclosed : HasDerivAt
      (fun ε =>
        t - χ * (alphaOf (lineJet 0 ε))⁻¹ +
          Real.sin (Real.sqrt (alphaOf (lineJet 0 ε)) * χ) /
            (Real.sqrt (alphaOf (lineJet 0 ε)) ^ 3))
      (-(2 : ℝ) * χ - χ * Real.cos ((Real.sqrt 10 / 5) * χ)
        + (3 * Real.sqrt 10 / 2) * Real.sin ((Real.sqrt 10 / 5) * χ)) 0 := by
    have hsum := (hasDerivAt_const (0 : ℝ) t).sub hχα |>.add hquot
    refine hsum.congr_deriv ?_
    rw [sqrt_alpha_lineJet0_zero]
    linarith [sin_div_psi3_deriv0 χ]
  refine hclosed.congr_of_eventuallyEq ?_
  filter_upwards [eventually_alphaOf_lineJet0_pos] with ε hα
  have hpow : alphaOf (lineJet 0 ε) * Real.sqrt (alphaOf (lineJet 0 ε)) =
      Real.sqrt (alphaOf (lineJet 0 ε)) ^ 3 := by
    have hsq := Real.sq_sqrt hα.le
    calc
      alphaOf (lineJet 0 ε) * Real.sqrt (alphaOf (lineJet 0 ε))
          = Real.sqrt (alphaOf (lineJet 0 ε)) ^ 2 *
            Real.sqrt (alphaOf (lineJet 0 ε)) := by rw [hsq]
      _ = Real.sqrt (alphaOf (lineJet 0 ε)) ^ 3 := by ring
  rw [fg_g_lineJet0_ell hα, hpow]
  ring

lemma hasDerivAt_alphaOf_lineJet4 :
    HasDerivAt (fun ε => alphaOf (lineJet 4 ε))
      (-(2 * (Real.sqrt 10 / 5))) 0 := by
  have hlin : HasDerivAt (fun ε : ℝ => (2 * (Real.sqrt 10 / 5)) * ε)
      (2 * (Real.sqrt 10 / 5)) 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).const_mul (2 * (Real.sqrt 10 / 5))
  have hsq : HasDerivAt (fun ε : ℝ => ε ^ 2) (0 : ℝ) 0 := by
    simpa using (hasDerivAt_pow 2 (0 : ℝ))
  have h : HasDerivAt
      (fun ε : ℝ => 2 / 5 - 2 * (Real.sqrt 10 / 5) * ε - ε ^ 2)
      (-(2 * (Real.sqrt 10 / 5))) 0 := by
    have h' := (hlin.const_sub (2 / 5 : ℝ)).sub hsq
    refine (h'.congr_of_eventuallyEq
      (Eventually.of_forall fun ε => by simp [Pi.sub_apply])).congr_deriv ?_
    ring
  refine h.congr_of_eventuallyEq ?_
  filter_upwards with ε
  simpa using alphaOf_lineJet4 ε

lemma sqrt_alpha_deriv4_eval :
    (1 / (2 * (Real.sqrt 10 / 5))) * (-(2 * (Real.sqrt 10 / 5))) = (-1 : ℝ) := by
  have hs : Real.sqrt 10 ≠ 0 := Real.sqrt_ne_zero'.2 (by norm_num)
  field_simp [hs]

lemma hasDerivAt_sqrt_alpha_lineJet4 :
    HasDerivAt (fun ε => Real.sqrt (alphaOf (lineJet 4 ε))) (-1) 0 := by
  have hα0 : 0 < alphaOf (lineJet 4 0) := by
    rw [lineJet_zero, alphaOf_sStar]; norm_num
  have h := (Real.hasDerivAt_sqrt hα0.ne').comp 0 hasDerivAt_alphaOf_lineJet4
  refine h.congr_deriv ?_
  rw [lineJet_zero, alphaOf_sStar, sqrt_two_div_five]
  exact sqrt_alpha_deriv4_eval

lemma sqrt_alpha_lineJet4_zero :
    Real.sqrt (alphaOf (lineJet 4 0)) = Real.sqrt 10 / 5 := by
  rw [lineJet_zero, alphaOf_sStar, sqrt_two_div_five]

lemma fg_f_lineJet4_ell {ε χ : ℝ} (hα : 0 < alphaOf (lineJet 4 ε)) :
    fg_f (lineJet 4 ε) χ =
      1 - (1 - Real.cos (Real.sqrt (alphaOf (lineJet 4 ε)) * χ)) /
        ((5 / 2) * alphaOf (lineJet 4 ε)) := by
  rw [fg_f_ell hα, rnorm_lineJet4]
  ring

lemma fg_g_lineJet4_ell {ε t χ : ℝ} (hα : 0 < alphaOf (lineJet 4 ε)) :
    fg_g (lineJet 4 ε) t χ =
      t - χ / alphaOf (lineJet 4 ε) +
        Real.sin (Real.sqrt (alphaOf (lineJet 4 ε)) * χ) /
          (alphaOf (lineJet 4 ε) * Real.sqrt (alphaOf (lineJet 4 ε))) := by
  have h := fg_g_ell (s := lineJet 4 ε) (t := t) (chi := χ) hα
  simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using h

lemma fg_f_lineJet4_div_deriv (χ : ℝ) :
    (0 : ℝ) -
      (Real.sin ((Real.sqrt 10 / 5) * χ) * (-χ) * ((5 / 2) * (2 / 5))
        - (1 - Real.cos ((Real.sqrt 10 / 5) * χ)) * (-Real.sqrt 10)) /
        ((5 / 2) * (2 / 5)) ^ 2
      = χ * Real.sin ((Real.sqrt 10 / 5) * χ)
        - Real.sqrt 10 * (1 - Real.cos ((Real.sqrt 10 / 5) * χ)) := by
  norm_num
  ring

lemma hasDerivAt_fg_f_lineJet4_fixed (χ : ℝ) :
    HasDerivAt (fun ε => fg_f (lineJet 4 ε) χ)
      (χ * Real.sin ((Real.sqrt 10 / 5) * χ)
        - Real.sqrt 10 * (1 - Real.cos ((Real.sqrt 10 / 5) * χ))) 0 := by
  have hψ := hasDerivAt_sqrt_alpha_lineJet4
  have hψχ : HasDerivAt
      (fun ε => Real.sqrt (alphaOf (lineJet 4 ε)) * χ) (-χ) 0 :=
    (hψ.mul_const χ).congr_deriv (by ring)
  have hω : Real.sqrt (alphaOf (lineJet 4 0)) * χ = (Real.sqrt 10 / 5) * χ := by
    rw [sqrt_alpha_lineJet4_zero]
  have hcos : HasDerivAt
      (fun ε => Real.cos (Real.sqrt (alphaOf (lineJet 4 ε)) * χ))
      (-Real.sin ((Real.sqrt 10 / 5) * χ) * (-χ)) 0 := by
    exact ((Real.hasDerivAt_cos (Real.sqrt (alphaOf (lineJet 4 0)) * χ)).comp 0 hψχ).congr_deriv
      (by rw [hω])
  have hnum : HasDerivAt
      (fun ε => 1 - Real.cos (Real.sqrt (alphaOf (lineJet 4 ε)) * χ))
      (Real.sin ((Real.sqrt 10 / 5) * χ) * (-χ)) 0 :=
    ((hasDerivAt_const (0 : ℝ) (1 : ℝ)).sub hcos).congr_deriv (by ring)
  have hden : HasDerivAt (fun ε => (5 / 2) * alphaOf (lineJet 4 ε))
      (-Real.sqrt 10) 0 :=
    (hasDerivAt_alphaOf_lineJet4.const_mul (5 / 2)).congr_deriv (by ring)
  have hden0 : (5 / 2) * alphaOf (lineJet 4 0) ≠ 0 := by
    rw [lineJet_zero, alphaOf_sStar]; norm_num
  have hdiv := hnum.div hden hden0
  have hclosed : HasDerivAt
      (fun ε =>
        1 - (1 - Real.cos (Real.sqrt (alphaOf (lineJet 4 ε)) * χ)) /
          ((5 / 2) * alphaOf (lineJet 4 ε)))
      (χ * Real.sin ((Real.sqrt 10 / 5) * χ)
        - Real.sqrt 10 * (1 - Real.cos ((Real.sqrt 10 / 5) * χ))) 0 := by
    refine ((hasDerivAt_const (0 : ℝ) (1 : ℝ)).sub hdiv).congr_deriv ?_
    rw [lineJet_zero, alphaOf_sStar, sqrt_two_div_five]
    exact fg_f_lineJet4_div_deriv χ
  refine hclosed.congr_of_eventuallyEq ?_
  filter_upwards [eventually_alphaOf_lineJet4_pos] with ε hα
  exact fg_f_lineJet4_ell hα

lemma hasDerivAt_inv_alpha_lineJet4 :
    HasDerivAt (fun ε => (alphaOf (lineJet 4 ε))⁻¹)
      (5 * Real.sqrt 10 / 2) 0 := by
  have hα0 : alphaOf (lineJet 4 0) ≠ 0 := by
    rw [lineJet_zero, alphaOf_sStar]; norm_num
  refine (hasDerivAt_alphaOf_lineJet4.inv hα0).congr_deriv ?_
  rw [lineJet_zero, alphaOf_sStar]
  have hs : Real.sqrt 10 ≠ 0 := Real.sqrt_ne_zero'.2 (by norm_num)
  field_simp [hs]

lemma hasDerivAt_pow3_sqrt_alpha_lineJet4 :
    HasDerivAt (fun ε => Real.sqrt (alphaOf (lineJet 4 ε)) ^ 3)
      (-(6 / 5)) 0 := by
  have h := (hasDerivAt_pow 3 (Real.sqrt (alphaOf (lineJet 4 0)))).comp 0
    hasDerivAt_sqrt_alpha_lineJet4
  refine h.congr_deriv ?_
  rw [sqrt_alpha_lineJet4_zero, sqrt10_div5_sq]
  ring

lemma sin_div_psi3_deriv4 (χ : ℝ) :
    (Real.cos ((Real.sqrt 10 / 5) * χ) * (-χ) * (Real.sqrt 10 / 5) ^ 3
      - Real.sin ((Real.sqrt 10 / 5) * χ) * (-(6 / 5))) /
      ((Real.sqrt 10 / 5) ^ 3) ^ 2
      = -((5 * Real.sqrt 10 / 4) * χ * Real.cos ((Real.sqrt 10 / 5) * χ))
        + (75 / 4) * Real.sin ((Real.sqrt 10 / 5) * χ) := by
  rw [psi3_sStar]
  have hden : (2 * Real.sqrt 10 / 25) ^ 2 = (8 : ℝ) / 125 := by
    have hs : Real.sqrt 10 ≠ 0 := Real.sqrt_ne_zero'.2 (by norm_num)
    field_simp [hs]
    rw [sqrt10_sq_val]
    ring
  rw [hden]
  have hs : Real.sqrt 10 ≠ 0 := Real.sqrt_ne_zero'.2 (by norm_num)
  field_simp [hs]
  ring

lemma hasDerivAt_fg_g_lineJet4_fixed (t χ : ℝ) :
    HasDerivAt (fun ε => fg_g (lineJet 4 ε) t χ)
      (-(5 * Real.sqrt 10 / 2) * χ
        - (5 * Real.sqrt 10 / 4) * χ * Real.cos ((Real.sqrt 10 / 5) * χ)
        + (75 / 4) * Real.sin ((Real.sqrt 10 / 5) * χ)) 0 := by
  have hψχ : HasDerivAt
      (fun ε => Real.sqrt (alphaOf (lineJet 4 ε)) * χ) (-χ) 0 :=
    (hasDerivAt_sqrt_alpha_lineJet4.mul_const χ).congr_deriv (by ring)
  have hω : Real.sqrt (alphaOf (lineJet 4 0)) * χ = (Real.sqrt 10 / 5) * χ := by
    rw [sqrt_alpha_lineJet4_zero]
  have hsin : HasDerivAt
      (fun ε => Real.sin (Real.sqrt (alphaOf (lineJet 4 ε)) * χ))
      (Real.cos ((Real.sqrt 10 / 5) * χ) * (-χ)) 0 := by
    have h := (Real.hasDerivAt_sin (Real.sqrt (alphaOf (lineJet 4 0)) * χ)).comp 0 hψχ
    exact h.congr_deriv (by rw [hω])
  have hψ30 : Real.sqrt (alphaOf (lineJet 4 0)) ^ 3 ≠ 0 := by
    rw [sqrt_alpha_lineJet4_zero]
    exact pow_ne_zero 3 (div_ne_zero (Real.sqrt_ne_zero'.2 (by norm_num)) (by norm_num))
  have hquot := hsin.div hasDerivAt_pow3_sqrt_alpha_lineJet4 hψ30
  have hχα : HasDerivAt (fun ε => χ * (alphaOf (lineJet 4 ε))⁻¹)
      ((5 * Real.sqrt 10 / 2) * χ) 0 :=
    (hasDerivAt_inv_alpha_lineJet4.const_mul χ).congr_deriv (by ring)
  have hclosed : HasDerivAt
      (fun ε =>
        t - χ * (alphaOf (lineJet 4 ε))⁻¹ +
          Real.sin (Real.sqrt (alphaOf (lineJet 4 ε)) * χ) /
            (Real.sqrt (alphaOf (lineJet 4 ε)) ^ 3))
      (-(5 * Real.sqrt 10 / 2) * χ
        - (5 * Real.sqrt 10 / 4) * χ * Real.cos ((Real.sqrt 10 / 5) * χ)
        + (75 / 4) * Real.sin ((Real.sqrt 10 / 5) * χ)) 0 := by
    have hsum := (hasDerivAt_const (0 : ℝ) t).sub hχα |>.add hquot
    refine hsum.congr_deriv ?_
    rw [sqrt_alpha_lineJet4_zero]
    have hq := sin_div_psi3_deriv4 χ
    linarith [hq]
  refine hclosed.congr_of_eventuallyEq ?_
  filter_upwards [eventually_alphaOf_lineJet4_pos] with ε hα
  have hpow : alphaOf (lineJet 4 ε) * Real.sqrt (alphaOf (lineJet 4 ε)) =
      Real.sqrt (alphaOf (lineJet 4 ε)) ^ 3 := by
    have hsq := Real.sq_sqrt hα.le
    calc
      alphaOf (lineJet 4 ε) * Real.sqrt (alphaOf (lineJet 4 ε))
          = Real.sqrt (alphaOf (lineJet 4 ε)) ^ 2 *
            Real.sqrt (alphaOf (lineJet 4 ε)) := by rw [hsq]
      _ = Real.sqrt (alphaOf (lineJet 4 ε)) ^ 3 := by ring
  rw [fg_g_lineJet4_ell hα, hpow]
  ring


lemma hasDerivAt_fg_f_chiOf_lineJet0 (t : ℝ) :
    HasDerivAt (fun ε => fg_f (lineJet 0 ε) (chiOf (lineJet 0 ε) t))
      ((2 * Real.sqrt 10 / 25) * (2 * t / 5) * Real.sin (nStar * t)
        - (2 / 5) * (1 - Real.cos (nStar * t))
        + (-(2 / 5) * Fε_lineJet0 (2 * t / 5)) *
          (-Real.sin (nStar * t) * (Real.sqrt 10 / 5))) 0 := by
  have h := hasDerivAt_fg_f_chiOf_gen t (hasDerivAt_chiOf_lineJet0 t)
    (hasDerivAt_fg_f_lineJet0_fixed (2 * t / 5))
  refine h.congr_deriv ?_
  rw [deriv_fg_f_sStar_at, omega_mul_chi_sStar]

lemma hasDerivAt_fg_g_chiOf_lineJet0 (t : ℝ) :
    HasDerivAt (fun ε => fg_g (lineJet 0 ε) t (chiOf (lineJet 0 ε) t))
      (-(2 : ℝ) * (2 * t / 5) - (2 * t / 5) * Real.cos (nStar * t)
        + (3 * Real.sqrt 10 / 2) * Real.sin (nStar * t)
        + (-(2 / 5) * Fε_lineJet0 (2 * t / 5)) *
          ((5 / 2) * (Real.cos (nStar * t) - 1))) 0 := by
  have h := hasDerivAt_fg_g_chiOf_gen t (hasDerivAt_chiOf_lineJet0 t)
    (hasDerivAt_fg_g_lineJet0_fixed t (2 * t / 5))
  refine h.congr_deriv ?_
  rw [deriv_fg_g_sStar_at, omega_mul_chi_sStar]

lemma chiPrime_lineJet4 (t : ℝ) :
    -(2 / 5) * (Real.sqrt 10 * (2 * t / 5) ^ 3 *
      stumpffS ((2 / 5) * (2 * t / 5) ^ 2)) =
      -(2 / 5) * Real.sqrt 10 * (t - Real.sin (nStar * t) / nStar) := by
  have h := chiCube_S_sStar t
  calc
    -(2 / 5) * (Real.sqrt 10 * (2 * t / 5) ^ 3 *
        stumpffS ((2 / 5) * (2 * t / 5) ^ 2))
        = -(2 / 5) * Real.sqrt 10 *
            ((2 * t / 5) ^ 3 * stumpffS ((2 / 5) * (2 * t / 5) ^ 2)) := by ring
    _ = -(2 / 5) * Real.sqrt 10 * (t - Real.sin (nStar * t) / nStar) := by rw [h]

lemma hasDerivAt_chiOf_lineJet4' (t : ℝ) :
    HasDerivAt (fun ε => chiOf (lineJet 4 ε) t)
      (-(2 / 5) * Real.sqrt 10 * (t - Real.sin (nStar * t) / nStar)) 0 :=
  (hasDerivAt_chiOf_lineJet4 t).congr_deriv (chiPrime_lineJet4 t)

lemma hasDerivAt_fg_f_chiOf_lineJet4 (t : ℝ) :
    HasDerivAt (fun ε => fg_f (lineJet 4 ε) (chiOf (lineJet 4 ε) t))
      ((2 * t / 5) * Real.sin (nStar * t)
        - Real.sqrt 10 * (1 - Real.cos (nStar * t))
        + (-(2 / 5) * Real.sqrt 10 * (t - Real.sin (nStar * t) / nStar)) *
          (-Real.sin (nStar * t) * (Real.sqrt 10 / 5))) 0 := by
  have h := hasDerivAt_fg_f_chiOf_gen t (hasDerivAt_chiOf_lineJet4' t)
    (hasDerivAt_fg_f_lineJet4_fixed (2 * t / 5))
  refine h.congr_deriv ?_
  rw [deriv_fg_f_sStar_at, omega_mul_chi_sStar]

lemma hasDerivAt_fg_g_chiOf_lineJet4 (t : ℝ) :
    HasDerivAt (fun ε => fg_g (lineJet 4 ε) t (chiOf (lineJet 4 ε) t))
      (-(5 * Real.sqrt 10 / 2) * (2 * t / 5)
        - (5 * Real.sqrt 10 / 4) * (2 * t / 5) * Real.cos (nStar * t)
        + (75 / 4) * Real.sin (nStar * t)
        + (-(2 / 5) * Real.sqrt 10 * (t - Real.sin (nStar * t) / nStar)) *
          ((5 / 2) * (Real.cos (nStar * t) - 1))) 0 := by
  have h := hasDerivAt_fg_g_chiOf_gen t (hasDerivAt_chiOf_lineJet4' t)
    (hasDerivAt_fg_g_lineJet4_fixed t (2 * t / 5))
  refine h.congr_deriv ?_
  rw [deriv_fg_g_sStar_at, omega_mul_chi_sStar]

lemma stmCol_dx (t : ℝ) :
    stmCol 0 t =
      ofCoords
        (stmRad t 1 0 0 0 * Real.cos (nStar * t)
          - stmTan t 1 0 0 0 * Real.sin (nStar * t))
        (stmRad t 1 0 0 0 * Real.sin (nStar * t)
          + stmTan t 1 0 0 0 * Real.cos (nStar * t))
        0 := by
  simpa [stmCol] using stmInertial_ofCoords t 1 0 0 0

lemma stmCol_dvy (t : ℝ) :
    stmCol 3 t =
      ofCoords
        (stmRad t 0 0 0 1 * Real.cos (nStar * t)
          - stmTan t 0 0 0 1 * Real.sin (nStar * t))
        (stmRad t 0 0 0 1 * Real.sin (nStar * t)
          + stmTan t 0 0 0 1 * Real.cos (nStar * t))
        0 := by
  simpa [stmCol] using stmInertial_ofCoords t 0 0 0 1

lemma sqrt10_div5_eq_n : Real.sqrt 10 / 5 = (5 / 2) * nStar := by
  have h := omega_mul_chi_sStar 1
  -- (√10/5)*(2/5) = nStar
  have : (Real.sqrt 10 / 5) * (2 / 5) = nStar := by
    simpa using h
  have h2 : (2 / 5 : ℝ) ≠ 0 := by norm_num
  field_simp [h2] at this
  linarith

lemma chiPrime_lineJet0 (t : ℝ) :
    -(2 / 5) * Fε_lineJet0 (2 * t / 5) =
      -(8 * t / 25) + (4 / 25) * Real.sin (nStar * t) / nStar := by
  rw [Fε_lineJet0_sStar]
  have hn := nStar_ne
  field_simp [hn]
  ring

lemma hasDerivAt_chiOf_lineJet0' (t : ℝ) :
    HasDerivAt (fun ε => chiOf (lineJet 0 ε) t)
      (-(8 * t / 25) + (4 / 25) * Real.sin (nStar * t) / nStar) 0 :=
  (hasDerivAt_chiOf_lineJet0 t).congr_deriv (chiPrime_lineJet0 t)

lemma fg_f_prime_lineJet0 (t : ℝ) :
    (2 * Real.sqrt 10 / 25) * (2 * t / 5) * Real.sin (nStar * t)
      - (2 / 5) * (1 - Real.cos (nStar * t))
      + (-(2 / 5) * Fε_lineJet0 (2 * t / 5)) *
        (-Real.sin (nStar * t) * (Real.sqrt 10 / 5))
      = (2 * nStar * t / 5) * Real.sin (nStar * t)
        - (2 / 5) * (1 - Real.cos (nStar * t))
        - (-(8 * t / 25) + (4 / 25) * Real.sin (nStar * t) / nStar) *
          Real.sin (nStar * t) * ((5 / 2) * nStar) := by
  have hχ := chiPrime_lineJet0 t
  have hn : 2 * Real.sqrt 10 / 25 = nStar := by rw [nStar, meanMotion_eq]
  rw [hχ, hn, sqrt10_div5_eq_n]
  ring

lemma fg_g_prime_lineJet0 (t : ℝ) :
    -(2 : ℝ) * (2 * t / 5) - (2 * t / 5) * Real.cos (nStar * t)
      + (3 * Real.sqrt 10 / 2) * Real.sin (nStar * t)
      + (-(2 / 5) * Fε_lineJet0 (2 * t / 5)) *
        ((5 / 2) * (Real.cos (nStar * t) - 1))
      = -(4 * t / 5) - (2 * t / 5) * Real.cos (nStar * t)
        + (3 * Real.sqrt 10 / 2) * Real.sin (nStar * t)
        + (-(8 * t / 25) + (4 / 25) * Real.sin (nStar * t) / nStar) *
          ((5 / 2) * (Real.cos (nStar * t) - 1)) := by
  rw [chiPrime_lineJet0]
  ring

lemma stmCol_dx_coords (t : ℝ) :
    stmCol 0 t =
      ofCoords
        ((2 - Real.cos (nStar * t)) * Real.cos (nStar * t)
          - (2 * Real.sin (nStar * t) - 3 * nStar * t) * Real.sin (nStar * t))
        ((2 - Real.cos (nStar * t)) * Real.sin (nStar * t)
          + (2 * Real.sin (nStar * t) - 3 * nStar * t) * Real.cos (nStar * t))
        0 := by
  rw [stmCol_dx]
  simp [stmRad, stmTan]

lemma stmCol_dvy_coords (t : ℝ) :
    stmCol 3 t =
      ofCoords
        ((2 * (1 - Real.cos (nStar * t)) / nStar) * Real.cos (nStar * t)
          - ((4 * Real.sin (nStar * t) - 3 * nStar * t) / nStar) *
            Real.sin (nStar * t))
        ((2 * (1 - Real.cos (nStar * t)) / nStar) * Real.sin (nStar * t)
          + ((4 * Real.sin (nStar * t) - 3 * nStar * t) / nStar) *
            Real.cos (nStar * t))
        0 := by
  rw [stmCol_dvy]
  simp [stmRad, stmTan]

lemma sqrt10_cube : Real.sqrt 10 ^ 3 = 10 * Real.sqrt 10 := by
  calc
    Real.sqrt 10 ^ 3 = Real.sqrt 10 ^ 2 * Real.sqrt 10 := by ring
    _ = 10 * Real.sqrt 10 := by rw [sqrt10_sq_val]

lemma sin_sq_as_cos (θ : ℝ) :
    Real.sin θ ^ 2 = 1 - Real.cos θ ^ 2 := by
  linarith [Real.sin_sq_add_cos_sq θ]

lemma axis0_x_eq (t : ℝ) :
    Real.cos (nStar * t) +
      ((2 * Real.sqrt 10 / 25) * (2 * t / 5) * Real.sin (nStar * t)
        - (2 / 5) * (1 - Real.cos (nStar * t))
        + (2 / 5) * Fε_lineJet0 (2 * t / 5) *
          (Real.sin (nStar * t) * (Real.sqrt 10 / 5))) * (5 / 2)
      = (2 - Real.cos (nStar * t)) * Real.cos (nStar * t)
        - (2 * Real.sin (nStar * t) - 3 * nStar * t) * Real.sin (nStar * t) := by
  have hs : Real.sqrt 10 ≠ 0 := Real.sqrt_ne_zero'.2 (by norm_num)
  have hF := Fε_lineJet0_sStar t
  have hn : nStar = 2 * Real.sqrt 10 / 25 := by rw [nStar, meanMotion_eq]
  rw [hF, hn]
  field_simp [hs]
  ring_nf
  simp only [sqrt10_sq_val, sqrt10_cube, sin_sq_as_cos]
  ring

lemma axis0_y_eq (t : ℝ) :
    (-(2 * (2 * t / 5)) - (2 * t / 5) * Real.cos (nStar * t)
        + (3 * Real.sqrt 10 / 2) * Real.sin (nStar * t)
        + -(2 / 5 * Fε_lineJet0 (2 * t / 5) *
            (5 / 2 * (Real.cos (nStar * t) - 1)))) *
      (Real.sqrt 10 / 5)
      = (2 - Real.cos (nStar * t)) * Real.sin (nStar * t)
        + (2 * Real.sin (nStar * t) - 3 * nStar * t) * Real.cos (nStar * t) := by
  have hs : Real.sqrt 10 ≠ 0 := Real.sqrt_ne_zero'.2 (by norm_num)
  have hF := Fε_lineJet0_sStar t
  have hn : nStar = 2 * Real.sqrt 10 / 25 := by rw [nStar, meanMotion_eq]
  rw [hF, hn]
  field_simp [hs]
  ring_nf
  simp only [sqrt10_sq_val, sqrt10_cube, sin_sq_as_cos]
  ring

lemma axis4_x_eq (t : ℝ) :
    ((2 * t / 5) * Real.sin (nStar * t)
        - Real.sqrt 10 * (1 - Real.cos (nStar * t))
        + (2 / 5) * Real.sqrt 10 * (t - Real.sin (nStar * t) / nStar) *
          (Real.sin (nStar * t) * (Real.sqrt 10 / 5))) * (5 / 2)
      = (2 * (1 - Real.cos (nStar * t)) / nStar) * Real.cos (nStar * t)
        - ((4 * Real.sin (nStar * t) - 3 * nStar * t) / nStar) *
          Real.sin (nStar * t) := by
  have hs : Real.sqrt 10 ≠ 0 := Real.sqrt_ne_zero'.2 (by norm_num)
  have hn0 := nStar_ne
  have hn : nStar = 2 * Real.sqrt 10 / 25 := by rw [nStar, meanMotion_eq]
  rw [hn] at hn0 ⊢
  field_simp [hs, hn0]
  ring_nf
  simp only [sqrt10_sq_val, sqrt10_cube, sin_sq_as_cos]
  ring

lemma axis4_y_eq (t : ℝ) :
    (Real.sin (nStar * t) / nStar) +
      (-(5 * Real.sqrt 10 / 2 * (2 * t / 5))
        - (5 * Real.sqrt 10 / 4) * (2 * t / 5) * Real.cos (nStar * t)
        + (75 / 4) * Real.sin (nStar * t)
        + -(2 / 5 * Real.sqrt 10 * (t - Real.sin (nStar * t) / nStar) *
            (5 / 2 * (Real.cos (nStar * t) - 1)))) *
        (Real.sqrt 10 / 5)
      = (2 * (1 - Real.cos (nStar * t)) / nStar) * Real.sin (nStar * t)
        + ((4 * Real.sin (nStar * t) - 3 * nStar * t) / nStar) *
          Real.cos (nStar * t) := by
  have hs : Real.sqrt 10 ≠ 0 := Real.sqrt_ne_zero'.2 (by norm_num)
  have hn0 := nStar_ne
  have hn : nStar = 2 * Real.sqrt 10 / 25 := by rw [nStar, meanMotion_eq]
  rw [hn] at hn0 ⊢
  field_simp [hs, hn0]
  ring_nf
  simp only [sqrt10_sq_val, sqrt10_cube, sin_sq_as_cos]
  ring

lemma axis0_vec_eq_stm (t : ℝ) :
    Real.cos (nStar * t) • ofCoords 1 0 0 +
        ((2 * Real.sqrt 10 / 25) * (2 * t / 5) * Real.sin (nStar * t)
          - (2 / 5) * (1 - Real.cos (nStar * t))
          + (2 / 5) * Fε_lineJet0 (2 * t / 5) *
            (Real.sin (nStar * t) * (Real.sqrt 10 / 5))) •
          ofCoords (5 / 2) 0 0 +
      (-(2 * (2 * t / 5)) - (2 * t / 5) * Real.cos (nStar * t)
        + (3 * Real.sqrt 10 / 2) * Real.sin (nStar * t)
        + -(2 / 5 * Fε_lineJet0 (2 * t / 5) *
            (5 / 2 * (Real.cos (nStar * t) - 1)))) •
        ofCoords 0 (Real.sqrt 10 / 5) 0
      = stmCol 0 t := by
  rw [ofCoords_smul, ofCoords_smul, ofCoords_smul, ofCoords_add, ofCoords_add,
    stmCol_dx_coords]
  apply (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).injective
  ext i
  fin_cases i
  · simp [ofCoords]; exact axis0_x_eq t
  · simp [ofCoords]; exact axis0_y_eq t
  · simp [ofCoords]

lemma hasDerivAt_keplerIC_lineJet0 (t : ℝ) :
    HasDerivAt (fun ε => keplerIC (lineJet 0 ε) t) (stmCol 0 t) 0 := by
  have hf := hasDerivAt_fg_f_chiOf_lineJet0 t
  have hg := hasDerivAt_fg_g_chiOf_lineJet0 t
  have hp := hasDerivAt_pos_lineJet0
  have hv := hasDerivAt_vel_lineJet0
  have hsum := (hf.smul hp).add (hg.smul hv)
  have hf0 := fg_f_sStar_n t
  refine (hsum.congr_of_eventuallyEq
    (Eventually.of_forall fun ε => keplerIC_lineJet_apply 0 ε t)).congr_deriv ?_
  simp [lineJet_zero, chiOf_sStar, hf0, sStar_pos, sStar_vel, eX, smul_zero]
  exact axis0_vec_eq_stm t

lemma axis4_vec_eq_stm (t : ℝ) :
    ((2 * t / 5) * Real.sin (nStar * t)
        - Real.sqrt 10 * (1 - Real.cos (nStar * t))
        + (2 / 5) * Real.sqrt 10 * (t - Real.sin (nStar * t) / nStar) *
          (Real.sin (nStar * t) * (Real.sqrt 10 / 5))) •
        ofCoords (5 / 2) 0 0 +
      ((Real.sin (nStar * t) / nStar) • ofCoords 0 1 0 +
        (-(5 * Real.sqrt 10 / 2 * (2 * t / 5))
          - (5 * Real.sqrt 10 / 4) * (2 * t / 5) * Real.cos (nStar * t)
          + (75 / 4) * Real.sin (nStar * t)
          + -(2 / 5 * Real.sqrt 10 * (t - Real.sin (nStar * t) / nStar) *
              (5 / 2 * (Real.cos (nStar * t) - 1)))) •
          ofCoords 0 (Real.sqrt 10 / 5) 0)
      = stmCol 3 t := by
  rw [ofCoords_smul, ofCoords_smul, ofCoords_smul, ofCoords_add, ofCoords_add,
    stmCol_dvy_coords]
  apply (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).injective
  ext i
  fin_cases i
  · simp [ofCoords]; exact axis4_x_eq t
  · simp [ofCoords]; exact axis4_y_eq t
  · simp [ofCoords]

lemma hasDerivAt_keplerIC_lineJet4 (t : ℝ) :
    HasDerivAt (fun ε => keplerIC (lineJet 4 ε) t) (stmCol 3 t) 0 := by
  have hf := hasDerivAt_fg_f_chiOf_lineJet4 t
  have hg := hasDerivAt_fg_g_chiOf_lineJet4 t
  have hp := hasDerivAt_pos_lineJet4
  have hv := hasDerivAt_vel_lineJet4
  have hsum := (hf.smul hp).add (hg.smul hv)
  have hg0 := fg_g_sStar_n t
  refine (hsum.congr_of_eventuallyEq
    (Eventually.of_forall fun ε => keplerIC_lineJet_apply 4 ε t)).congr_deriv ?_
  simp [lineJet_zero, chiOf_sStar, hg0, sStar_pos, sStar_vel, eY, smul_zero]
  exact axis4_vec_eq_stm t

lemma hasDerivAt_keplerIC_inPlane (j : Fin 4) (t : ℝ) :
    HasDerivAt (fun ε => keplerIC (lineJet (inPlane j) ε) t) (stmCol j t) 0 := by
  fin_cases j
  · simpa [inPlane] using hasDerivAt_keplerIC_lineJet0 t
  · simpa [inPlane] using hasDerivAt_keplerIC_lineJet1 t
  · simpa [inPlane] using hasDerivAt_keplerIC_lineJet3 t
  · simpa [inPlane] using hasDerivAt_keplerIC_lineJet4 t

lemma inner_diff_div_rho (t : ℝ) (w : Vec) :
    ⟪keplerIC sStar t - obs t, w⟫ / rhoStar t = ⟪uStar t, w⟫ := by
  simp [uStar, inner_smul_left, div_eq_inv_mul]

lemma hasDerivAt_rho_of {j : Fin 6} {w : Vec} {t : ℝ}
    (h : HasDerivAt (fun ε => keplerIC (lineJet j ε) t) w 0) :
    HasDerivAt (fun ε => ‖keplerIC (lineJet j ε) t - obs t‖) (⟪uStar t, w⟫) 0 := by
  have hf := h.sub_const (obs t)
  have hne : keplerIC (lineJet j 0) t - obs t ≠ 0 := by
    rw [lineJet_zero]; exact sub_ne_zero.mpr (keplerIC_sStar_obs_ne t)
  have hn := hasDerivAt_norm_vec hf hne
  refine hn.congr_deriv ?_
  rw [lineJet_zero]
  exact inner_diff_div_rho t w

lemma kepler_obs_eq_rho_uStar (t : ℝ) :
    keplerIC sStar t - obs t = rhoStar t • uStar t := by
  unfold uStar
  rw [smul_smul]
  change keplerIC sStar t - obs t = (rhoStar t * (rhoStar t)⁻¹) • (keplerIC sStar t - obs t)
  rw [mul_inv_cancel₀ (rhoStar_ne t), one_smul]

lemma hasDerivAt_los_of {j : Fin 6} {w : Vec} {t : ℝ}
    (h : HasDerivAt (fun ε => keplerIC (lineJet j ε) t) w 0) :
    HasDerivAt (fun ε => los obs (keplerIC (lineJet j ε)) t) (dlosSTM t w) 0 := by
  have hr := hasDerivAt_rho_of h
  have hg := h.sub_const (obs t)
  have hne : ‖keplerIC (lineJet j 0) t - obs t‖ ≠ 0 := by
    rw [lineJet_zero]; exact rhoStar_ne t
  have hinv := hr.inv hne
  have hsmul := hinv.smul hg
  have hval :
      ‖keplerIC (lineJet j 0) t - obs t‖⁻¹ • w
        + (-⟪uStar t, w⟫ / ‖keplerIC (lineJet j 0) t - obs t‖ ^ 2)
            • (keplerIC (lineJet j 0) t - obs t)
        = dlosSTM t w := by
    rw [lineJet_zero]
    have hρ : ‖keplerIC sStar t - obs t‖ = rhoStar t := rfl
    rw [hρ, kepler_obs_eq_rho_uStar t]
    have hn := rhoStar_ne t
    have hpow : rhoStar t ^ 2 = rhoStar t * rhoStar t := sq (rhoStar t)
    have hscale :
        ⟪uStar t, w⟫ * ((rhoStar t)⁻¹ * (rhoStar t)⁻¹) * rhoStar t
          = (rhoStar t)⁻¹ * ⟪uStar t, w⟫ := by
      field_simp [hn]
    simp [dlosSTM, hpow, div_eq_mul_inv, smul_smul, smul_sub, neg_smul]
    rw [hscale, ← sub_eq_add_neg]
  refine (hsmul.congr_of_eventuallyEq
    (Eventually.of_forall fun ε => los_kepler_apply (lineJet j ε) t)).congr_deriv ?_
  simpa using hval

lemma hasDerivAt_los_inPlane (j : Fin 4) (t : ℝ) :
    HasDerivAt (fun ε => los obs (keplerIC (lineJet (inPlane j) ε)) t)
      (dlosCol j t) 0 := by
  simpa [dlosCol] using hasDerivAt_los_of (hasDerivAt_keplerIC_inPlane j t)

lemma fderiv_los_inPlane (j : Fin 4) (t : ℝ) :
    fderiv ℝ (fun s => los obs (keplerIC s) t) sStar (Pi.single (inPlane j) 1)
      = dlosCol j t := by
  have hf : HasFDerivAt (fun s => los obs (keplerIC s) t)
      (fderiv ℝ (fun s => los obs (keplerIC s) t) sStar)
      (lineJet (inPlane j) 0) := by
    rw [lineJet_zero]; exact hasFDerivAt_los_keplerIC t
  exact (hf.comp_hasDerivAt 0 (hasDerivAt_lineJet (inPlane j) 0)).unique
    (hasDerivAt_los_inPlane j t)

lemma secondDiff_dlosCol (j : Fin 4) (h : ℝ) :
    secondDiff (fun t => dlosCol j t) h
      = dlosCol j 0 - (2 : ℝ) • dlosCol j h + dlosCol j (2 * h) :=
  rfl

lemma fderiv_sdCart_inPlane (j : Fin 4) :
    fderiv ℝ sdCart sStar (Pi.single (inPlane j) 1)
      = sdPairCoord
          (secondDiff (fun t => dlosCol j t) hSD1)
          (secondDiff (fun t => dlosCol j t) hSD2) := by
  have heq : (fun t => fderiv ℝ (fun s => los obs (keplerIC s) t) sStar
        (Pi.single (inPlane j) 1))
      = fun t => dlosCol j t :=
    funext fun t => fderiv_los_inPlane j t
  rw [fderiv_sdCart_apply, heq]

lemma xyBlkSTM_apply (i j : Fin 4) :
    xyBlkSTM i j =
      let w1 := secondDiff (fun t => dlosCol j t) hSD1
      let w2 := secondDiff (fun t => dlosCol j t) hSD2
      sdPairCoord w1 w2 (inPlaneOut i) := by
  simp [xyBlkSTM, secondDiff, dlosCol]
  fin_cases i <;> simp [inPlaneOut, sdPairCoord]

lemma xyBlk_eq_xyBlkSTM : xyBlk = xyBlkSTM := by
  ext i j
  simp [xyBlk, xyBlkSTM_apply, fderiv_sdCart_inPlane]

lemma nStar_gt_tight : (252982 / 1000000 : ℝ) < nStar := by
  have hsq : (252982 / 1000000 : ℝ) ^ 2 < nStar ^ 2 := by
    rw [nStar_sq]; norm_num
  exact lt_of_pow_lt_pow_left₀ 2 nStar_pos.le hsq

lemma nStar_lt_tight : nStar < (252983 / 1000000 : ℝ) := by
  have hsq : nStar ^ 2 < (252983 / 1000000 : ℝ) ^ 2 := by
    rw [nStar_sq]; norm_num
  exact lt_of_pow_lt_pow_left₀ 2 (by norm_num) hsq

lemma nStar_tight :
    (252982 / 1000000 : ℝ) < nStar ∧ nStar < (252983 / 1000000 : ℝ) :=
  ⟨nStar_gt_tight, nStar_lt_tight⟩

open Complex Finset in
lemma cos_bound8 {x : ℝ} (hx : |x| ≤ 1) :
    |Real.cos x - (1 - x ^ 2 / 2 + x ^ 4 / 24 - x ^ 6 / 720)| ≤
      |x| ^ 8 * (9 / 322560) := by
  have hx' : ‖(x : ℂ)‖ ≤ 1 := by simpa [Complex.norm_real, Real.norm_eq_abs] using hx
  have h :=
    calc
      ‖Complex.cos x - (1 - (x : ℂ) ^ 2 / 2 + (x : ℂ) ^ 4 / 24 - (x : ℂ) ^ 6 / 720)‖ =
          ‖(Complex.exp (-(x : ℂ) * I) - ∑ m ∈ range 8, (-(x : ℂ) * I) ^ m / m.factorial) / 2 +
            (Complex.exp ((x : ℂ) * I) - ∑ m ∈ range 8, ((x : ℂ) * I) ^ m / m.factorial) / 2‖ := by
        simp [Complex.cos, field, Finset.sum_range_succ, Nat.factorial]
        grind [I_sq, two_ne_zero]
      _ ≤ ‖Complex.exp (-(x : ℂ) * I) - ∑ m ∈ range 8, (-(x : ℂ) * I) ^ m / m.factorial‖ / 2 +
          ‖Complex.exp ((x : ℂ) * I) - ∑ m ∈ range 8, ((x : ℂ) * I) ^ m / m.factorial‖ / 2 := by
        grw [norm_add_le]
        simp
      _ ≤ ‖-(x : ℂ) * I‖ ^ 8 * (Nat.succ 8 * (Nat.factorial 8 * (8 : ℕ) : ℝ)⁻¹) / 2 +
          ‖(x : ℂ) * I‖ ^ 8 * (Nat.succ 8 * (Nat.factorial 8 * (8 : ℕ) : ℝ)⁻¹) / 2 := by
        grw [Complex.exp_bound (by simpa) (by simp), Complex.exp_bound (by simpa) (by simp)]
      _ ≤ |x| ^ 8 * (9 / 322560) := by
        simp [norm_mul, norm_neg, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs]
        norm_num
  simpa [← Complex.ofReal_cos, ← Real.norm_eq_abs, ← Complex.norm_real] using h

open Complex Finset in
lemma sin_bound9 {x : ℝ} (hx : |x| ≤ 1) :
    |Real.sin x - (x - x ^ 3 / 6 + x ^ 5 / 120 - x ^ 7 / 5040)| ≤
      |x| ^ 9 * (10 / 3265920) := by
  have hx' : ‖(x : ℂ)‖ ≤ 1 := by simpa [Complex.norm_real, Real.norm_eq_abs] using hx
  have h :=
    calc
      ‖Complex.sin x - ((x : ℂ) - (x : ℂ) ^ 3 / 6 + (x : ℂ) ^ 5 / 120 - (x : ℂ) ^ 7 / 5040)‖ =
          ‖(Complex.exp (-(x : ℂ) * I) - ∑ m ∈ range 9, (-(x : ℂ) * I) ^ m / m.factorial) * I / 2 -
            (Complex.exp ((x : ℂ) * I) - ∑ m ∈ range 9, ((x : ℂ) * I) ^ m / m.factorial) * I / 2‖ := by
        simp [Complex.sin, field, Finset.sum_range_succ, Nat.factorial]
        grind [I_sq, two_ne_zero]
      _ ≤ ‖Complex.exp (-(x : ℂ) * I) - ∑ m ∈ range 9, (-(x : ℂ) * I) ^ m / m.factorial‖ / 2 +
          ‖Complex.exp ((x : ℂ) * I) - ∑ m ∈ range 9, ((x : ℂ) * I) ^ m / m.factorial‖ / 2 := by
        grw [norm_sub_le]
        simp
      _ ≤ ‖-(x : ℂ) * I‖ ^ 9 * (Nat.succ 9 * (Nat.factorial 9 * (9 : ℕ) : ℝ)⁻¹) / 2 +
          ‖(x : ℂ) * I‖ ^ 9 * (Nat.succ 9 * (Nat.factorial 9 * (9 : ℕ) : ℝ)⁻¹) / 2 := by
        grw [Complex.exp_bound (by simpa) (by simp), Complex.exp_bound (by simpa) (by simp)]
      _ ≤ |x| ^ 9 * (10 / 3265920) := by
        simp [norm_mul, norm_neg, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs]
        norm_num
  simpa [← Complex.ofReal_sin, ← Real.norm_eq_abs, ← Complex.norm_real] using h

def cosPoly8 (x : ℝ) : ℝ :=
  1 - x ^ 2 / 2 + x ^ 4 / 24 - x ^ 6 / 720

def sinPoly9 (x : ℝ) : ℝ :=
  x - x ^ 3 / 6 + x ^ 5 / 120 - x ^ 7 / 5040

lemma cos_of_poly8 {x r : ℝ} (habs : |x| ≤ 1)
    (hrem : |x| ^ 8 * (9 / 322560) ≤ r) :
    cosPoly8 x - r ≤ Real.cos x ∧ Real.cos x ≤ cosPoly8 x + r := by
  unfold cosPoly8
  have hb := abs_le.mp (cos_bound8 habs)
  constructor <;> linarith

lemma sin_of_poly9 {x r : ℝ} (habs : |x| ≤ 1)
    (hrem : |x| ^ 9 * (10 / 3265920) ≤ r) :
    sinPoly9 x - r ≤ Real.sin x ∧ Real.sin x ≤ sinPoly9 x + r := by
  unfold sinPoly9
  have hb := abs_le.mp (sin_bound9 habs)
  constructor <;> linarith

lemma nStar_pow8 : nStar ^ 8 = (4096 / 244140625 : ℝ) := by
  calc
    nStar ^ 8 = (nStar ^ 2) ^ 4 := by ring
    _ = (8 / 125) ^ 4 := by rw [nStar_sq]
    _ = 4096 / 244140625 := by norm_num

lemma cosPoly8_one : cosPoly8 (1 : ℝ) = (389 / 720 : ℝ) := by
  simp only [cosPoly8]; norm_num

lemma cos_one_tight :
    (174263 / 322560 : ℝ) ≤ Real.cos 1 ∧ Real.cos 1 ≤ (174281 / 322560 : ℝ) := by
  have hrem : |(1 : ℝ)| ^ 8 * (9 / 322560) ≤ (1 / 35840 : ℝ) := by norm_num
  have h := cos_of_poly8 (by norm_num) hrem
  rw [cosPoly8_one] at h
  constructor <;> linarith [h.1, h.2]

lemma cosPoly8_half : cosPoly8 (1 / 2 : ℝ) = (40439 / 46080 : ℝ) := by
  simp only [cosPoly8]; norm_num

lemma cos_half_tight :
    (72466679 / 82575360 : ℝ) ≤ Real.cos (1 / 2) ∧
      Real.cos (1 / 2) ≤ (72466697 / 82575360 : ℝ) := by
  have hrem : |(1 / 2 : ℝ)| ^ 8 * (9 / 322560) ≤ (1 / 9175040 : ℝ) := by norm_num
  have h := cos_of_poly8 (by norm_num) hrem
  rw [cosPoly8_half] at h
  constructor <;> linarith [h.1, h.2]

lemma cosPoly8_quarter : cosPoly8 (1 / 4 : ℝ) = (2857439 / 2949120 : ℝ) := by
  simp only [cosPoly8]; norm_num

lemma cos_quarter_tight :
    (20482122743 / 21139292160 : ℝ) ≤ Real.cos (1 / 4) ∧
      Real.cos (1 / 4) ≤ (20482122761 / 21139292160 : ℝ) := by
  have hrem : |(1 / 4 : ℝ)| ^ 8 * (9 / 322560) ≤ (1 / 2348810240 : ℝ) := by norm_num
  have h := cos_of_poly8 (by norm_num) hrem
  rw [cosPoly8_quarter] at h
  constructor <;> linarith [h.1, h.2]

lemma sinPoly9_one : sinPoly9 (1 : ℝ) = (4241 / 5040 : ℝ) := by
  simp only [sinPoly9]; norm_num

lemma sin_one_tight :
    (196297 / 233280 : ℝ) ≤ Real.sin 1 ∧ Real.sin 1 ≤ (1374089 / 1632960 : ℝ) := by
  have hrem : |(1 : ℝ)| ^ 9 * (10 / 3265920) ≤ (1 / 326592 : ℝ) := by norm_num
  have h := sin_of_poly9 (by norm_num) hrem
  rw [sinPoly9_one] at h
  constructor <;> linarith [h.1, h.2]

lemma sinPoly9_half : sinPoly9 (1 / 2 : ℝ) = (309287 / 645120 : ℝ) := by
  simp only [sinPoly9]; norm_num

lemma sin_half_tight :
    (309287 / 645120 : ℝ) - (1 / 167215104 : ℝ) ≤ Real.sin (1 / 2) ∧
      Real.sin (1 / 2) ≤ (309287 / 645120 : ℝ) + (1 / 167215104 : ℝ) := by
  have hrem : |(1 / 2 : ℝ)| ^ 9 * (10 / 3265920) ≤ (1 / 167215104 : ℝ) := by norm_num
  have h := sin_of_poly9 (by norm_num) hrem
  rw [sinPoly9_half] at h
  constructor <;> linarith [h.1, h.2]

lemma sinPoly9_quarter : sinPoly9 (1 / 4 : ℝ) = (20429471 / 82575360 : ℝ) := by
  simp only [sinPoly9]; norm_num

lemma sin_quarter_tight :
    (20429471 / 82575360 : ℝ) - (1 / 85614133248 : ℝ) ≤ Real.sin (1 / 4) ∧
      Real.sin (1 / 4) ≤ (20429471 / 82575360 : ℝ) + (1 / 85614133248 : ℝ) := by
  have hrem : |(1 / 4 : ℝ)| ^ 9 * (10 / 3265920) ≤ (1 / 85614133248 : ℝ) := by norm_num
  have h := sin_of_poly9 (by norm_num) hrem
  rw [sinPoly9_quarter] at h
  constructor <;> linarith [h.1, h.2]

lemma uStar_ofLp0 (t : ℝ) :
    (uStar t).ofLp 0 =
      ((5 / 2) * Real.cos (nStar * t) - Real.cos t) * (rhoStar t)⁻¹ := by
  simp [uStar, PiLp.smul_apply, smul_eq_mul, PiLp.sub_apply,
    (keplerIC_sStar_ofLp01 t).1, (obs_ofLp01 t).1, rhoStar, mul_comm]

lemma uStar_ofLp1 (t : ℝ) :
    (uStar t).ofLp 1 =
      ((5 / 2) * Real.sin (nStar * t) - Real.sin t) * (rhoStar t)⁻¹ := by
  simp [uStar, PiLp.smul_apply, smul_eq_mul, PiLp.sub_apply,
    (keplerIC_sStar_ofLp01 t).2, (obs_ofLp01 t).2, rhoStar, mul_comm]

lemma uStar_ofLp2 (t : ℝ) : (uStar t).ofLp 2 = 0 := by
  simp [uStar, PiLp.smul_apply, smul_eq_mul, PiLp.sub_apply,
    keplerIC_sStar_ofLp2, obs_ofLp2]

lemma dlosSTM_ofLp (t : ℝ) (dr : Vec) (i : Fin 3) :
    (dlosSTM t dr).ofLp i =
      (rhoStar t)⁻¹ * (dr.ofLp i - ⟪uStar t, dr⟫ * (uStar t).ofLp i) := by
  simp [dlosSTM, PiLp.smul_apply, smul_eq_mul, PiLp.sub_apply]

lemma stmCol0_zero : stmCol 0 0 = ofCoords 1 0 0 := by
  rw [stmCol_dx_coords]
  simp [mul_zero]
  norm_num

lemma stmCol1_zero : stmCol 1 0 = ofCoords 0 1 0 := by
  rw [stmCol_dy]
  simp

lemma stmCol2_zero : stmCol 2 0 = 0 := by
  rw [stmCol_dvx]
  simp [ofCoords_zero]

lemma stmCol3_zero : stmCol 3 0 = 0 := by
  rw [stmCol_dvy_coords]
  simp [mul_zero, ofCoords_zero]

lemma uStar_zero : uStar 0 = ofCoords 1 0 0 := by
  apply (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).injective
  ext i; fin_cases i
  · have h := uStar_ofLp0 (0 : ℝ)
    simp [rhoStar_zero] at h
    simpa [ofCoords, h] using (by norm_num : (5 / 2 - 1 : ℝ) * (2 / 3) = 1)
  · have h := uStar_ofLp1 (0 : ℝ)
    simp [rhoStar_zero] at h
    simpa [ofCoords, h]
  · have h := uStar_ofLp2 (0 : ℝ)
    simpa [ofCoords] using h

lemma inner_uStar_stmCol0_zero : ⟪uStar 0, stmCol 0 0⟫ = 1 := by
  rw [stmCol0_zero, uStar_zero, ← vecDot_eq_inner]
  simp [vecDot, ofLp_ofCoords, Fin.sum_univ_three]

lemma dlosCol0_zero_ofLp (i : Fin 3) : (dlosCol 0 0).ofLp i = 0 := by
  have hinn : ⟪ofCoords 1 0 0, ofCoords 1 0 0⟫ = 1 := by
    rw [← vecDot_eq_inner]; simp [vecDot, ofLp_ofCoords, Fin.sum_univ_three]
  rw [dlosCol, dlosSTM_ofLp, rhoStar_zero, stmCol0_zero, uStar_zero, hinn]
  fin_cases i <;> simp [ofLp_ofCoords]

lemma dlosCol0_zero : dlosCol 0 0 = 0 := by
  apply (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).injective
  ext i; fin_cases i <;> simpa [PiLp.zero_apply] using dlosCol0_zero_ofLp _

lemma dlosCol2_zero : dlosCol 2 0 = 0 := by
  simp [dlosCol, dlosSTM, stmCol2_zero]

lemma dlosCol3_zero : dlosCol 3 0 = 0 := by
  simp [dlosCol, dlosSTM, stmCol3_zero]

lemma inner_uStar_stmCol1_zero : ⟪uStar 0, stmCol 1 0⟫ = 0 := by
  rw [stmCol1_zero, uStar_zero, ← vecDot_eq_inner]
  simp [vecDot, ofLp_ofCoords, Fin.sum_univ_three]

lemma dlosCol1_zero_ofLp :
    (dlosCol 1 0).ofLp 0 = 0 ∧ (dlosCol 1 0).ofLp 1 = 2 / 3 ∧
      (dlosCol 1 0).ofLp 2 = 0 := by
  have hinn : ⟪ofCoords 1 0 0, ofCoords 0 1 0⟫ = 0 := by
    rw [← vecDot_eq_inner]; simp [vecDot, ofLp_ofCoords, Fin.sum_univ_three]
  refine ⟨?_, ?_, ?_⟩
  · rw [dlosCol, dlosSTM_ofLp, rhoStar_zero, stmCol1_zero, uStar_zero, hinn]
    simp [ofLp_ofCoords]
  · rw [dlosCol, dlosSTM_ofLp, rhoStar_zero, stmCol1_zero, uStar_zero, hinn]
    simp [ofLp_ofCoords]
  · rw [dlosCol, dlosSTM_ofLp, rhoStar_zero, stmCol1_zero, uStar_zero, hinn]
    simp [ofLp_ofCoords]

lemma dlosCol1_zero : dlosCol 1 0 = ofCoords 0 (2 / 3) 0 := by
  apply (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).injective
  ext i; fin_cases i
  · simpa [ofCoords] using dlosCol1_zero_ofLp.1
  · simpa [ofCoords] using dlosCol1_zero_ofLp.2.1
  · simpa [ofCoords] using dlosCol1_zero_ofLp.2.2

/-! Interval arithmetic for the in-plane STM/dlos block. -/

lemma add_bounds {aLo aHi bLo bHi a b : ℝ}
    (hal : aLo ≤ a) (hah : a ≤ aHi) (hbl : bLo ≤ b) (hbh : b ≤ bHi) :
    aLo + bLo ≤ a + b ∧ a + b ≤ aHi + bHi := by constructor <;> linarith

lemma sub_bounds {aLo aHi bLo bHi a b : ℝ}
    (hal : aLo ≤ a) (hah : a ≤ aHi) (hbl : bLo ≤ b) (hbh : b ≤ bHi) :
    aLo - bHi ≤ a - b ∧ a - b ≤ aHi - bLo := by constructor <;> linarith

lemma mul_nonneg_bounds {aLo aHi bLo bHi a b : ℝ}
    (ha0 : 0 ≤ aLo) (hb0 : 0 ≤ bLo)
    (hal : aLo ≤ a) (hah : a ≤ aHi) (hbl : bLo ≤ b) (hbh : b ≤ bHi) :
    aLo * bLo ≤ a * b ∧ a * b ≤ aHi * bHi := by
  constructor
  · exact mul_le_mul hal hbl hb0 (ha0.trans hal)
  · exact mul_le_mul hah hbh (hb0.trans hbl) (ha0.trans (hal.trans hah))

lemma mul_nonpos_nonneg_bounds {aLo aHi bLo bHi a b : ℝ}
    (ha1 : aHi ≤ 0) (hb0 : 0 ≤ bLo)
    (hal : aLo ≤ a) (hah : a ≤ aHi) (hbl : bLo ≤ b) (hbh : b ≤ bHi) :
    aLo * bHi ≤ a * b ∧ a * b ≤ aHi * bLo := by
  have ha : a ≤ 0 := hah.trans ha1
  have hb : 0 ≤ b := hb0.trans hbl
  constructor <;> nlinarith

lemma inv_pos_bounds {dLo dHi d : ℝ} (hd0 : 0 < dLo)
    (hdl : dLo ≤ d) (hdh : d ≤ dHi) :
    dHi⁻¹ ≤ d⁻¹ ∧ d⁻¹ ≤ dLo⁻¹ := by
  have hd : 0 < d := hd0.trans_le hdl
  have hdHi : 0 < dHi := hd.trans_le hdh
  constructor
  · exact inv_anti₀ hd hdh
  · exact inv_anti₀ hd0 hdl

lemma nStar_pow4 : nStar ^ 4 = (64 / 15625 : ℝ) := by
  calc
    nStar ^ 4 = (nStar ^ 2) ^ 2 := by ring
    _ = (8 / 125) ^ 2 := by rw [nStar_sq]
    _ = 64 / 15625 := by norm_num

lemma nStar_pow6 : nStar ^ 6 = (512 / 1953125 : ℝ) := by
  calc
    nStar ^ 6 = nStar ^ 2 * nStar ^ 4 := by ring
    _ = (8 / 125) * (64 / 15625) := by rw [nStar_sq, nStar_pow4]
    _ = 512 / 1953125 := by norm_num

lemma nStar_div4_sq : (nStar / 4) ^ 2 = (1 / 250 : ℝ) := by
  field_simp; rw [nStar_sq]; norm_num

lemma nStar_div2_sq : (nStar / 2) ^ 2 = (2 / 125 : ℝ) := by
  field_simp; rw [nStar_sq]; norm_num

lemma cosPoly8_nStar_div4 : cosPoly8 (nStar / 4) = (11227507499 / 11250000000 : ℝ) := by
  simp only [cosPoly8]
  have h2 := nStar_div4_sq
  have h4 : (nStar / 4) ^ 4 = (1 / 62500 : ℝ) := by
    calc (nStar / 4) ^ 4 = ((nStar / 4) ^ 2) ^ 2 := by ring
      _ = (1 / 250) ^ 2 := by rw [h2]
      _ = 1 / 62500 := by norm_num
  have h6 : (nStar / 4) ^ 6 = (1 / 15625000 : ℝ) := by
    calc (nStar / 4) ^ 6 = (nStar / 4) ^ 2 * (nStar / 4) ^ 4 := by ring
      _ = (1 / 250) * (1 / 62500) := by rw [h2, h4]
      _ = 1 / 15625000 := by norm_num
  rw [h2, h4, h6]; norm_num

lemma cos_nStar_div4_tight :
    (1257480839887991 / 1260000000000000 : ℝ) ≤ Real.cos (nStar / 4) ∧
      Real.cos (nStar / 4) ≤ (1257480839888009 / 1260000000000000 : ℝ) := by
  have hrem : |nStar / 4| ^ 8 * (9 / 322560) ≤ (1 / 140000000000000 : ℝ) := by
    have habs : |nStar / 4| ^ 2 = (1 / 250 : ℝ) := by
      rw [sq_abs, nStar_div4_sq]
    have h8 : |nStar / 4| ^ 8 = (1 / 3906250000 : ℝ) := by
      calc |nStar / 4| ^ 8 = (|nStar / 4| ^ 2) ^ 4 := by ring
        _ = (1 / 250) ^ 4 := by rw [habs]
        _ = 1 / 3906250000 := by norm_num
    rw [h8]; norm_num
  have h := cos_of_poly8 abs_nStar_div4_le_one hrem
  rw [cosPoly8_nStar_div4] at h
  constructor <;> linarith [h.1, h.2]

lemma cosPoly8_nStar_div2 : cosPoly8 (nStar / 2) = (87188437 / 87890625 : ℝ) := by
  simp only [cosPoly8]
  have h2 := nStar_div2_sq
  have h4 : (nStar / 2) ^ 4 = (4 / 15625 : ℝ) := by
    calc (nStar / 2) ^ 4 = ((nStar / 2) ^ 2) ^ 2 := by ring
      _ = (2 / 125) ^ 2 := by rw [h2]
      _ = 4 / 15625 := by norm_num
  have h6 : (nStar / 2) ^ 6 = (8 / 1953125 : ℝ) := by
    calc (nStar / 2) ^ 6 = (nStar / 2) ^ 2 * (nStar / 2) ^ 4 := by ring
      _ = (2 / 125) * (4 / 15625) := by rw [h2, h4]
      _ = 8 / 1953125 := by norm_num
  rw [h2, h4, h6]; norm_num

lemma cos_nStar_div2_tight :
    (4882552471991 / 4921875000000 : ℝ) ≤ Real.cos (nStar / 2) ∧
      Real.cos (nStar / 2) ≤ (4882552472009 / 4921875000000 : ℝ) := by
  have hrem : |nStar / 2| ^ 8 * (9 / 322560) ≤ (1 / 546875000000 : ℝ) := by
    have habs : |nStar / 2| ^ 2 = (2 / 125 : ℝ) := by
      rw [sq_abs, nStar_div2_sq]
    have h8 : |nStar / 2| ^ 8 = (16 / 244140625 : ℝ) := by
      calc |nStar / 2| ^ 8 = (|nStar / 2| ^ 2) ^ 4 := by ring
        _ = (2 / 125) ^ 4 := by rw [habs]
        _ = 16 / 244140625 := by norm_num
    rw [h8]; norm_num
  have h := cos_of_poly8 abs_nStar_div2_le_one hrem
  rw [cosPoly8_nStar_div2] at h
  constructor <;> linarith [h.1, h.2]

lemma cosPoly8_nStar : cosPoly8 nStar = (85093093 / 87890625 : ℝ) := by
  simp only [cosPoly8]
  rw [nStar_sq, nStar_pow4, nStar_pow6]; norm_num

lemma cos_nStar_tight :
    (74456456339 / 76904296875 : ℝ) ≤ Real.cos nStar ∧
      Real.cos nStar ≤ (74456456411 / 76904296875 : ℝ) := by
  have hrem : |nStar| ^ 8 * (9 / 322560) ≤ (4 / 8544921875 : ℝ) := by
    rw [abs_of_nonneg nStar_pos.le, nStar_pow8]; norm_num
  have h := cos_of_poly8 abs_nStar_le_one hrem
  rw [cosPoly8_nStar] at h
  constructor <;> linarith [h.1, h.2]

lemma sinPoly9_factor_div4 :
    sinPoly9 (nStar / 4) = (nStar / 4) * (78697510499 / 78750000000 : ℝ) := by
  simp only [sinPoly9]
  have h2 := nStar_div4_sq
  have h4 : (nStar / 4) ^ 4 = (1 / 62500 : ℝ) := by
    calc (nStar / 4) ^ 4 = ((nStar / 4) ^ 2) ^ 2 := by ring
      _ = (1 / 250) ^ 2 := by rw [h2]
      _ = 1 / 62500 := by norm_num
  have h6 : (nStar / 4) ^ 6 = (1 / 15625000 : ℝ) := by
    calc (nStar / 4) ^ 6 = (nStar / 4) ^ 2 * (nStar / 4) ^ 4 := by ring
      _ = (1 / 250) * (1 / 62500) := by rw [h2, h4]
      _ = 1 / 15625000 := by norm_num
  have hx3 : (nStar / 4) ^ 3 = (nStar / 4) * (nStar / 4) ^ 2 := by ring
  have hx5 : (nStar / 4) ^ 5 = (nStar / 4) * (nStar / 4) ^ 4 := by ring
  have hx7 : (nStar / 4) ^ 7 = (nStar / 4) * (nStar / 4) ^ 6 := by ring
  rw [hx3, hx5, hx7, h2, h4, h6]
  ring

lemma sin_nStar_div4_tight :
    (63203 / 1000000 : ℝ) ≤ Real.sin (nStar / 4) ∧
      Real.sin (nStar / 4) ≤ (63204 / 1000000 : ℝ) := by
  have hQ : (0 : ℝ) ≤ 78697510499 / 78750000000 := by norm_num
  have hrem : |nStar / 4| ^ 9 * (10 / 3265920) ≤ (1 / 10000000000000000 : ℝ) := by
    have : |nStar / 4| ≤ (252983 / 4000000 : ℝ) := by
      rw [abs_of_nonneg (div_nonneg nStar_pos.le (by norm_num))]
      linarith [nStar_lt_tight]
    have : |nStar / 4| ^ 9 ≤ (252983 / 4000000 : ℝ) ^ 9 :=
      pow_le_pow_left₀ (abs_nonneg _) this 9
    nlinarith
  have h := sin_of_poly9 abs_nStar_div4_le_one hrem
  rw [sinPoly9_factor_div4] at h
  have hlo : (252982 / 4000000 : ℝ) * (78697510499 / 78750000000)
      ≤ (nStar / 4) * (78697510499 / 78750000000) :=
    mul_le_mul_of_nonneg_right (by linarith [nStar_gt_tight] : (252982 / 4000000 : ℝ) ≤ nStar / 4) hQ
  have hhi : (nStar / 4) * (78697510499 / 78750000000)
      ≤ (252983 / 4000000 : ℝ) * (78697510499 / 78750000000) :=
    mul_le_mul_of_nonneg_right (by linarith [nStar_lt_tight] : nStar / 4 ≤ (252983 / 4000000 : ℝ)) hQ
  constructor <;> nlinarith [h.1, h.2, hlo, hhi]

lemma sinPoly9_factor_div2 :
    sinPoly9 (nStar / 2) = (nStar / 2) * (613595062 / 615234375 : ℝ) := by
  simp only [sinPoly9]
  have h2 := nStar_div2_sq
  have h4 : (nStar / 2) ^ 4 = (4 / 15625 : ℝ) := by
    calc (nStar / 2) ^ 4 = ((nStar / 2) ^ 2) ^ 2 := by ring
      _ = (2 / 125) ^ 2 := by rw [h2]
      _ = 4 / 15625 := by norm_num
  have h6 : (nStar / 2) ^ 6 = (8 / 1953125 : ℝ) := by
    calc (nStar / 2) ^ 6 = (nStar / 2) ^ 2 * (nStar / 2) ^ 4 := by ring
      _ = (2 / 125) * (4 / 15625) := by rw [h2, h4]
      _ = 8 / 1953125 := by norm_num
  have hx3 : (nStar / 2) ^ 3 = (nStar / 2) * (nStar / 2) ^ 2 := by ring
  have hx5 : (nStar / 2) ^ 5 = (nStar / 2) * (nStar / 2) ^ 4 := by ring
  have hx7 : (nStar / 2) ^ 7 = (nStar / 2) * (nStar / 2) ^ 6 := by ring
  rw [hx3, hx5, hx7, h2, h4, h6]
  ring

lemma sin_nStar_div2_tight :
    (126153 / 1000000 : ℝ) ≤ Real.sin (nStar / 2) ∧
      Real.sin (nStar / 2) ≤ (126155 / 1000000 : ℝ) := by
  have hQ : (0 : ℝ) ≤ 613595062 / 615234375 := by norm_num
  have hrem : |nStar / 2| ^ 9 * (10 / 3265920) ≤ (1 / 10000000000000 : ℝ) := by
    have : |nStar / 2| ≤ (252983 / 2000000 : ℝ) := by
      rw [abs_of_nonneg (div_nonneg nStar_pos.le (by norm_num))]
      linarith [nStar_lt_tight]
    have : |nStar / 2| ^ 9 ≤ (252983 / 2000000 : ℝ) ^ 9 :=
      pow_le_pow_left₀ (abs_nonneg _) this 9
    nlinarith
  have h := sin_of_poly9 abs_nStar_div2_le_one hrem
  rw [sinPoly9_factor_div2] at h
  have hlo : (252982 / 2000000 : ℝ) * (613595062 / 615234375)
      ≤ (nStar / 2) * (613595062 / 615234375) :=
    mul_le_mul_of_nonneg_right (by linarith [nStar_gt_tight] : (252982 / 2000000 : ℝ) ≤ nStar / 2) hQ
  have hhi : (nStar / 2) * (613595062 / 615234375)
      ≤ (252983 / 2000000 : ℝ) * (613595062 / 615234375) :=
    mul_le_mul_of_nonneg_right (by linarith [nStar_lt_tight] : nStar / 2 ≤ (252983 / 2000000 : ℝ)) hQ
  constructor <;> nlinarith [h.1, h.2, hlo, hhi]

lemma sinPoly9_factor_nStar :
    sinPoly9 nStar = nStar * (608692843 / 615234375 : ℝ) := by
  simp only [sinPoly9]
  have hx3 : nStar ^ 3 = nStar * nStar ^ 2 := by ring
  have hx5 : nStar ^ 5 = nStar * nStar ^ 4 := by ring
  have hx7 : nStar ^ 7 = nStar * nStar ^ 6 := by ring
  rw [hx3, hx5, hx7, nStar_sq, nStar_pow4, nStar_pow6]
  ring

lemma sin_nStar_tight :
    (250292 / 1000000 : ℝ) ≤ Real.sin nStar ∧
      Real.sin nStar ≤ (250294 / 1000000 : ℝ) := by
  have hQ : (0 : ℝ) ≤ 608692843 / 615234375 := by norm_num
  have hrem : |nStar| ^ 9 * (10 / 3265920) ≤ (1 / 10000000000 : ℝ) := by
    have : |nStar| ≤ (252983 / 1000000 : ℝ) := by
      rw [abs_of_nonneg nStar_pos.le]; exact nStar_lt_tight.le
    have : |nStar| ^ 9 ≤ (252983 / 1000000 : ℝ) ^ 9 :=
      pow_le_pow_left₀ (abs_nonneg _) this 9
    nlinarith
  have h := sin_of_poly9 abs_nStar_le_one hrem
  rw [sinPoly9_factor_nStar] at h
  have hlo : (252982 / 1000000 : ℝ) * (608692843 / 615234375)
      ≤ nStar * (608692843 / 615234375) :=
    mul_le_mul_of_nonneg_right nStar_gt_tight.le hQ
  have hhi : nStar * (608692843 / 615234375)
      ≤ (252983 / 1000000 : ℝ) * (608692843 / 615234375) :=
    mul_le_mul_of_nonneg_right nStar_lt_tight.le hQ
  constructor <;> nlinarith [h.1, h.2, hlo, hhi]

lemma one_sub_nStar_tight :
    (747017 / 1000000 : ℝ) < 1 - nStar ∧ 1 - nStar < (747018 / 1000000 : ℝ) := by
  constructor <;> linarith [nStar_gt_tight, nStar_lt_tight]

lemma abs_nm1_div4_tight :
    (747017 / 4000000 : ℝ) < |(nStar - 1) * (1 / 4)| ∧
      |(nStar - 1) * (1 / 4)| < (747018 / 4000000 : ℝ) := by
  have hx : |(nStar - 1) * (1 / 4)| = (1 - nStar) / 4 := by
    simpa [div_eq_mul_inv] using abs_nm1_mul_nonneg (1 / 4) (by norm_num)
  rw [hx]
  constructor <;> linarith [one_sub_nStar_tight.1, one_sub_nStar_tight.2]

lemma abs_nm1_div2_tight :
    (747017 / 2000000 : ℝ) < |(nStar - 1) * (1 / 2)| ∧
      |(nStar - 1) * (1 / 2)| < (747018 / 2000000 : ℝ) := by
  have hx : |(nStar - 1) * (1 / 2)| = (1 - nStar) / 2 := by
    simpa [div_eq_mul_inv] using abs_nm1_mul_nonneg (1 / 2) (by norm_num)
  rw [hx]
  constructor <;> linarith [one_sub_nStar_tight.1, one_sub_nStar_tight.2]

lemma abs_nm1_one_tight :
    (747017 / 1000000 : ℝ) < |nStar - 1| ∧ |nStar - 1| < (747018 / 1000000 : ℝ) := by
  have hx : |nStar - 1| = 1 - nStar := by
    rw [abs_of_nonpos (sub_nonpos.mpr nStar_lt_one.le), neg_sub]
  rw [hx]; exact one_sub_nStar_tight

lemma pow_even_abs (x : ℝ) :
    x ^ 2 = |x| ^ 2 ∧ x ^ 4 = |x| ^ 4 ∧ x ^ 6 = |x| ^ 6 := by
  have h2 : x ^ 2 = |x| ^ 2 := (sq_abs x).symm
  have h4 : x ^ 4 = |x| ^ 4 := by
    calc x ^ 4 = (x ^ 2) ^ 2 := by ring
      _ = (|x| ^ 2) ^ 2 := by rw [h2]
      _ = |x| ^ 4 := by ring
  have h6 : x ^ 6 = |x| ^ 6 := by
    calc x ^ 6 = x ^ 2 * x ^ 4 := by ring
      _ = |x| ^ 2 * |x| ^ 4 := by rw [h2, h4]
      _ = |x| ^ 6 := by ring
  exact ⟨h2, h4, h6⟩

lemma cosPoly8_abs (x : ℝ) :
    cosPoly8 x = 1 - |x| ^ 2 / 2 + |x| ^ 4 / 24 - |x| ^ 6 / 720 := by
  simp only [cosPoly8]
  have h := pow_even_abs x
  rw [h.1, h.2.1, h.2.2]

lemma rem8_of_le {x A B : ℝ} (hx : |x| ≤ A) (hA : 0 ≤ A)
    (hAB : A ^ 8 * (9 / 322560) ≤ B) :
    |x| ^ 8 * (9 / 322560) ≤ B := by
  have := pow_le_pow_left₀ (abs_nonneg x) hx 8
  have := mul_le_mul_of_nonneg_right this (by norm_num : (0 : ℝ) ≤ 9 / 322560)
  exact this.trans hAB

lemma cos_nm1_div4_tight :
    (982612 / 1000000 : ℝ) ≤ Real.cos ((nStar - 1) * (1 / 4)) ∧
      Real.cos ((nStar - 1) * (1 / 4)) ≤ (982613 / 1000000 : ℝ) := by
  have habs : |(nStar - 1) * (1 / 4)| ≤ 1 := by linarith [abs_nm1_div4_tight.2]
  have hA : |(nStar - 1) * (1 / 4)| ≤ (747018 / 4000000 : ℝ) :=
    abs_nm1_div4_tight.2.le
  have hrem : |(nStar - 1) * (1 / 4)| ^ 8 * (9 / 322560) ≤ (1 / 10000000000 : ℝ) :=
    rem8_of_le hA (by norm_num) (by norm_num)
  have h := cos_of_poly8 habs hrem
  rw [cosPoly8_abs] at h
  have hx2lo : (747017 / 4000000 : ℝ) ^ 2 ≤ |(nStar - 1) * (1 / 4)| ^ 2 :=
    pow_le_pow_left₀ (by norm_num) abs_nm1_div4_tight.1.le 2
  have hx2hi : |(nStar - 1) * (1 / 4)| ^ 2 ≤ (747018 / 4000000 : ℝ) ^ 2 :=
    pow_le_pow_left₀ (abs_nonneg _) hA 2
  have hx6hi : |(nStar - 1) * (1 / 4)| ^ 6 ≤ (747018 / 4000000 : ℝ) ^ 6 :=
    pow_le_pow_left₀ (abs_nonneg _) hA 6
  have hx4hi : |(nStar - 1) * (1 / 4)| ^ 4 ≤ (747018 / 4000000 : ℝ) ^ 4 :=
    pow_le_pow_left₀ (abs_nonneg _) hA 4
  -- poly ≥ 1 - x²/2 - x⁶/720
  have hx4lo : (747017 / 4000000 : ℝ) ^ 4 ≤ |(nStar - 1) * (1 / 4)| ^ 4 :=
    pow_le_pow_left₀ (by norm_num) abs_nm1_div4_tight.1.le 4
  have hx6lo : (747017 / 4000000 : ℝ) ^ 6 ≤ |(nStar - 1) * (1 / 4)| ^ 6 :=
    pow_le_pow_left₀ (by norm_num) abs_nm1_div4_tight.1.le 6
  have hlo : (982612 / 1000000 : ℝ)
      ≤ 1 - (747018 / 4000000 : ℝ) ^ 2 / 2 + (747017 / 4000000 : ℝ) ^ 4 / 24
        - (747018 / 4000000 : ℝ) ^ 6 / 720 - (1 / 10000000000 : ℝ) := by
    norm_num
  have hhi : 1 - (747017 / 4000000 : ℝ) ^ 2 / 2 + (747018 / 4000000 : ℝ) ^ 4 / 24
      - (747017 / 4000000 : ℝ) ^ 6 / 720 + (1 / 10000000000 : ℝ)
      ≤ (982613 / 1000000 : ℝ) := by
    norm_num
  constructor
  · nlinarith [h.1, hx2hi, hx4lo, hx6hi, hlo]
  · nlinarith [h.2, hx2lo, hx4hi, hx6lo, hhi]

lemma cos_nm1_div2_tight :
    (931052 / 1000000 : ℝ) ≤ Real.cos ((nStar - 1) * (1 / 2)) ∧
      Real.cos ((nStar - 1) * (1 / 2)) ≤ (931054 / 1000000 : ℝ) := by
  have habs : |(nStar - 1) * (1 / 2)| ≤ 1 := by linarith [abs_nm1_div2_tight.2]
  have hA : |(nStar - 1) * (1 / 2)| ≤ (747018 / 2000000 : ℝ) :=
    abs_nm1_div2_tight.2.le
  have hrem : |(nStar - 1) * (1 / 2)| ^ 8 * (9 / 322560) ≤ (2 / 100000000 : ℝ) :=
    rem8_of_le hA (by norm_num) (by norm_num)
  have h := cos_of_poly8 habs hrem
  rw [cosPoly8_abs] at h
  have hx2 : ((nStar - 1) * (1 / 2)) ^ 2 = |(nStar - 1) * (1 / 2)| ^ 2 := by
    rw [sq_abs]
  have hx2lo : (747017 / 2000000 : ℝ) ^ 2 ≤ |(nStar - 1) * (1 / 2)| ^ 2 :=
    pow_le_pow_left₀ (by norm_num) abs_nm1_div2_tight.1.le 2
  have hx2hi : |(nStar - 1) * (1 / 2)| ^ 2 ≤ (747018 / 2000000 : ℝ) ^ 2 :=
    pow_le_pow_left₀ (abs_nonneg _) hA 2
  have hx6hi : |(nStar - 1) * (1 / 2)| ^ 6 ≤ (747018 / 2000000 : ℝ) ^ 6 :=
    pow_le_pow_left₀ (abs_nonneg _) hA 6
  have hx4hi : |(nStar - 1) * (1 / 2)| ^ 4 ≤ (747018 / 2000000 : ℝ) ^ 4 :=
    pow_le_pow_left₀ (abs_nonneg _) hA 4
  have hx4lo : (747017 / 2000000 : ℝ) ^ 4 ≤ |(nStar - 1) * (1 / 2)| ^ 4 :=
    pow_le_pow_left₀ (by norm_num) abs_nm1_div2_tight.1.le 4
  have hx6lo : (747017 / 2000000 : ℝ) ^ 6 ≤ |(nStar - 1) * (1 / 2)| ^ 6 :=
    pow_le_pow_left₀ (by norm_num) abs_nm1_div2_tight.1.le 6
  have hlo : (931052 / 1000000 : ℝ)
      ≤ 1 - (747018 / 2000000 : ℝ) ^ 2 / 2 + (747017 / 2000000 : ℝ) ^ 4 / 24
        - (747018 / 2000000 : ℝ) ^ 6 / 720 - (2 / 100000000 : ℝ) := by
    norm_num
  have hhi : 1 - (747017 / 2000000 : ℝ) ^ 2 / 2 + (747018 / 2000000 : ℝ) ^ 4 / 24
      - (747017 / 2000000 : ℝ) ^ 6 / 720 + (2 / 100000000 : ℝ)
      ≤ (931054 / 1000000 : ℝ) := by
    norm_num
  constructor
  · nlinarith [h.1, hx2hi, hx4lo, hx6hi, hlo]
  · nlinarith [h.2, hx2lo, hx4hi, hx6lo, hhi]

lemma cos_nm1_one_tight :
    (733705 / 1000000 : ℝ) ≤ Real.cos (nStar - 1) ∧
      Real.cos (nStar - 1) ≤ (733727 / 1000000 : ℝ) := by
  have habs : |nStar - 1| ≤ 1 := by linarith [abs_nm1_one_tight.2]
  have hA : |nStar - 1| ≤ (747018 / 1000000 : ℝ) := abs_nm1_one_tight.2.le
  have hrem : |nStar - 1| ^ 8 * (9 / 322560) ≤ (1 / 100000 : ℝ) :=
    rem8_of_le hA (by norm_num) (by norm_num)
  have h := cos_of_poly8 habs hrem
  rw [cosPoly8_abs] at h
  have hx2 : (nStar - 1) ^ 2 = |nStar - 1| ^ 2 := by rw [sq_abs]
  have hx2lo : (747017 / 1000000 : ℝ) ^ 2 ≤ |nStar - 1| ^ 2 :=
    pow_le_pow_left₀ (by norm_num) abs_nm1_one_tight.1.le 2
  have hx2hi : |nStar - 1| ^ 2 ≤ (747018 / 1000000 : ℝ) ^ 2 :=
    pow_le_pow_left₀ (abs_nonneg _) hA 2
  have hx6hi : |nStar - 1| ^ 6 ≤ (747018 / 1000000 : ℝ) ^ 6 :=
    pow_le_pow_left₀ (abs_nonneg _) hA 6
  have hx4hi : |nStar - 1| ^ 4 ≤ (747018 / 1000000 : ℝ) ^ 4 :=
    pow_le_pow_left₀ (abs_nonneg _) hA 4
  have hx4lo : (747017 / 1000000 : ℝ) ^ 4 ≤ |nStar - 1| ^ 4 :=
    pow_le_pow_left₀ (by norm_num) abs_nm1_one_tight.1.le 4
  have hx6lo : (747017 / 1000000 : ℝ) ^ 6 ≤ |nStar - 1| ^ 6 :=
    pow_le_pow_left₀ (by norm_num) abs_nm1_one_tight.1.le 6
  have hlo : (733705 / 1000000 : ℝ)
      ≤ 1 - (747018 / 1000000 : ℝ) ^ 2 / 2 + (747017 / 1000000 : ℝ) ^ 4 / 24
        - (747018 / 1000000 : ℝ) ^ 6 / 720 - (1 / 100000 : ℝ) := by
    norm_num
  have hhi : 1 - (747017 / 1000000 : ℝ) ^ 2 / 2 + (747018 / 1000000 : ℝ) ^ 4 / 24
      - (747017 / 1000000 : ℝ) ^ 6 / 720 + (1 / 100000 : ℝ)
      ≤ (733727 / 1000000 : ℝ) := by
    norm_num
  constructor
  · nlinarith [h.1, hx2hi, hx4lo, hx6hi, hlo]
  · nlinarith [h.2, hx2lo, hx4hi, hx6lo, hhi]

lemma rhoStar_sq_div4_tight :
    (2336935 / 1000000 : ℝ) ≤ rhoStar (1 / 4) ^ 2 ∧
      rhoStar (1 / 4) ^ 2 ≤ (2336940 / 1000000 : ℝ) := by
  rw [rhoStar_sq_cos]
  constructor <;> nlinarith [cos_nm1_div4_tight.1, cos_nm1_div4_tight.2]

lemma rhoStar_sq_div2_tight :
    (2594730 / 1000000 : ℝ) ≤ rhoStar (1 / 2) ^ 2 ∧
      rhoStar (1 / 2) ^ 2 ≤ (2594740 / 1000000 : ℝ) := by
  rw [rhoStar_sq_cos]
  constructor <;> nlinarith [cos_nm1_div2_tight.1, cos_nm1_div2_tight.2]

lemma rhoStar_sq_one_tight :
    (3581365 / 1000000 : ℝ) ≤ rhoStar 1 ^ 2 ∧
      rhoStar 1 ^ 2 ≤ (3581475 / 1000000 : ℝ) := by
  have : (nStar - 1) * (1 : ℝ) = nStar - 1 := by ring
  rw [rhoStar_sq_cos, this]
  constructor <;> nlinarith [cos_nm1_one_tight.1, cos_nm1_one_tight.2]

lemma rhoStar_div4_tight :
    (1528702 / 1000000 : ℝ) ≤ rhoStar (1 / 4) ∧
      rhoStar (1 / 4) ≤ (1528708 / 1000000 : ℝ) := by
  have hr := rhoStar_sq_div4_tight
  constructor
  · refine le_rho_of_sq (by norm_num) (le_trans ?_ hr.1); norm_num
  · refine rho_of_sq_le (by norm_num) (le_trans hr.2 ?_); norm_num

lemma rhoStar_div2_tight :
    (1610815 / 1000000 : ℝ) ≤ rhoStar (1 / 2) ∧
      rhoStar (1 / 2) ≤ (1610822 / 1000000 : ℝ) := by
  have hr := rhoStar_sq_div2_tight
  constructor
  · refine le_rho_of_sq (by norm_num) (le_trans ?_ hr.1); norm_num
  · refine rho_of_sq_le (by norm_num) (le_trans hr.2 ?_); norm_num

lemma rhoStar_one_tight :
    (1892420 / 1000000 : ℝ) ≤ rhoStar 1 ∧
      rhoStar 1 ≤ (1892500 / 1000000 : ℝ) := by
  have hr := rhoStar_sq_one_tight
  constructor
  · refine le_rho_of_sq (by norm_num) (le_trans ?_ hr.1); norm_num
  · refine rho_of_sq_le (by norm_num) (le_trans hr.2 ?_); norm_num

lemma stmCol0_ofLp (t : ℝ) :
    (stmCol 0 t).ofLp 0 =
      (2 - Real.cos (nStar * t)) * Real.cos (nStar * t)
        - (2 * Real.sin (nStar * t) - 3 * nStar * t) * Real.sin (nStar * t) ∧
    (stmCol 0 t).ofLp 1 =
      (2 - Real.cos (nStar * t)) * Real.sin (nStar * t)
        + (2 * Real.sin (nStar * t) - 3 * nStar * t) * Real.cos (nStar * t) ∧
    (stmCol 0 t).ofLp 2 = 0 := by
  rw [stmCol_dx_coords]; simp [ofLp_ofCoords]

lemma stmCol1_ofLp (t : ℝ) :
    (stmCol 1 t).ofLp 0 = Real.sin (nStar * t) * (1 - Real.cos (nStar * t)) ∧
    (stmCol 1 t).ofLp 1 = 1 - Real.cos (nStar * t) + Real.cos (nStar * t) ^ 2 ∧
    (stmCol 1 t).ofLp 2 = 0 := by
  rw [stmCol_dy]; simp [ofLp_ofCoords]

lemma stmCol2_ofLp (t : ℝ) :
    (stmCol 2 t).ofLp 0 =
      Real.sin (nStar * t) / nStar * Real.cos (nStar * t)
        + 2 * (1 - Real.cos (nStar * t)) * Real.sin (nStar * t) / nStar ∧
    (stmCol 2 t).ofLp 1 =
      Real.sin (nStar * t) / nStar * Real.sin (nStar * t)
        - 2 * (1 - Real.cos (nStar * t)) * Real.cos (nStar * t) / nStar ∧
    (stmCol 2 t).ofLp 2 = 0 := by
  rw [stmCol_dvx]; simp [ofLp_ofCoords]

lemma stmCol3_ofLp (t : ℝ) :
    (stmCol 3 t).ofLp 0 =
      (2 * (1 - Real.cos (nStar * t)) / nStar) * Real.cos (nStar * t)
        - ((4 * Real.sin (nStar * t) - 3 * nStar * t) / nStar) * Real.sin (nStar * t) ∧
    (stmCol 3 t).ofLp 1 =
      (2 * (1 - Real.cos (nStar * t)) / nStar) * Real.sin (nStar * t)
        + ((4 * Real.sin (nStar * t) - 3 * nStar * t) / nStar) * Real.cos (nStar * t) ∧
    (stmCol 3 t).ofLp 2 = 0 := by
  rw [stmCol_dvy_coords]; simp [ofLp_ofCoords]

lemma inner_uStar_stm (t : ℝ) (dr : Vec) :
    ⟪uStar t, dr⟫ = (uStar t).ofLp 0 * dr.ofLp 0 + (uStar t).ofLp 1 * dr.ofLp 1
      + (uStar t).ofLp 2 * dr.ofLp 2 := by
  rw [← vecDot_eq_inner]
  simp [vecDot, Fin.sum_univ_three]

lemma dlosSTM_ofLp01 (t : ℝ) (dr : Vec) :
    (dlosSTM t dr).ofLp 0 =
      (rhoStar t)⁻¹ * (dr.ofLp 0 - ⟪uStar t, dr⟫ * (uStar t).ofLp 0) ∧
    (dlosSTM t dr).ofLp 1 =
      (rhoStar t)⁻¹ * (dr.ofLp 1 - ⟪uStar t, dr⟫ * (uStar t).ofLp 1) := by
  constructor <;> rw [dlosSTM_ofLp]


lemma mul_nonneg_nonpos_bounds {aLo aHi bLo bHi a b : ℝ}
    (ha0 : 0 ≤ aLo) (hb1 : bHi ≤ 0)
    (hal : aLo ≤ a) (hah : a ≤ aHi) (hbl : bLo ≤ b) (hbh : b ≤ bHi) :
    aHi * bLo ≤ a * b ∧ a * b ≤ aLo * bHi := by
  have ha : 0 ≤ a := ha0.trans hal
  have hb : b ≤ 0 := hbh.trans hb1
  constructor <;> nlinarith

lemma mul_nonpos_nonpos_bounds {aLo aHi bLo bHi a b : ℝ}
    (ha1 : aHi ≤ 0) (hb1 : bHi ≤ 0)
    (hal : aLo ≤ a) (hah : a ≤ aHi) (hbl : bLo ≤ b) (hbh : b ≤ bHi) :
    aHi * bHi ≤ a * b ∧ a * b ≤ aLo * bLo := by
  have ha : a ≤ 0 := hah.trans ha1
  have hb : b ≤ 0 := hbh.trans hb1
  constructor <;> nlinarith

lemma nStar_mul_div4 : nStar * (1 / 4) = nStar / 4 := by ring
lemma nStar_mul_div2 : nStar * (1 / 2) = nStar / 2 := by ring

lemma inv_nStar_tight :
    (3952834 / 1000000 : ℝ) ≤ nStar⁻¹ ∧ nStar⁻¹ ≤ (3952851 / 1000000 : ℝ) := by
  have h := inv_pos_bounds (by norm_num : (0 : ℝ) < 252982 / 1000000)
    nStar_gt_tight.le nStar_lt_tight.le
  constructor <;> nlinarith [h.1, h.2]

lemma inv_rhoStar_div4_tight :
    (654147 / 1000000 : ℝ) ≤ (rhoStar (1 / 4))⁻¹ ∧
      (rhoStar (1 / 4))⁻¹ ≤ (654150 / 1000000 : ℝ) := by
  have h := inv_pos_bounds (by norm_num) rhoStar_div4_tight.1 rhoStar_div4_tight.2
  constructor <;> nlinarith [h.1, h.2]

lemma inv_rhoStar_div2_tight :
    (620801 / 1000000 : ℝ) ≤ (rhoStar (1 / 2))⁻¹ ∧
      (rhoStar (1 / 2))⁻¹ ≤ (620804 / 1000000 : ℝ) := by
  have h := inv_pos_bounds (by norm_num) rhoStar_div2_tight.1 rhoStar_div2_tight.2
  constructor <;> nlinarith [h.1, h.2]

lemma inv_rhoStar_one_tight :
    (528401 / 1000000 : ℝ) ≤ (rhoStar 1)⁻¹ ∧
      (rhoStar 1)⁻¹ ≤ (528424 / 1000000 : ℝ) := by
  have h := inv_pos_bounds (by norm_num) rhoStar_one_tight.1 rhoStar_one_tight.2
  constructor <;> nlinarith [h.1, h.2]

lemma cos_nStar_div4_milli :
    (998000 / 1000000 : ℝ) ≤ Real.cos (nStar / 4) ∧
      Real.cos (nStar / 4) ≤ (998001 / 1000000 : ℝ) := by
  have h := cos_nStar_div4_tight
  constructor <;> nlinarith [h.1, h.2]

lemma cos_nStar_div2_milli :
    (992010 / 1000000 : ℝ) ≤ Real.cos (nStar / 2) ∧
      Real.cos (nStar / 2) ≤ (992011 / 1000000 : ℝ) := by
  have h := cos_nStar_div2_tight
  constructor <;> nlinarith [h.1, h.2]

lemma cos_nStar_milli :
    (968170 / 1000000 : ℝ) ≤ Real.cos nStar ∧
      Real.cos nStar ≤ (968171 / 1000000 : ℝ) := by
  have h := cos_nStar_tight
  constructor <;> nlinarith [h.1, h.2]

lemma cos_quarter_milli :
    (968912 / 1000000 : ℝ) ≤ Real.cos (1 / 4) ∧
      Real.cos (1 / 4) ≤ (968913 / 1000000 : ℝ) := by
  have h := cos_quarter_tight
  constructor <;> nlinarith [h.1, h.2]

lemma cos_half_milli :
    (877582 / 1000000 : ℝ) ≤ Real.cos (1 / 2) ∧
      Real.cos (1 / 2) ≤ (877583 / 1000000 : ℝ) := by
  have h := cos_half_tight
  constructor <;> nlinarith [h.1, h.2]

lemma cos_one_milli :
    (540249 / 1000000 : ℝ) ≤ Real.cos 1 ∧ Real.cos 1 ≤ (540306 / 1000000 : ℝ) := by
  have h := cos_one_tight
  constructor <;> nlinarith [h.1, h.2]

lemma sin_quarter_milli :
    (247403 / 1000000 : ℝ) ≤ Real.sin (1 / 4) ∧
      Real.sin (1 / 4) ≤ (247404 / 1000000 : ℝ) := by
  have h := sin_quarter_tight
  constructor <;> nlinarith [h.1, h.2]

lemma sin_half_milli :
    (479425 / 1000000 : ℝ) ≤ Real.sin (1 / 2) ∧
      Real.sin (1 / 2) ≤ (479426 / 1000000 : ℝ) := by
  have h := sin_half_tight
  constructor <;> nlinarith [h.1, h.2]

lemma sin_one_milli :
    (841465 / 1000000 : ℝ) ≤ Real.sin 1 ∧ Real.sin 1 ≤ (841472 / 1000000 : ℝ) := by
  have h := sin_one_tight
  constructor <;> nlinarith [h.1, h.2]

lemma ofLp_add (u v : Vec) (i : Fin 3) : (u + v).ofLp i = u.ofLp i + v.ofLp i := by
  simp [PiLp.add_apply]

lemma ofLp_sub (u v : Vec) (i : Fin 3) : (u - v).ofLp i = u.ofLp i - v.ofLp i := by
  simp [PiLp.sub_apply]

lemma ofLp_smul (c : ℝ) (u : Vec) (i : Fin 3) : (c • u).ofLp i = c * u.ofLp i := by
  simp [PiLp.smul_apply, smul_eq_mul]

lemma secondDiff_dlos_ofLp (j : Fin 4) (h : ℝ) (i : Fin 3) :
    (dlosCol j 0 - (2 : ℝ) • dlosCol j h + dlosCol j (2 * h)).ofLp i =
      (dlosCol j 0).ofLp i - 2 * (dlosCol j h).ofLp i + (dlosCol j (2 * h)).ofLp i := by
  simp [ofLp_add, ofLp_sub, ofLp_smul]

lemma uStar_ofLp2_zero (t : ℝ) : (uStar t).ofLp 2 = 0 := uStar_ofLp2 t

lemma inner_uStar_stm_xy (t : ℝ) (dr : Vec) :
    ⟪uStar t, dr⟫ = (uStar t).ofLp 0 * dr.ofLp 0 + (uStar t).ofLp 1 * dr.ofLp 1 := by
  rw [inner_uStar_stm]; simp [uStar_ofLp2]


lemma two_sub_cos_nStar_div4 :
    (1001999 / 1000000 : ℝ) ≤ 2 - Real.cos (nStar / 4) ∧
      2 - Real.cos (nStar / 4) ≤ (1002000 / 1000000 : ℝ) := by
  have h := cos_nStar_div4_milli
  constructor <;> nlinarith [h.1, h.2]

lemma two_sub_cos_nStar_div2 :
    (1007989 / 1000000 : ℝ) ≤ 2 - Real.cos (nStar / 2) ∧
      2 - Real.cos (nStar / 2) ≤ (1007990 / 1000000 : ℝ) := by
  have h := cos_nStar_div2_milli
  constructor <;> nlinarith [h.1, h.2]

lemma two_sub_cos_nStar :
    (1031829 / 1000000 : ℝ) ≤ 2 - Real.cos nStar ∧
      2 - Real.cos nStar ≤ (1031830 / 1000000 : ℝ) := by
  have h := cos_nStar_milli
  constructor <;> nlinarith [h.1, h.2]

lemma one_sub_cos_nStar_div4 :
    (1999 / 1000000 : ℝ) ≤ 1 - Real.cos (nStar / 4) ∧
      1 - Real.cos (nStar / 4) ≤ (2000 / 1000000 : ℝ) := by
  have h := cos_nStar_div4_milli
  constructor <;> nlinarith [h.1, h.2]

lemma one_sub_cos_nStar_div2 :
    (7989 / 1000000 : ℝ) ≤ 1 - Real.cos (nStar / 2) ∧
      1 - Real.cos (nStar / 2) ≤ (7990 / 1000000 : ℝ) := by
  have h := cos_nStar_div2_milli
  constructor <;> nlinarith [h.1, h.2]

lemma one_sub_cos_nStar :
    (31829 / 1000000 : ℝ) ≤ 1 - Real.cos nStar ∧
      1 - Real.cos nStar ≤ (31830 / 1000000 : ℝ) := by
  have h := cos_nStar_milli
  constructor <;> nlinarith [h.1, h.2]

lemma two_sin_nStar_div4 :
    (126406 / 1000000 : ℝ) ≤ 2 * Real.sin (nStar / 4) ∧
      2 * Real.sin (nStar / 4) ≤ (126408 / 1000000 : ℝ) := by
  have h := sin_nStar_div4_tight
  constructor <;> nlinarith [h.1, h.2]

lemma two_sin_nStar_div2 :
    (252306 / 1000000 : ℝ) ≤ 2 * Real.sin (nStar / 2) ∧
      2 * Real.sin (nStar / 2) ≤ (252310 / 1000000 : ℝ) := by
  have h := sin_nStar_div2_tight
  constructor <;> nlinarith [h.1, h.2]

lemma two_sin_nStar :
    (500584 / 1000000 : ℝ) ≤ 2 * Real.sin nStar ∧
      2 * Real.sin nStar ≤ (500588 / 1000000 : ℝ) := by
  have h := sin_nStar_tight
  constructor <;> nlinarith [h.1, h.2]

lemma three_nStar_div4 :
    (189736 / 1000000 : ℝ) ≤ 3 * (nStar / 4) ∧
      3 * (nStar / 4) ≤ (189738 / 1000000 : ℝ) := by
  have h := nStar_tight
  constructor <;> nlinarith [h.1, h.2]

lemma three_nStar_div2 :
    (379473 / 1000000 : ℝ) ≤ 3 * (nStar / 2) ∧
      3 * (nStar / 2) ≤ (379475 / 1000000 : ℝ) := by
  have h := nStar_tight
  constructor <;> nlinarith [h.1, h.2]

lemma three_nStar :
    (758946 / 1000000 : ℝ) ≤ 3 * nStar ∧
      3 * nStar ≤ (758949 / 1000000 : ℝ) := by
  have h := nStar_tight
  constructor <;> nlinarith [h.1, h.2]


lemma tan_dx_div4 :
    (-63332 / 1000000 : ℝ) ≤ 2 * Real.sin (nStar / 4) - 3 * (nStar / 4) ∧
      2 * Real.sin (nStar / 4) - 3 * (nStar / 4) ≤ (-63328 / 1000000 : ℝ) := by
  have hs := two_sin_nStar_div4
  have hn := three_nStar_div4
  constructor <;> nlinarith [hs.1, hs.2, hn.1, hn.2]

lemma tan_dx_div2 :
    (-127169 / 1000000 : ℝ) ≤ 2 * Real.sin (nStar / 2) - 3 * (nStar / 2) ∧
      2 * Real.sin (nStar / 2) - 3 * (nStar / 2) ≤ (-127163 / 1000000 : ℝ) := by
  have hs := two_sin_nStar_div2
  have hn := three_nStar_div2
  constructor <;> nlinarith [hs.1, hs.2, hn.1, hn.2]

lemma tan_dx_one :
    (-258365 / 1000000 : ℝ) ≤ 2 * Real.sin nStar - 3 * nStar ∧
      2 * Real.sin nStar - 3 * nStar ≤ (-258358 / 1000000 : ℝ) := by
  have hs := two_sin_nStar
  have hn := three_nStar
  constructor <;> nlinarith [hs.1, hs.2, hn.1, hn.2]

lemma two_c_mul_cos_div4 :
    (999995 / 1000000 : ℝ) ≤ (2 - Real.cos (nStar / 4)) * Real.cos (nStar / 4) ∧
      (2 - Real.cos (nStar / 4)) * Real.cos (nStar / 4) ≤ (999998 / 1000000 : ℝ) := by
  have ha := two_sub_cos_nStar_div4
  have hb := cos_nStar_div4_milli
  have h := mul_nonneg_bounds (by norm_num) (by norm_num) ha.1 ha.2 hb.1 hb.2
  constructor <;> nlinarith [h.1, h.2]

lemma two_c_mul_sin_div4 :
    (63329 / 1000000 : ℝ) ≤ (2 - Real.cos (nStar / 4)) * Real.sin (nStar / 4) ∧
      (2 - Real.cos (nStar / 4)) * Real.sin (nStar / 4) ≤ (63331 / 1000000 : ℝ) := by
  have ha := two_sub_cos_nStar_div4
  have hb := sin_nStar_div4_tight
  have h := mul_nonneg_bounds (by norm_num) (by norm_num) ha.1 ha.2 hb.1 hb.2
  constructor <;> nlinarith [h.1, h.2]

lemma tan_dx_mul_sin_div4 :
    (-4003 / 1000000 : ℝ) ≤
      (2 * Real.sin (nStar / 4) - 3 * (nStar / 4)) * Real.sin (nStar / 4) ∧
      (2 * Real.sin (nStar / 4) - 3 * (nStar / 4)) * Real.sin (nStar / 4)
        ≤ (-4002 / 1000000 : ℝ) := by
  have ha := tan_dx_div4
  have hb := sin_nStar_div4_tight
  have h := mul_nonpos_nonneg_bounds (by norm_num) (by norm_num) ha.1 ha.2 hb.1 hb.2
  constructor <;> nlinarith [h.1, h.2]

lemma tan_dx_mul_cos_div4 :
    (-63206 / 1000000 : ℝ) ≤
      (2 * Real.sin (nStar / 4) - 3 * (nStar / 4)) * Real.cos (nStar / 4) ∧
      (2 * Real.sin (nStar / 4) - 3 * (nStar / 4)) * Real.cos (nStar / 4)
        ≤ (-63201 / 1000000 : ℝ) := by
  have ha := tan_dx_div4
  have hb := cos_nStar_div4_milli
  have h := mul_nonpos_nonneg_bounds (by norm_num) (by norm_num) ha.1 ha.2 hb.1 hb.2
  constructor <;> nlinarith [h.1, h.2]

lemma three_nStar_mul_div4 :
    3 * nStar * (1 / 4) = 3 * (nStar / 4) := by ring

lemma stmCol0_x_div4 :
    (1003997 / 1000000 : ℝ) ≤ (stmCol 0 (1 / 4)).ofLp 0 ∧
      (stmCol 0 (1 / 4)).ofLp 0 ≤ (1004001 / 1000000 : ℝ) := by
  have hx := (stmCol0_ofLp (1 / 4)).1
  rw [hx, nStar_mul_div4, three_nStar_mul_div4]
  have ha := two_c_mul_cos_div4
  have hb := tan_dx_mul_sin_div4
  constructor <;> nlinarith [ha.1, ha.2, hb.1, hb.2]

lemma stmCol0_y_div4 :
    (123 / 1000000 : ℝ) ≤ (stmCol 0 (1 / 4)).ofLp 1 ∧
      (stmCol 0 (1 / 4)).ofLp 1 ≤ (130 / 1000000 : ℝ) := by
  have hy := (stmCol0_ofLp (1 / 4)).2.1
  rw [hy, nStar_mul_div4, three_nStar_mul_div4]
  have ha := two_c_mul_sin_div4
  have hb := tan_dx_mul_cos_div4
  constructor <;> nlinarith [ha.1, ha.2, hb.1, hb.2]


lemma three_nStar_mul_div2 : 3 * nStar * (1 / 2) = 3 * (nStar / 2) := by ring

lemma two_c_mul_cos_div2 :
    (999935 / 1000000 : ℝ) ≤ (2 - Real.cos (nStar / 2)) * Real.cos (nStar / 2) ∧
      (2 - Real.cos (nStar / 2)) * Real.cos (nStar / 2) ≤ (999938 / 1000000 : ℝ) := by
  have ha := two_sub_cos_nStar_div2
  have hb := cos_nStar_div2_milli
  have h := mul_nonneg_bounds (by norm_num) (by norm_num) ha.1 ha.2 hb.1 hb.2
  constructor <;> nlinarith [h.1, h.2]

lemma two_c_mul_sin_div2 :
    (127160 / 1000000 : ℝ) ≤ (2 - Real.cos (nStar / 2)) * Real.sin (nStar / 2) ∧
      (2 - Real.cos (nStar / 2)) * Real.sin (nStar / 2) ≤ (127163 / 1000000 : ℝ) := by
  have ha := two_sub_cos_nStar_div2
  have hb := sin_nStar_div2_tight
  have h := mul_nonneg_bounds (by norm_num) (by norm_num) ha.1 ha.2 hb.1 hb.2
  constructor <;> nlinarith [h.1, h.2]

lemma tan_dx_mul_sin_div2 :
    (-16044 / 1000000 : ℝ) ≤
      (2 * Real.sin (nStar / 2) - 3 * (nStar / 2)) * Real.sin (nStar / 2) ∧
      (2 * Real.sin (nStar / 2) - 3 * (nStar / 2)) * Real.sin (nStar / 2)
        ≤ (-16041 / 1000000 : ℝ) := by
  have ha := tan_dx_div2
  have hb := sin_nStar_div2_tight
  have h := mul_nonpos_nonneg_bounds (by norm_num) (by norm_num) ha.1 ha.2 hb.1 hb.2
  constructor <;> nlinarith [h.1, h.2]

lemma tan_dx_mul_cos_div2 :
    (-126154 / 1000000 : ℝ) ≤
      (2 * Real.sin (nStar / 2) - 3 * (nStar / 2)) * Real.cos (nStar / 2) ∧
      (2 * Real.sin (nStar / 2) - 3 * (nStar / 2)) * Real.cos (nStar / 2)
        ≤ (-126146 / 1000000 : ℝ) := by
  have ha := tan_dx_div2
  have hb := cos_nStar_div2_milli
  have h := mul_nonpos_nonneg_bounds (by norm_num) (by norm_num) ha.1 ha.2 hb.1 hb.2
  constructor <;> nlinarith [h.1, h.2]

lemma stmCol0_x_div2 :
    (1015976 / 1000000 : ℝ) ≤ (stmCol 0 (1 / 2)).ofLp 0 ∧
      (stmCol 0 (1 / 2)).ofLp 0 ≤ (1015982 / 1000000 : ℝ) := by
  have hx := (stmCol0_ofLp (1 / 2)).1
  rw [hx, nStar_mul_div2, three_nStar_mul_div2]
  have ha := two_c_mul_cos_div2
  have hb := tan_dx_mul_sin_div2
  constructor <;> nlinarith [ha.1, ha.2, hb.1, hb.2]

lemma stmCol0_y_div2 :
    (1006 / 1000000 : ℝ) ≤ (stmCol 0 (1 / 2)).ofLp 1 ∧
      (stmCol 0 (1 / 2)).ofLp 1 ≤ (1017 / 1000000 : ℝ) := by
  have hy := (stmCol0_ofLp (1 / 2)).2.1
  rw [hy, nStar_mul_div2, three_nStar_mul_div2]
  have ha := two_c_mul_sin_div2
  have hb := tan_dx_mul_cos_div2
  constructor <;> nlinarith [ha.1, ha.2, hb.1, hb.2]

lemma two_c_mul_cos_one :
    (998985 / 1000000 : ℝ) ≤ (2 - Real.cos nStar) * Real.cos nStar ∧
      (2 - Real.cos nStar) * Real.cos nStar ≤ (998988 / 1000000 : ℝ) := by
  have ha := two_sub_cos_nStar
  have hb := cos_nStar_milli
  have h := mul_nonneg_bounds (by norm_num) (by norm_num) ha.1 ha.2 hb.1 hb.2
  constructor <;> nlinarith [h.1, h.2]

lemma two_c_mul_sin_one :
    (258258 / 1000000 : ℝ) ≤ (2 - Real.cos nStar) * Real.sin nStar ∧
      (2 - Real.cos nStar) * Real.sin nStar ≤ (258261 / 1000000 : ℝ) := by
  have ha := two_sub_cos_nStar
  have hb := sin_nStar_tight
  have h := mul_nonneg_bounds (by norm_num) (by norm_num) ha.1 ha.2 hb.1 hb.2
  constructor <;> nlinarith [h.1, h.2]

lemma tan_dx_mul_sin_one :
    (-64668 / 1000000 : ℝ) ≤ (2 * Real.sin nStar - 3 * nStar) * Real.sin nStar ∧
      (2 * Real.sin nStar - 3 * nStar) * Real.sin nStar ≤ (-64664 / 1000000 : ℝ) := by
  have ha := tan_dx_one
  have hb := sin_nStar_tight
  have h := mul_nonpos_nonneg_bounds (by norm_num) (by norm_num) ha.1 ha.2 hb.1 hb.2
  constructor <;> nlinarith [h.1, h.2]

lemma tan_dx_mul_cos_one :
    (-250142 / 1000000 : ℝ) ≤ (2 * Real.sin nStar - 3 * nStar) * Real.cos nStar ∧
      (2 * Real.sin nStar - 3 * nStar) * Real.cos nStar ≤ (-250134 / 1000000 : ℝ) := by
  have ha := tan_dx_one
  have hb := cos_nStar_milli
  have h := mul_nonpos_nonneg_bounds (by norm_num) (by norm_num) ha.1 ha.2 hb.1 hb.2
  constructor <;> nlinarith [h.1, h.2]

lemma stmCol0_x_one :
    (1063649 / 1000000 : ℝ) ≤ (stmCol 0 1).ofLp 0 ∧
      (stmCol 0 1).ofLp 0 ≤ (1063656 / 1000000 : ℝ) := by
  have hx := (stmCol0_ofLp 1).1
  rw [hx, mul_one]
  have ha := two_c_mul_cos_one
  have hb := tan_dx_mul_sin_one
  constructor <;> nlinarith [ha.1, ha.2, hb.1, hb.2]

lemma stmCol0_y_one :
    (8116 / 1000000 : ℝ) ≤ (stmCol 0 1).ofLp 1 ∧
      (stmCol 0 1).ofLp 1 ≤ (8127 / 1000000 : ℝ) := by
  have hy := (stmCol0_ofLp 1).2.1
  rw [hy, mul_one]
  have ha := two_c_mul_sin_one
  have hb := tan_dx_mul_cos_one
  constructor <;> nlinarith [ha.1, ha.2, hb.1, hb.2]

lemma sin_mul_omc_div4 :
    (126 / 1000000 : ℝ) ≤ Real.sin (nStar / 4) * (1 - Real.cos (nStar / 4)) ∧
      Real.sin (nStar / 4) * (1 - Real.cos (nStar / 4)) ≤ (127 / 1000000 : ℝ) := by
  have ha := sin_nStar_div4_tight
  have hb := one_sub_cos_nStar_div4
  have h := mul_nonneg_bounds (by norm_num) (by norm_num) ha.1 ha.2 hb.1 hb.2
  constructor <;> nlinarith [h.1, h.2]

lemma cos_sq_nStar_div4 :
    (996004 / 1000000 : ℝ) ≤ Real.cos (nStar / 4) ^ 2 ∧
      Real.cos (nStar / 4) ^ 2 ≤ (996006 / 1000000 : ℝ) := by
  have hb := cos_nStar_div4_milli
  have h := mul_nonneg_bounds (by norm_num) (by norm_num) hb.1 hb.2 hb.1 hb.2
  constructor <;> nlinarith [h.1, h.2]

lemma stmCol1_x_div4 :
    (126 / 1000000 : ℝ) ≤ (stmCol 1 (1 / 4)).ofLp 0 ∧
      (stmCol 1 (1 / 4)).ofLp 0 ≤ (127 / 1000000 : ℝ) := by
  have hx := (stmCol1_ofLp (1 / 4)).1
  rw [hx, nStar_mul_div4]
  exact sin_mul_omc_div4

lemma stmCol1_y_div4 :
    (998003 / 1000000 : ℝ) ≤ (stmCol 1 (1 / 4)).ofLp 1 ∧
      (stmCol 1 (1 / 4)).ofLp 1 ≤ (998006 / 1000000 : ℝ) := by
  have hy := (stmCol1_ofLp (1 / 4)).2.1
  rw [hy, nStar_mul_div4]
  have ha := one_sub_cos_nStar_div4
  have hb := cos_sq_nStar_div4
  constructor <;> nlinarith [ha.1, ha.2, hb.1, hb.2]


lemma sin_mul_omc_div2 :
    (1007 / 1000000 : ℝ) ≤ Real.sin (nStar / 2) * (1 - Real.cos (nStar / 2)) ∧
      Real.sin (nStar / 2) * (1 - Real.cos (nStar / 2)) ≤ (1008 / 1000000 : ℝ) := by
  have ha := sin_nStar_div2_tight
  have hb := one_sub_cos_nStar_div2
  have h := mul_nonneg_bounds (by norm_num) (by norm_num) ha.1 ha.2 hb.1 hb.2
  constructor <;> nlinarith [h.1, h.2]

lemma cos_sq_nStar_div2 :
    (984083 / 1000000 : ℝ) ≤ Real.cos (nStar / 2) ^ 2 ∧
      Real.cos (nStar / 2) ^ 2 ≤ (984086 / 1000000 : ℝ) := by
  have hb := cos_nStar_div2_milli
  have h := mul_nonneg_bounds (by norm_num) (by norm_num) hb.1 hb.2 hb.1 hb.2
  constructor <;> nlinarith [h.1, h.2]

lemma stmCol1_x_div2 :
    (1007 / 1000000 : ℝ) ≤ (stmCol 1 (1 / 2)).ofLp 0 ∧
      (stmCol 1 (1 / 2)).ofLp 0 ≤ (1008 / 1000000 : ℝ) := by
  have hx := (stmCol1_ofLp (1 / 2)).1
  rw [hx, nStar_mul_div2]
  exact sin_mul_omc_div2

lemma stmCol1_y_div2 :
    (992072 / 1000000 : ℝ) ≤ (stmCol 1 (1 / 2)).ofLp 1 ∧
      (stmCol 1 (1 / 2)).ofLp 1 ≤ (992076 / 1000000 : ℝ) := by
  have hy := (stmCol1_ofLp (1 / 2)).2.1
  rw [hy, nStar_mul_div2]
  have ha := one_sub_cos_nStar_div2
  have hb := cos_sq_nStar_div2
  constructor <;> nlinarith [ha.1, ha.2, hb.1, hb.2]

lemma sin_mul_omc_one :
    (7966 / 1000000 : ℝ) ≤ Real.sin nStar * (1 - Real.cos nStar) ∧
      Real.sin nStar * (1 - Real.cos nStar) ≤ (7967 / 1000000 : ℝ) := by
  have ha := sin_nStar_tight
  have hb := one_sub_cos_nStar
  have h := mul_nonneg_bounds (by norm_num) (by norm_num) ha.1 ha.2 hb.1 hb.2
  constructor <;> nlinarith [h.1, h.2]

lemma cos_sq_nStar :
    (937353 / 1000000 : ℝ) ≤ Real.cos nStar ^ 2 ∧
      Real.cos nStar ^ 2 ≤ (937356 / 1000000 : ℝ) := by
  have hb := cos_nStar_milli
  have h := mul_nonneg_bounds (by norm_num) (by norm_num) hb.1 hb.2 hb.1 hb.2
  constructor <;> nlinarith [h.1, h.2]

lemma stmCol1_x_one :
    (7966 / 1000000 : ℝ) ≤ (stmCol 1 1).ofLp 0 ∧
      (stmCol 1 1).ofLp 0 ≤ (7967 / 1000000 : ℝ) := by
  have hx := (stmCol1_ofLp 1).1
  rw [hx, mul_one]
  exact sin_mul_omc_one

lemma stmCol1_y_one :
    (969182 / 1000000 : ℝ) ≤ (stmCol 1 1).ofLp 1 ∧
      (stmCol 1 1).ofLp 1 ≤ (969186 / 1000000 : ℝ) := by
  have hy := (stmCol1_ofLp 1).2.1
  rw [hy, mul_one]
  have ha := one_sub_cos_nStar
  have hb := cos_sq_nStar
  constructor <;> nlinarith [ha.1, ha.2, hb.1, hb.2]


lemma five_halves_cos_div4 :
    (2495000 / 1000000 : ℝ) ≤ (5 / 2) * Real.cos (nStar / 4) ∧
      (5 / 2) * Real.cos (nStar / 4) ≤ (2495003 / 1000000 : ℝ) := by
  have h := cos_nStar_div4_milli
  constructor <;> nlinarith [h.1, h.2]

lemma five_halves_sin_div4 :
    (158007 / 1000000 : ℝ) ≤ (5 / 2) * Real.sin (nStar / 4) ∧
      (5 / 2) * Real.sin (nStar / 4) ≤ (158010 / 1000000 : ℝ) := by
  have h := sin_nStar_div4_tight
  constructor <;> nlinarith [h.1, h.2]

lemma uStar_x_div4 :
    (998285 / 1000000 : ℝ) ≤ (uStar (1 / 4)).ofLp 0 ∧
      (uStar (1 / 4)).ofLp 0 ≤ (998293 / 1000000 : ℝ) := by
  rw [uStar_ofLp0, nStar_mul_div4]
  have hn := five_halves_cos_div4
  have hc := cos_quarter_milli
  have hnum : (1526087 / 1000000 : ℝ) ≤
      (5 / 2) * Real.cos (nStar / 4) - Real.cos (1 / 4) ∧
      (5 / 2) * Real.cos (nStar / 4) - Real.cos (1 / 4) ≤ (1526091 / 1000000 : ℝ) := by
    constructor <;> nlinarith [hn.1, hn.2, hc.1, hc.2]
  have hr := inv_rhoStar_div4_tight
  have h := mul_nonneg_bounds (by norm_num) (by norm_num) hnum.1 hnum.2 hr.1 hr.2
  constructor <;> nlinarith [h.1, h.2]

lemma uStar_y_div4 :
    (-58480 / 1000000 : ℝ) ≤ (uStar (1 / 4)).ofLp 1 ∧
      (uStar (1 / 4)).ofLp 1 ≤ (-58476 / 1000000 : ℝ) := by
  rw [uStar_ofLp1, nStar_mul_div4]
  have hn := five_halves_sin_div4
  have hs := sin_quarter_milli
  have hnum : (-89397 / 1000000 : ℝ) ≤
      (5 / 2) * Real.sin (nStar / 4) - Real.sin (1 / 4) ∧
      (5 / 2) * Real.sin (nStar / 4) - Real.sin (1 / 4) ≤ (-89393 / 1000000 : ℝ) := by
    constructor <;> nlinarith [hn.1, hn.2, hs.1, hs.2]
  have hr := inv_rhoStar_div4_tight
  have h := mul_nonpos_nonneg_bounds (by norm_num) (by norm_num) hnum.1 hnum.2 hr.1 hr.2
  constructor <;> nlinarith [h.1, h.2]

/-! STM columns 2–3 and remaining `uStar` intervals. -/

lemma stmCol2_x_eq (t : ℝ) :
    (stmCol 2 t).ofLp 0 =
      (2 - Real.cos (nStar * t)) * Real.sin (nStar * t) * nStar⁻¹ := by
  have hx := (stmCol2_ofLp t).1
  rw [hx]
  have hn : nStar ≠ 0 := nStar_ne
  field_simp [hn]
  ring

lemma stmCol2_y_eq (t : ℝ) :
    (stmCol 2 t).ofLp 1 =
      (Real.sin (nStar * t) ^ 2
        - 2 * (1 - Real.cos (nStar * t)) * Real.cos (nStar * t)) * nStar⁻¹ := by
  have hy := (stmCol2_ofLp t).2.1
  rw [hy]
  have hn : nStar ≠ 0 := nStar_ne
  field_simp [hn]

lemma stmCol3_x_eq (t : ℝ) :
    (stmCol 3 t).ofLp 0 =
      (2 * (1 - Real.cos (nStar * t)) * Real.cos (nStar * t)
        - (4 * Real.sin (nStar * t) - 3 * nStar * t) * Real.sin (nStar * t))
        * nStar⁻¹ := by
  have hx := (stmCol3_ofLp t).1
  rw [hx]
  have hn : nStar ≠ 0 := nStar_ne
  field_simp [hn]

lemma stmCol3_y_eq (t : ℝ) :
    (stmCol 3 t).ofLp 1 =
      (2 * (1 - Real.cos (nStar * t)) * Real.sin (nStar * t)
        + (4 * Real.sin (nStar * t) - 3 * nStar * t) * Real.cos (nStar * t))
        * nStar⁻¹ := by
  have hy := (stmCol3_ofLp t).2.1
  rw [hy]
  have hn : nStar ≠ 0 := nStar_ne
  field_simp [hn]


lemma tighten_mul {aLo aHi bLo bHi lo hi a b : ℝ}
    (h : aLo * bLo ≤ a * b ∧ a * b ≤ aHi * bHi)
    (hlo : lo ≤ aLo * bLo) (hhi : aHi * bHi ≤ hi) :
    lo ≤ a * b ∧ a * b ≤ hi :=
  ⟨hlo.trans h.1, h.2.trans hhi⟩

lemma tighten_mul_pn {aLo aHi bLo bHi lo hi a b : ℝ}
    (h : aLo * bHi ≤ a * b ∧ a * b ≤ aHi * bLo)
    (hlo : lo ≤ aLo * bHi) (hhi : aHi * bLo ≤ hi) :
    lo ≤ a * b ∧ a * b ≤ hi :=
  ⟨hlo.trans h.1, h.2.trans hhi⟩

lemma stmCol2_x_div4 :
    (250329 / 1000000 : ℝ) ≤ (stmCol 2 (1 / 4)).ofLp 0 ∧
      (stmCol 2 (1 / 4)).ofLp 0 ≤ (250339 / 1000000 : ℝ) := by
  rw [stmCol2_x_eq, nStar_mul_div4]
  have ha := two_c_mul_sin_div4
  have hb := inv_nStar_tight
  have h := mul_nonneg_bounds (by norm_num) (by norm_num) ha.1 ha.2 hb.1 hb.2
  refine tighten_mul h ?_ ?_ <;> norm_num

lemma sin_sq_nStar_div4 :
    (3994 / 1000000 : ℝ) ≤ Real.sin (nStar / 4) ^ 2 ∧
      Real.sin (nStar / 4) ^ 2 ≤ (3995 / 1000000 : ℝ) := by
  have hb := sin_nStar_div4_tight
  have h := mul_nonneg_bounds (by norm_num) (by norm_num) hb.1 hb.2 hb.1 hb.2
  constructor <;> nlinarith [h.1, h.2]

lemma two_omc_mul_cos_div4 :
    (3990 / 1000000 : ℝ) ≤ 2 * (1 - Real.cos (nStar / 4)) * Real.cos (nStar / 4) ∧
      2 * (1 - Real.cos (nStar / 4)) * Real.cos (nStar / 4) ≤ (3993 / 1000000 : ℝ) := by
  have ha := one_sub_cos_nStar_div4
  have hb := cos_nStar_div4_milli
  have h := mul_nonneg_bounds (by norm_num) (by norm_num) ha.1 ha.2 hb.1 hb.2
  constructor <;> nlinarith [h.1, h.2]

lemma stmCol2_y_num_div4 :
    (1 / 1000000 : ℝ) ≤
      Real.sin (nStar / 4) ^ 2 - 2 * (1 - Real.cos (nStar / 4)) * Real.cos (nStar / 4) ∧
      Real.sin (nStar / 4) ^ 2 - 2 * (1 - Real.cos (nStar / 4)) * Real.cos (nStar / 4)
        ≤ (5 / 1000000 : ℝ) := by
  have ha := sin_sq_nStar_div4
  have hb := two_omc_mul_cos_div4
  constructor <;> nlinarith [ha.1, ha.2, hb.1, hb.2]

lemma stmCol2_y_div4 :
    (3 / 1000000 : ℝ) ≤ (stmCol 2 (1 / 4)).ofLp 1 ∧
      (stmCol 2 (1 / 4)).ofLp 1 ≤ (20 / 1000000 : ℝ) := by
  rw [stmCol2_y_eq, nStar_mul_div4]
  have ha := stmCol2_y_num_div4
  have hb := inv_nStar_tight
  have h := mul_nonneg_bounds (by norm_num) (by norm_num) ha.1 ha.2 hb.1 hb.2
  refine tighten_mul h ?_ ?_ <;> norm_num

lemma stmCol2_x_div2 :
    (502642 / 1000000 : ℝ) ≤ (stmCol 2 (1 / 2)).ofLp 0 ∧
      (stmCol 2 (1 / 2)).ofLp 0 ≤ (502657 / 1000000 : ℝ) := by
  rw [stmCol2_x_eq, nStar_mul_div2]
  have ha := two_c_mul_sin_div2
  have hb := inv_nStar_tight
  have h := mul_nonneg_bounds (by norm_num) (by norm_num) ha.1 ha.2 hb.1 hb.2
  refine tighten_mul h ?_ ?_ <;> norm_num

lemma sin_sq_nStar_div2 :
    (15914 / 1000000 : ℝ) ≤ Real.sin (nStar / 2) ^ 2 ∧
      Real.sin (nStar / 2) ^ 2 ≤ (15916 / 1000000 : ℝ) := by
  have hb := sin_nStar_div2_tight
  have h := mul_nonneg_bounds (by norm_num) (by norm_num) hb.1 hb.2 hb.1 hb.2
  constructor <;> nlinarith [h.1, h.2]

lemma two_omc_mul_cos_div2 :
    (15850 / 1000000 : ℝ) ≤ 2 * (1 - Real.cos (nStar / 2)) * Real.cos (nStar / 2) ∧
      2 * (1 - Real.cos (nStar / 2)) * Real.cos (nStar / 2) ≤ (15853 / 1000000 : ℝ) := by
  have ha := one_sub_cos_nStar_div2
  have hb := cos_nStar_div2_milli
  have h := mul_nonneg_bounds (by norm_num) (by norm_num) ha.1 ha.2 hb.1 hb.2
  constructor <;> nlinarith [h.1, h.2]

lemma stmCol2_y_num_div2 :
    (61 / 1000000 : ℝ) ≤
      Real.sin (nStar / 2) ^ 2 - 2 * (1 - Real.cos (nStar / 2)) * Real.cos (nStar / 2) ∧
      Real.sin (nStar / 2) ^ 2 - 2 * (1 - Real.cos (nStar / 2)) * Real.cos (nStar / 2)
        ≤ (66 / 1000000 : ℝ) := by
  have ha := sin_sq_nStar_div2
  have hb := two_omc_mul_cos_div2
  constructor <;> nlinarith [ha.1, ha.2, hb.1, hb.2]

lemma stmCol2_y_div2 :
    (241 / 1000000 : ℝ) ≤ (stmCol 2 (1 / 2)).ofLp 1 ∧
      (stmCol 2 (1 / 2)).ofLp 1 ≤ (261 / 1000000 : ℝ) := by
  rw [stmCol2_y_eq, nStar_mul_div2]
  have ha := stmCol2_y_num_div2
  have hb := inv_nStar_tight
  have h := mul_nonneg_bounds (by norm_num) (by norm_num) ha.1 ha.2 hb.1 hb.2
  refine tighten_mul h ?_ ?_ <;> norm_num

lemma stmCol2_x_one :
    (1020851 / 1000000 : ℝ) ≤ (stmCol 2 1).ofLp 0 ∧
      (stmCol 2 1).ofLp 0 ≤ (1020868 / 1000000 : ℝ) := by
  rw [stmCol2_x_eq, mul_one]
  have ha := two_c_mul_sin_one
  have hb := inv_nStar_tight
  have h := mul_nonneg_bounds (by norm_num) (by norm_num) ha.1 ha.2 hb.1 hb.2
  refine tighten_mul h ?_ ?_ <;> norm_num

lemma sin_sq_nStar :
    (62646 / 1000000 : ℝ) ≤ Real.sin nStar ^ 2 ∧
      Real.sin nStar ^ 2 ≤ (62648 / 1000000 : ℝ) := by
  have hb := sin_nStar_tight
  have h := mul_nonneg_bounds (by norm_num) (by norm_num) hb.1 hb.2 hb.1 hb.2
  constructor <;> nlinarith [h.1, h.2]

lemma two_omc_mul_cos_one :
    (61631 / 1000000 : ℝ) ≤ 2 * (1 - Real.cos nStar) * Real.cos nStar ∧
      2 * (1 - Real.cos nStar) * Real.cos nStar ≤ (61634 / 1000000 : ℝ) := by
  have ha := one_sub_cos_nStar
  have hb := cos_nStar_milli
  have h := mul_nonneg_bounds (by norm_num) (by norm_num) ha.1 ha.2 hb.1 hb.2
  constructor <;> nlinarith [h.1, h.2]

lemma stmCol2_y_num_one :
    (1012 / 1000000 : ℝ) ≤
      Real.sin nStar ^ 2 - 2 * (1 - Real.cos nStar) * Real.cos nStar ∧
      Real.sin nStar ^ 2 - 2 * (1 - Real.cos nStar) * Real.cos nStar
        ≤ (1017 / 1000000 : ℝ) := by
  have ha := sin_sq_nStar
  have hb := two_omc_mul_cos_one
  constructor <;> nlinarith [ha.1, ha.2, hb.1, hb.2]

lemma stmCol2_y_one :
    (4000 / 1000000 : ℝ) ≤ (stmCol 2 1).ofLp 1 ∧
      (stmCol 2 1).ofLp 1 ≤ (4021 / 1000000 : ℝ) := by
  rw [stmCol2_y_eq, mul_one]
  have ha := stmCol2_y_num_one
  have hb := inv_nStar_tight
  have h := mul_nonneg_bounds (by norm_num) (by norm_num) ha.1 ha.2 hb.1 hb.2
  refine tighten_mul h ?_ ?_ <;> norm_num

lemma four_sin_nStar_div4 :
    (252812 / 1000000 : ℝ) ≤ 4 * Real.sin (nStar / 4) ∧
      4 * Real.sin (nStar / 4) ≤ (252816 / 1000000 : ℝ) := by
  have h := sin_nStar_div4_tight
  constructor <;> nlinarith [h.1, h.2]

lemma tan_dv_div4 :
    (63074 / 1000000 : ℝ) ≤ 4 * Real.sin (nStar / 4) - 3 * (nStar / 4) ∧
      4 * Real.sin (nStar / 4) - 3 * (nStar / 4) ≤ (63080 / 1000000 : ℝ) := by
  have hs := four_sin_nStar_div4
  have hn := three_nStar_div4
  constructor <;> nlinarith [hs.1, hs.2, hn.1, hn.2]

lemma tan_dv_mul_sin_div4 :
    (3986 / 1000000 : ℝ) ≤
      (4 * Real.sin (nStar / 4) - 3 * (nStar / 4)) * Real.sin (nStar / 4) ∧
      (4 * Real.sin (nStar / 4) - 3 * (nStar / 4)) * Real.sin (nStar / 4)
        ≤ (3987 / 1000000 : ℝ) := by
  have ha := tan_dv_div4
  have hb := sin_nStar_div4_tight
  have h := mul_nonneg_bounds (by norm_num) (by norm_num) ha.1 ha.2 hb.1 hb.2
  constructor <;> nlinarith [h.1, h.2]

lemma stmCol3_x_num_div4 :
    (3 / 1000000 : ℝ) ≤
      2 * (1 - Real.cos (nStar / 4)) * Real.cos (nStar / 4)
        - (4 * Real.sin (nStar / 4) - 3 * (nStar / 4)) * Real.sin (nStar / 4) ∧
      2 * (1 - Real.cos (nStar / 4)) * Real.cos (nStar / 4)
        - (4 * Real.sin (nStar / 4) - 3 * (nStar / 4)) * Real.sin (nStar / 4)
        ≤ (7 / 1000000 : ℝ) := by
  have ha := two_omc_mul_cos_div4
  have hb := tan_dv_mul_sin_div4
  constructor <;> nlinarith [ha.1, ha.2, hb.1, hb.2]

lemma stmCol3_x_div4 :
    (11 / 1000000 : ℝ) ≤ (stmCol 3 (1 / 4)).ofLp 0 ∧
      (stmCol 3 (1 / 4)).ofLp 0 ≤ (28 / 1000000 : ℝ) := by
  rw [stmCol3_x_eq, nStar_mul_div4, three_nStar_mul_div4]
  have ha := stmCol3_x_num_div4
  have hb := inv_nStar_tight
  have h := mul_nonneg_bounds (by norm_num) (by norm_num) ha.1 ha.2 hb.1 hb.2
  refine tighten_mul h ?_ ?_ <;> norm_num

lemma two_omc_mul_sin_div4 :
    (252 / 1000000 : ℝ) ≤ 2 * (1 - Real.cos (nStar / 4)) * Real.sin (nStar / 4) ∧
      2 * (1 - Real.cos (nStar / 4)) * Real.sin (nStar / 4) ≤ (253 / 1000000 : ℝ) := by
  have ha := one_sub_cos_nStar_div4
  have hb := sin_nStar_div4_tight
  have h := mul_nonneg_bounds (by norm_num) (by norm_num) ha.1 ha.2 hb.1 hb.2
  constructor <;> nlinarith [h.1, h.2]

lemma tan_dv_mul_cos_div4 :
    (62947 / 1000000 : ℝ) ≤
      (4 * Real.sin (nStar / 4) - 3 * (nStar / 4)) * Real.cos (nStar / 4) ∧
      (4 * Real.sin (nStar / 4) - 3 * (nStar / 4)) * Real.cos (nStar / 4)
        ≤ (62954 / 1000000 : ℝ) := by
  have ha := tan_dv_div4
  have hb := cos_nStar_div4_milli
  have h := mul_nonneg_bounds (by norm_num) (by norm_num) ha.1 ha.2 hb.1 hb.2
  constructor <;> nlinarith [h.1, h.2]

lemma stmCol3_y_num_div4 :
    (63199 / 1000000 : ℝ) ≤
      2 * (1 - Real.cos (nStar / 4)) * Real.sin (nStar / 4)
        + (4 * Real.sin (nStar / 4) - 3 * (nStar / 4)) * Real.cos (nStar / 4) ∧
      2 * (1 - Real.cos (nStar / 4)) * Real.sin (nStar / 4)
        + (4 * Real.sin (nStar / 4) - 3 * (nStar / 4)) * Real.cos (nStar / 4)
        ≤ (63207 / 1000000 : ℝ) := by
  have ha := two_omc_mul_sin_div4
  have hb := tan_dv_mul_cos_div4
  constructor <;> nlinarith [ha.1, ha.2, hb.1, hb.2]

lemma stmCol3_y_div4 :
    (249815 / 1000000 : ℝ) ≤ (stmCol 3 (1 / 4)).ofLp 1 ∧
      (stmCol 3 (1 / 4)).ofLp 1 ≤ (249848 / 1000000 : ℝ) := by
  rw [stmCol3_y_eq, nStar_mul_div4, three_nStar_mul_div4]
  have ha := stmCol3_y_num_div4
  have hb := inv_nStar_tight
  have h := mul_nonneg_bounds (by norm_num) (by norm_num) ha.1 ha.2 hb.1 hb.2
  refine tighten_mul h ?_ ?_ <;> norm_num

lemma four_sin_nStar_div2 :
    (504612 / 1000000 : ℝ) ≤ 4 * Real.sin (nStar / 2) ∧
      4 * Real.sin (nStar / 2) ≤ (504620 / 1000000 : ℝ) := by
  have h := sin_nStar_div2_tight
  constructor <;> nlinarith [h.1, h.2]

lemma tan_dv_div2 :
    (125137 / 1000000 : ℝ) ≤ 4 * Real.sin (nStar / 2) - 3 * (nStar / 2) ∧
      4 * Real.sin (nStar / 2) - 3 * (nStar / 2) ≤ (125147 / 1000000 : ℝ) := by
  have hs := four_sin_nStar_div2
  have hn := three_nStar_div2
  constructor <;> nlinarith [hs.1, hs.2, hn.1, hn.2]

lemma tan_dv_mul_sin_div2 :
    (15786 / 1000000 : ℝ) ≤
      (4 * Real.sin (nStar / 2) - 3 * (nStar / 2)) * Real.sin (nStar / 2) ∧
      (4 * Real.sin (nStar / 2) - 3 * (nStar / 2)) * Real.sin (nStar / 2)
        ≤ (15788 / 1000000 : ℝ) := by
  have ha := tan_dv_div2
  have hb := sin_nStar_div2_tight
  have h := mul_nonneg_bounds (by norm_num) (by norm_num) ha.1 ha.2 hb.1 hb.2
  constructor <;> nlinarith [h.1, h.2]

lemma stmCol3_x_num_div2 :
    (62 / 1000000 : ℝ) ≤
      2 * (1 - Real.cos (nStar / 2)) * Real.cos (nStar / 2)
        - (4 * Real.sin (nStar / 2) - 3 * (nStar / 2)) * Real.sin (nStar / 2) ∧
      2 * (1 - Real.cos (nStar / 2)) * Real.cos (nStar / 2)
        - (4 * Real.sin (nStar / 2) - 3 * (nStar / 2)) * Real.sin (nStar / 2)
        ≤ (67 / 1000000 : ℝ) := by
  have ha := two_omc_mul_cos_div2
  have hb := tan_dv_mul_sin_div2
  constructor <;> nlinarith [ha.1, ha.2, hb.1, hb.2]

lemma stmCol3_x_div2 :
    (245 / 1000000 : ℝ) ≤ (stmCol 3 (1 / 2)).ofLp 0 ∧
      (stmCol 3 (1 / 2)).ofLp 0 ≤ (265 / 1000000 : ℝ) := by
  rw [stmCol3_x_eq, nStar_mul_div2, three_nStar_mul_div2]
  have ha := stmCol3_x_num_div2
  have hb := inv_nStar_tight
  have h := mul_nonneg_bounds (by norm_num) (by norm_num) ha.1 ha.2 hb.1 hb.2
  refine tighten_mul h ?_ ?_ <;> norm_num

lemma two_omc_mul_sin_div2 :
    (2015 / 1000000 : ℝ) ≤ 2 * (1 - Real.cos (nStar / 2)) * Real.sin (nStar / 2) ∧
      2 * (1 - Real.cos (nStar / 2)) * Real.sin (nStar / 2) ≤ (2016 / 1000000 : ℝ) := by
  have ha := one_sub_cos_nStar_div2
  have hb := sin_nStar_div2_tight
  have h := mul_nonneg_bounds (by norm_num) (by norm_num) ha.1 ha.2 hb.1 hb.2
  constructor <;> nlinarith [h.1, h.2]

lemma tan_dv_mul_cos_div2 :
    (124137 / 1000000 : ℝ) ≤
      (4 * Real.sin (nStar / 2) - 3 * (nStar / 2)) * Real.cos (nStar / 2) ∧
      (4 * Real.sin (nStar / 2) - 3 * (nStar / 2)) * Real.cos (nStar / 2)
        ≤ (124148 / 1000000 : ℝ) := by
  have ha := tan_dv_div2
  have hb := cos_nStar_div2_milli
  have h := mul_nonneg_bounds (by norm_num) (by norm_num) ha.1 ha.2 hb.1 hb.2
  constructor <;> nlinarith [h.1, h.2]

lemma stmCol3_y_num_div2 :
    (126152 / 1000000 : ℝ) ≤
      2 * (1 - Real.cos (nStar / 2)) * Real.sin (nStar / 2)
        + (4 * Real.sin (nStar / 2) - 3 * (nStar / 2)) * Real.cos (nStar / 2) ∧
      2 * (1 - Real.cos (nStar / 2)) * Real.sin (nStar / 2)
        + (4 * Real.sin (nStar / 2) - 3 * (nStar / 2)) * Real.cos (nStar / 2)
        ≤ (126164 / 1000000 : ℝ) := by
  have ha := two_omc_mul_sin_div2
  have hb := tan_dv_mul_cos_div2
  constructor <;> nlinarith [ha.1, ha.2, hb.1, hb.2]

lemma stmCol3_y_div2 :
    (498657 / 1000000 : ℝ) ≤ (stmCol 3 (1 / 2)).ofLp 1 ∧
      (stmCol 3 (1 / 2)).ofLp 1 ≤ (498708 / 1000000 : ℝ) := by
  rw [stmCol3_y_eq, nStar_mul_div2, three_nStar_mul_div2]
  have ha := stmCol3_y_num_div2
  have hb := inv_nStar_tight
  have h := mul_nonneg_bounds (by norm_num) (by norm_num) ha.1 ha.2 hb.1 hb.2
  refine tighten_mul h ?_ ?_ <;> norm_num

lemma four_sin_nStar :
    (1001168 / 1000000 : ℝ) ≤ 4 * Real.sin nStar ∧
      4 * Real.sin nStar ≤ (1001176 / 1000000 : ℝ) := by
  have h := sin_nStar_tight
  constructor <;> nlinarith [h.1, h.2]

lemma tan_dv_one :
    (242219 / 1000000 : ℝ) ≤ 4 * Real.sin nStar - 3 * nStar ∧
      4 * Real.sin nStar - 3 * nStar ≤ (242230 / 1000000 : ℝ) := by
  have hs := four_sin_nStar
  have hn := three_nStar
  constructor <;> nlinarith [hs.1, hs.2, hn.1, hn.2]

lemma tan_dv_mul_sin_one :
    (60625 / 1000000 : ℝ) ≤ (4 * Real.sin nStar - 3 * nStar) * Real.sin nStar ∧
      (4 * Real.sin nStar - 3 * nStar) * Real.sin nStar ≤ (60629 / 1000000 : ℝ) := by
  have ha := tan_dv_one
  have hb := sin_nStar_tight
  have h := mul_nonneg_bounds (by norm_num) (by norm_num) ha.1 ha.2 hb.1 hb.2
  constructor <;> nlinarith [h.1, h.2]

lemma stmCol3_x_num_one :
    (1002 / 1000000 : ℝ) ≤
      2 * (1 - Real.cos nStar) * Real.cos nStar
        - (4 * Real.sin nStar - 3 * nStar) * Real.sin nStar ∧
      2 * (1 - Real.cos nStar) * Real.cos nStar
        - (4 * Real.sin nStar - 3 * nStar) * Real.sin nStar
        ≤ (1009 / 1000000 : ℝ) := by
  have ha := two_omc_mul_cos_one
  have hb := tan_dv_mul_sin_one
  constructor <;> nlinarith [ha.1, ha.2, hb.1, hb.2]

lemma stmCol3_x_one :
    (3960 / 1000000 : ℝ) ≤ (stmCol 3 1).ofLp 0 ∧
      (stmCol 3 1).ofLp 0 ≤ (3989 / 1000000 : ℝ) := by
  rw [stmCol3_x_eq, mul_one, mul_one]
  have ha := stmCol3_x_num_one
  have hb := inv_nStar_tight
  have h := mul_nonneg_bounds (by norm_num) (by norm_num) ha.1 ha.2 hb.1 hb.2
  refine tighten_mul h ?_ ?_ <;> norm_num

lemma two_omc_mul_sin_one :
    (15933 / 1000000 : ℝ) ≤ 2 * (1 - Real.cos nStar) * Real.sin nStar ∧
      2 * (1 - Real.cos nStar) * Real.sin nStar ≤ (15934 / 1000000 : ℝ) := by
  have ha := one_sub_cos_nStar
  have hb := sin_nStar_tight
  have h := mul_nonneg_bounds (by norm_num) (by norm_num) ha.1 ha.2 hb.1 hb.2
  constructor <;> nlinarith [h.1, h.2]

lemma tan_dv_mul_cos_one :
    (234509 / 1000000 : ℝ) ≤ (4 * Real.sin nStar - 3 * nStar) * Real.cos nStar ∧
      (4 * Real.sin nStar - 3 * nStar) * Real.cos nStar ≤ (234521 / 1000000 : ℝ) := by
  have ha := tan_dv_one
  have hb := cos_nStar_milli
  have h := mul_nonneg_bounds (by norm_num) (by norm_num) ha.1 ha.2 hb.1 hb.2
  constructor <;> nlinarith [h.1, h.2]

lemma stmCol3_y_num_one :
    (250442 / 1000000 : ℝ) ≤
      2 * (1 - Real.cos nStar) * Real.sin nStar
        + (4 * Real.sin nStar - 3 * nStar) * Real.cos nStar ∧
      2 * (1 - Real.cos nStar) * Real.sin nStar
        + (4 * Real.sin nStar - 3 * nStar) * Real.cos nStar
        ≤ (250455 / 1000000 : ℝ) := by
  have ha := two_omc_mul_sin_one
  have hb := tan_dv_mul_cos_one
  constructor <;> nlinarith [ha.1, ha.2, hb.1, hb.2]

lemma stmCol3_y_one :
    (989955 / 1000000 : ℝ) ≤ (stmCol 3 1).ofLp 1 ∧
      (stmCol 3 1).ofLp 1 ≤ (990012 / 1000000 : ℝ) := by
  rw [stmCol3_y_eq, mul_one, mul_one]
  have ha := stmCol3_y_num_one
  have hb := inv_nStar_tight
  have h := mul_nonneg_bounds (by norm_num) (by norm_num) ha.1 ha.2 hb.1 hb.2
  refine tighten_mul h ?_ ?_ <;> norm_num

lemma five_halves_cos_div2 :
    (2480025 / 1000000 : ℝ) ≤ (5 / 2) * Real.cos (nStar / 2) ∧
      (5 / 2) * Real.cos (nStar / 2) ≤ (2480028 / 1000000 : ℝ) := by
  have h := cos_nStar_div2_milli
  constructor <;> nlinarith [h.1, h.2]

lemma five_halves_sin_div2 :
    (315382 / 1000000 : ℝ) ≤ (5 / 2) * Real.sin (nStar / 2) ∧
      (5 / 2) * Real.sin (nStar / 2) ≤ (315388 / 1000000 : ℝ) := by
  have h := sin_nStar_div2_tight
  constructor <;> nlinarith [h.1, h.2]

lemma uStar_x_div2 :
    (994797 / 1000000 : ℝ) ≤ (uStar (1 / 2)).ofLp 0 ∧
      (uStar (1 / 2)).ofLp 0 ≤ (994805 / 1000000 : ℝ) := by
  rw [uStar_ofLp0, nStar_mul_div2]
  have hn := five_halves_cos_div2
  have hc := cos_half_milli
  have hnum : (1602442 / 1000000 : ℝ) ≤
      (5 / 2) * Real.cos (nStar / 2) - Real.cos (1 / 2) ∧
      (5 / 2) * Real.cos (nStar / 2) - Real.cos (1 / 2) ≤ (1602446 / 1000000 : ℝ) := by
    constructor <;> nlinarith [hn.1, hn.2, hc.1, hc.2]
  have hr := inv_rhoStar_div2_tight
  have h := mul_nonneg_bounds (by norm_num) (by norm_num) hnum.1 hnum.2 hr.1 hr.2
  refine tighten_mul h ?_ ?_ <;> norm_num

lemma uStar_y_div2 :
    (-101840 / 1000000 : ℝ) ≤ (uStar (1 / 2)).ofLp 1 ∧
      (uStar (1 / 2)).ofLp 1 ≤ (-101834 / 1000000 : ℝ) := by
  rw [uStar_ofLp1, nStar_mul_div2]
  have hn := five_halves_sin_div2
  have hs := sin_half_milli
  have hnum : (-164044 / 1000000 : ℝ) ≤
      (5 / 2) * Real.sin (nStar / 2) - Real.sin (1 / 2) ∧
      (5 / 2) * Real.sin (nStar / 2) - Real.sin (1 / 2) ≤ (-164037 / 1000000 : ℝ) := by
    constructor <;> nlinarith [hn.1, hn.2, hs.1, hs.2]
  have hr := inv_rhoStar_div2_tight
  have h := mul_nonpos_nonneg_bounds (by norm_num) (by norm_num) hnum.1 hnum.2 hr.1 hr.2
  refine tighten_mul_pn h ?_ ?_ <;> norm_num

lemma five_halves_cos_one :
    (2420425 / 1000000 : ℝ) ≤ (5 / 2) * Real.cos nStar ∧
      (5 / 2) * Real.cos nStar ≤ (2420428 / 1000000 : ℝ) := by
  have h := cos_nStar_milli
  constructor <;> nlinarith [h.1, h.2]

lemma five_halves_sin_one :
    (625730 / 1000000 : ℝ) ≤ (5 / 2) * Real.sin nStar ∧
      (5 / 2) * Real.sin nStar ≤ (625735 / 1000000 : ℝ) := by
  have h := sin_nStar_tight
  constructor <;> nlinarith [h.1, h.2]

lemma uStar_x_one :
    (993456 / 1000000 : ℝ) ≤ (uStar 1).ofLp 0 ∧
      (uStar 1).ofLp 0 ≤ (993532 / 1000000 : ℝ) := by
  rw [uStar_ofLp0, mul_one]
  have hn := five_halves_cos_one
  have hc := cos_one_milli
  have hnum : (1880119 / 1000000 : ℝ) ≤
      (5 / 2) * Real.cos nStar - Real.cos 1 ∧
      (5 / 2) * Real.cos nStar - Real.cos 1 ≤ (1880179 / 1000000 : ℝ) := by
    constructor <;> nlinarith [hn.1, hn.2, hc.1, hc.2]
  have hr := inv_rhoStar_one_tight
  have h := mul_nonneg_bounds (by norm_num) (by norm_num) hnum.1 hnum.2 hr.1 hr.2
  refine tighten_mul h ?_ ?_ <;> norm_num

lemma uStar_y_one :
    (-114004 / 1000000 : ℝ) ≤ (uStar 1).ofLp 1 ∧
      (uStar 1).ofLp 1 ≤ (-113991 / 1000000 : ℝ) := by
  rw [uStar_ofLp1, mul_one]
  have hn := five_halves_sin_one
  have hs := sin_one_milli
  have hnum : (-215742 / 1000000 : ℝ) ≤
      (5 / 2) * Real.sin nStar - Real.sin 1 ∧
      (5 / 2) * Real.sin nStar - Real.sin 1 ≤ (-215730 / 1000000 : ℝ) := by
    constructor <;> nlinarith [hn.1, hn.2, hs.1, hs.2]
  have hr := inv_rhoStar_one_tight
  have h := mul_nonpos_nonneg_bounds (by norm_num) (by norm_num) hnum.1 hnum.2 hr.1 hr.2
  refine tighten_mul_pn h ?_ ?_ <;> norm_num

/-! `dlosCol` intervals via `inner_uStar_stm_xy` and `ρ⁻¹` boxes. -/

lemma two_hSD1 : (2 : ℝ) * hSD1 = 1 / 2 := by unfold hSD1; norm_num
lemma two_hSD2 : (2 : ℝ) * hSD2 = 1 := by unfold hSD2; norm_num

lemma dlosCol_ofLp01 (j : Fin 4) (t : ℝ) :
    (dlosCol j t).ofLp 0 =
      (rhoStar t)⁻¹ *
        ((stmCol j t).ofLp 0 - ⟪uStar t, stmCol j t⟫ * (uStar t).ofLp 0) ∧
    (dlosCol j t).ofLp 1 =
      (rhoStar t)⁻¹ *
        ((stmCol j t).ofLp 1 - ⟪uStar t, stmCol j t⟫ * (uStar t).ofLp 1) :=
  dlosSTM_ofLp01 t (stmCol j t)

lemma inner_uStar_stmCol0_div4 :
    (1002267 / 1000000 : ℝ) ≤ ⟪uStar (1 / 4), stmCol 0 (1 / 4)⟫ ∧
      ⟪uStar (1 / 4), stmCol 0 (1 / 4)⟫ ≤ (1002280 / 1000000 : ℝ) := by
  rw [inner_uStar_stm_xy]
  have hux := uStar_x_div4
  have huy := uStar_y_div4
  have hdx := stmCol0_x_div4
  have hdy := stmCol0_y_div4
  have h0 := mul_nonneg_bounds (by norm_num) (by norm_num) hux.1 hux.2 hdx.1 hdx.2
  have h1 := mul_nonpos_nonneg_bounds (by norm_num) (by norm_num) huy.1 huy.2 hdy.1 hdy.2
  constructor <;> nlinarith [h0.1, h0.2, h1.1, h1.2]

lemma inner_uStar_stmCol0_div2 :
    (1010586 / 1000000 : ℝ) ≤ ⟪uStar (1 / 2), stmCol 0 (1 / 2)⟫ ∧
      ⟪uStar (1 / 2), stmCol 0 (1 / 2)⟫ ≤ (1010602 / 1000000 : ℝ) := by
  rw [inner_uStar_stm_xy]
  have hux := uStar_x_div2
  have huy := uStar_y_div2
  have hdx := stmCol0_x_div2
  have hdy := stmCol0_y_div2
  have h0 := mul_nonneg_bounds (by norm_num) (by norm_num) hux.1 hux.2 hdx.1 hdx.2
  have h1 := mul_nonpos_nonneg_bounds (by norm_num) (by norm_num) huy.1 huy.2 hdy.1 hdy.2
  constructor <;> nlinarith [h0.1, h0.2, h1.1, h1.2]

lemma inner_uStar_stmCol0_one :
    (1055761 / 1000000 : ℝ) ≤ ⟪uStar 1, stmCol 0 1⟫ ∧
      ⟪uStar 1, stmCol 0 1⟫ ≤ (1055852 / 1000000 : ℝ) := by
  rw [inner_uStar_stm_xy]
  have hux := uStar_x_one
  have huy := uStar_y_one
  have hdx := stmCol0_x_one
  have hdy := stmCol0_y_one
  have h0 := mul_nonneg_bounds (by norm_num) (by norm_num) hux.1 hux.2 hdx.1 hdx.2
  have h1 := mul_nonpos_nonneg_bounds (by norm_num) (by norm_num) huy.1 huy.2 hdy.1 hdy.2
  constructor <;> nlinarith [h0.1, h0.2, h1.1, h1.2]

lemma inner_uStar_stmCol1_div4 :
    (-58238 / 1000000 : ℝ) ≤ ⟪uStar (1 / 4), stmCol 1 (1 / 4)⟫ ∧
      ⟪uStar (1 / 4), stmCol 1 (1 / 4)⟫ ≤ (-58232 / 1000000 : ℝ) := by
  rw [inner_uStar_stm_xy]
  have hux := uStar_x_div4
  have huy := uStar_y_div4
  have hdx := stmCol1_x_div4
  have hdy := stmCol1_y_div4
  have h0 := mul_nonneg_bounds (by norm_num) (by norm_num) hux.1 hux.2 hdx.1 hdx.2
  have h1 := mul_nonpos_nonneg_bounds (by norm_num) (by norm_num) huy.1 huy.2 hdy.1 hdy.2
  constructor <;> nlinarith [h0.1, h0.2, h1.1, h1.2]

lemma inner_uStar_stmCol1_div2 :
    (-100032 / 1000000 : ℝ) ≤ ⟪uStar (1 / 2), stmCol 1 (1 / 2)⟫ ∧
      ⟪uStar (1 / 2), stmCol 1 (1 / 2)⟫ ≤ (-100023 / 1000000 : ℝ) := by
  rw [inner_uStar_stm_xy]
  have hux := uStar_x_div2
  have huy := uStar_y_div2
  have hdx := stmCol1_x_div2
  have hdy := stmCol1_y_div2
  have h0 := mul_nonneg_bounds (by norm_num) (by norm_num) hux.1 hux.2 hdx.1 hdx.2
  have h1 := mul_nonpos_nonneg_bounds (by norm_num) (by norm_num) huy.1 huy.2 hdy.1 hdy.2
  constructor <;> nlinarith [h0.1, h0.2, h1.1, h1.2]

lemma inner_uStar_stmCol1_one :
    (-102578 / 1000000 : ℝ) ≤ ⟪uStar 1, stmCol 1 1⟫ ∧
      ⟪uStar 1, stmCol 1 1⟫ ≤ (-102562 / 1000000 : ℝ) := by
  rw [inner_uStar_stm_xy]
  have hux := uStar_x_one
  have huy := uStar_y_one
  have hdx := stmCol1_x_one
  have hdy := stmCol1_y_one
  have h0 := mul_nonneg_bounds (by norm_num) (by norm_num) hux.1 hux.2 hdx.1 hdx.2
  have h1 := mul_nonpos_nonneg_bounds (by norm_num) (by norm_num) huy.1 huy.2 hdy.1 hdy.2
  constructor <;> nlinarith [h0.1, h0.2, h1.1, h1.2]

lemma inner_uStar_stmCol2_div4 :
    (249898 / 1000000 : ℝ) ≤ ⟪uStar (1 / 4), stmCol 2 (1 / 4)⟫ ∧
      ⟪uStar (1 / 4), stmCol 2 (1 / 4)⟫ ≤ (249912 / 1000000 : ℝ) := by
  rw [inner_uStar_stm_xy]
  have hux := uStar_x_div4
  have huy := uStar_y_div4
  have hdx := stmCol2_x_div4
  have hdy := stmCol2_y_div4
  have h0 := mul_nonneg_bounds (by norm_num) (by norm_num) hux.1 hux.2 hdx.1 hdx.2
  have h1 := mul_nonpos_nonneg_bounds (by norm_num) (by norm_num) huy.1 huy.2 hdy.1 hdy.2
  constructor <;> nlinarith [h0.1, h0.2, h1.1, h1.2]

lemma inner_uStar_stmCol2_div2 :
    (500000 / 1000000 : ℝ) ≤ ⟪uStar (1 / 2), stmCol 2 (1 / 2)⟫ ∧
      ⟪uStar (1 / 2), stmCol 2 (1 / 2)⟫ ≤ (500022 / 1000000 : ℝ) := by
  rw [inner_uStar_stm_xy]
  have hux := uStar_x_div2
  have huy := uStar_y_div2
  have hdx := stmCol2_x_div2
  have hdy := stmCol2_y_div2
  have h0 := mul_nonneg_bounds (by norm_num) (by norm_num) hux.1 hux.2 hdx.1 hdx.2
  have h1 := mul_nonpos_nonneg_bounds (by norm_num) (by norm_num) huy.1 huy.2 hdy.1 hdy.2
  constructor <;> nlinarith [h0.1, h0.2, h1.1, h1.2]

lemma inner_uStar_stmCol2_one :
    (1013712 / 1000000 : ℝ) ≤ ⟪uStar 1, stmCol 2 1⟫ ∧
      ⟪uStar 1, stmCol 2 1⟫ ≤ (1013810 / 1000000 : ℝ) := by
  rw [inner_uStar_stm_xy]
  have hux := uStar_x_one
  have huy := uStar_y_one
  have hdx := stmCol2_x_one
  have hdy := stmCol2_y_one
  have h0 := mul_nonneg_bounds (by norm_num) (by norm_num) hux.1 hux.2 hdx.1 hdx.2
  have h1 := mul_nonpos_nonneg_bounds (by norm_num) (by norm_num) huy.1 huy.2 hdy.1 hdy.2
  constructor <;> nlinarith [h0.1, h0.2, h1.1, h1.2]

lemma inner_uStar_stmCol3_div4 :
    (-14601 / 1000000 : ℝ) ≤ ⟪uStar (1 / 4), stmCol 3 (1 / 4)⟫ ∧
      ⟪uStar (1 / 4), stmCol 3 (1 / 4)⟫ ≤ (-14580 / 1000000 : ℝ) := by
  rw [inner_uStar_stm_xy]
  have hux := uStar_x_div4
  have huy := uStar_y_div4
  have hdx := stmCol3_x_div4
  have hdy := stmCol3_y_div4
  have h0 := mul_nonneg_bounds (by norm_num) (by norm_num) hux.1 hux.2 hdx.1 hdx.2
  have h1 := mul_nonpos_nonneg_bounds (by norm_num) (by norm_num) huy.1 huy.2 hdy.1 hdy.2
  constructor <;> nlinarith [h0.1, h0.2, h1.1, h1.2]

lemma inner_uStar_stmCol3_div2 :
    (-50545 / 1000000 : ℝ) ≤ ⟪uStar (1 / 2), stmCol 3 (1 / 2)⟫ ∧
      ⟪uStar (1 / 2), stmCol 3 (1 / 2)⟫ ≤ (-50516 / 1000000 : ℝ) := by
  rw [inner_uStar_stm_xy]
  have hux := uStar_x_div2
  have huy := uStar_y_div2
  have hdx := stmCol3_x_div2
  have hdy := stmCol3_y_div2
  have h0 := mul_nonneg_bounds (by norm_num) (by norm_num) hux.1 hux.2 hdx.1 hdx.2
  have h1 := mul_nonpos_nonneg_bounds (by norm_num) (by norm_num) huy.1 huy.2 hdy.1 hdy.2
  constructor <;> nlinarith [h0.1, h0.2, h1.1, h1.2]

lemma inner_uStar_stmCol3_one :
    (-108932 / 1000000 : ℝ) ≤ ⟪uStar 1, stmCol 3 1⟫ ∧
      ⟪uStar 1, stmCol 3 1⟫ ≤ (-108882 / 1000000 : ℝ) := by
  rw [inner_uStar_stm_xy]
  have hux := uStar_x_one
  have huy := uStar_y_one
  have hdx := stmCol3_x_one
  have hdy := stmCol3_y_one
  have h0 := mul_nonneg_bounds (by norm_num) (by norm_num) hux.1 hux.2 hdx.1 hdx.2
  have h1 := mul_nonpos_nonneg_bounds (by norm_num) (by norm_num) huy.1 huy.2 hdy.1 hdy.2
  constructor <;> nlinarith [h0.1, h0.2, h1.1, h1.2]

lemma inn_ux_stmCol0_div4 :
    (1000548 / 1000000 : ℝ) ≤ ⟪uStar (1 / 4), stmCol 0 (1 / 4)⟫ * (uStar (1 / 4)).ofLp 0 ∧
      ⟪uStar (1 / 4), stmCol 0 (1 / 4)⟫ * (uStar (1 / 4)).ofLp 0 ≤ (1000570 / 1000000 : ℝ) := by
  have hinn := inner_uStar_stmCol0_div4
  have hux := uStar_x_div4
  have h := mul_nonneg_bounds (by norm_num) (by norm_num) hinn.1 hinn.2 hux.1 hux.2
  constructor <;> nlinarith [h.1, h.2]

lemma inn_uy_stmCol0_div4 :
    (-58614 / 1000000 : ℝ) ≤ ⟪uStar (1 / 4), stmCol 0 (1 / 4)⟫ * (uStar (1 / 4)).ofLp 1 ∧
      ⟪uStar (1 / 4), stmCol 0 (1 / 4)⟫ * (uStar (1 / 4)).ofLp 1 ≤ (-58608 / 1000000 : ℝ) := by
  have hinn := inner_uStar_stmCol0_div4
  have huy := uStar_y_div4
  have h := mul_nonneg_nonpos_bounds (by norm_num) (by norm_num) hinn.1 hinn.2 huy.1 huy.2
  constructor <;> nlinarith [h.1, h.2]

lemma proj_x_stmCol0_div4 :
    (3427 / 1000000 : ℝ) ≤
      (stmCol 0 (1 / 4)).ofLp 0
        - ⟪uStar (1 / 4), stmCol 0 (1 / 4)⟫ * (uStar (1 / 4)).ofLp 0 ∧
      (stmCol 0 (1 / 4)).ofLp 0
        - ⟪uStar (1 / 4), stmCol 0 (1 / 4)⟫ * (uStar (1 / 4)).ofLp 0
        ≤ (3453 / 1000000 : ℝ) := by
  have hdx := stmCol0_x_div4
  have hm := inn_ux_stmCol0_div4
  constructor <;> nlinarith [hdx.1, hdx.2, hm.1, hm.2]

lemma proj_y_stmCol0_div4 :
    (58731 / 1000000 : ℝ) ≤
      (stmCol 0 (1 / 4)).ofLp 1
        - ⟪uStar (1 / 4), stmCol 0 (1 / 4)⟫ * (uStar (1 / 4)).ofLp 1 ∧
      (stmCol 0 (1 / 4)).ofLp 1
        - ⟪uStar (1 / 4), stmCol 0 (1 / 4)⟫ * (uStar (1 / 4)).ofLp 1
        ≤ (58744 / 1000000 : ℝ) := by
  have hdy := stmCol0_y_div4
  have hm := inn_uy_stmCol0_div4
  constructor <;> nlinarith [hdy.1, hdy.2, hm.1, hm.2]

lemma dlosCol0_x_div4 :
    (2241 / 1000000 : ℝ) ≤ (dlosCol 0 (1 / 4)).ofLp 0 ∧
      (dlosCol 0 (1 / 4)).ofLp 0 ≤ (2259 / 1000000 : ℝ) := by
  rw [(dlosCol_ofLp01 0 (1 / 4)).1]
  have hp := proj_x_stmCol0_div4
  have hr := inv_rhoStar_div4_tight
  have h := mul_nonneg_bounds (by norm_num) (by norm_num) hr.1 hr.2 hp.1 hp.2
  constructor <;> nlinarith [h.1, h.2]

lemma dlosCol0_y_div4 :
    (38418 / 1000000 : ℝ) ≤ (dlosCol 0 (1 / 4)).ofLp 1 ∧
      (dlosCol 0 (1 / 4)).ofLp 1 ≤ (38428 / 1000000 : ℝ) := by
  rw [(dlosCol_ofLp01 0 (1 / 4)).2]
  have hp := proj_y_stmCol0_div4
  have hr := inv_rhoStar_div4_tight
  have h := mul_nonneg_bounds (by norm_num) (by norm_num) hr.1 hr.2 hp.1 hp.2
  constructor <;> nlinarith [h.1, h.2]

lemma inn_ux_stmCol0_div2 :
    (1005327 / 1000000 : ℝ) ≤ ⟪uStar (1 / 2), stmCol 0 (1 / 2)⟫ * (uStar (1 / 2)).ofLp 0 ∧
      ⟪uStar (1 / 2), stmCol 0 (1 / 2)⟫ * (uStar (1 / 2)).ofLp 0 ≤ (1005352 / 1000000 : ℝ) := by
  have hinn := inner_uStar_stmCol0_div2
  have hux := uStar_x_div2
  have h := mul_nonneg_bounds (by norm_num) (by norm_num) hinn.1 hinn.2 hux.1 hux.2
  constructor <;> nlinarith [h.1, h.2]

lemma inn_uy_stmCol0_div2 :
    (-102920 / 1000000 : ℝ) ≤ ⟪uStar (1 / 2), stmCol 0 (1 / 2)⟫ * (uStar (1 / 2)).ofLp 1 ∧
      ⟪uStar (1 / 2), stmCol 0 (1 / 2)⟫ * (uStar (1 / 2)).ofLp 1 ≤ (-102912 / 1000000 : ℝ) := by
  have hinn := inner_uStar_stmCol0_div2
  have huy := uStar_y_div2
  have h := mul_nonneg_nonpos_bounds (by norm_num) (by norm_num) hinn.1 hinn.2 huy.1 huy.2
  constructor <;> nlinarith [h.1, h.2]

lemma proj_x_stmCol0_div2 :
    (10624 / 1000000 : ℝ) ≤
      (stmCol 0 (1 / 2)).ofLp 0
        - ⟪uStar (1 / 2), stmCol 0 (1 / 2)⟫ * (uStar (1 / 2)).ofLp 0 ∧
      (stmCol 0 (1 / 2)).ofLp 0
        - ⟪uStar (1 / 2), stmCol 0 (1 / 2)⟫ * (uStar (1 / 2)).ofLp 0
        ≤ (10655 / 1000000 : ℝ) := by
  have hdx := stmCol0_x_div2
  have hm := inn_ux_stmCol0_div2
  constructor <;> nlinarith [hdx.1, hdx.2, hm.1, hm.2]

lemma proj_y_stmCol0_div2 :
    (103918 / 1000000 : ℝ) ≤
      (stmCol 0 (1 / 2)).ofLp 1
        - ⟪uStar (1 / 2), stmCol 0 (1 / 2)⟫ * (uStar (1 / 2)).ofLp 1 ∧
      (stmCol 0 (1 / 2)).ofLp 1
        - ⟪uStar (1 / 2), stmCol 0 (1 / 2)⟫ * (uStar (1 / 2)).ofLp 1
        ≤ (103937 / 1000000 : ℝ) := by
  have hdy := stmCol0_y_div2
  have hm := inn_uy_stmCol0_div2
  constructor <;> nlinarith [hdy.1, hdy.2, hm.1, hm.2]

lemma dlosCol0_x_div2 :
    (6595 / 1000000 : ℝ) ≤ (dlosCol 0 (1 / 2)).ofLp 0 ∧
      (dlosCol 0 (1 / 2)).ofLp 0 ≤ (6615 / 1000000 : ℝ) := by
  rw [(dlosCol_ofLp01 0 (1 / 2)).1]
  have hp := proj_x_stmCol0_div2
  have hr := inv_rhoStar_div2_tight
  have h := mul_nonneg_bounds (by norm_num) (by norm_num) hr.1 hr.2 hp.1 hp.2
  constructor <;> nlinarith [h.1, h.2]

lemma dlosCol0_y_div2 :
    (64512 / 1000000 : ℝ) ≤ (dlosCol 0 (1 / 2)).ofLp 1 ∧
      (dlosCol 0 (1 / 2)).ofLp 1 ≤ (64525 / 1000000 : ℝ) := by
  rw [(dlosCol_ofLp01 0 (1 / 2)).2]
  have hp := proj_y_stmCol0_div2
  have hr := inv_rhoStar_div2_tight
  have h := mul_nonneg_bounds (by norm_num) (by norm_num) hr.1 hr.2 hp.1 hp.2
  constructor <;> nlinarith [h.1, h.2]

lemma inn_ux_stmCol0_one :
    (1048852 / 1000000 : ℝ) ≤ ⟪uStar 1, stmCol 0 1⟫ * (uStar 1).ofLp 0 ∧
      ⟪uStar 1, stmCol 0 1⟫ * (uStar 1).ofLp 0 ≤ (1049023 / 1000000 : ℝ) := by
  have hinn := inner_uStar_stmCol0_one
  have hux := uStar_x_one
  have h := mul_nonneg_bounds (by norm_num) (by norm_num) hinn.1 hinn.2 hux.1 hux.2
  constructor <;> nlinarith [h.1, h.2]

lemma inn_uy_stmCol0_one :
    (-120372 / 1000000 : ℝ) ≤ ⟪uStar 1, stmCol 0 1⟫ * (uStar 1).ofLp 1 ∧
      ⟪uStar 1, stmCol 0 1⟫ * (uStar 1).ofLp 1 ≤ (-120347 / 1000000 : ℝ) := by
  have hinn := inner_uStar_stmCol0_one
  have huy := uStar_y_one
  have h := mul_nonneg_nonpos_bounds (by norm_num) (by norm_num) hinn.1 hinn.2 huy.1 huy.2
  constructor <;> nlinarith [h.1, h.2]

lemma proj_x_stmCol0_one :
    (14626 / 1000000 : ℝ) ≤
      (stmCol 0 1).ofLp 0
        - ⟪uStar 1, stmCol 0 1⟫ * (uStar 1).ofLp 0 ∧
      (stmCol 0 1).ofLp 0
        - ⟪uStar 1, stmCol 0 1⟫ * (uStar 1).ofLp 0
        ≤ (14804 / 1000000 : ℝ) := by
  have hdx := stmCol0_x_one
  have hm := inn_ux_stmCol0_one
  constructor <;> nlinarith [hdx.1, hdx.2, hm.1, hm.2]

lemma proj_y_stmCol0_one :
    (128463 / 1000000 : ℝ) ≤
      (stmCol 0 1).ofLp 1
        - ⟪uStar 1, stmCol 0 1⟫ * (uStar 1).ofLp 1 ∧
      (stmCol 0 1).ofLp 1
        - ⟪uStar 1, stmCol 0 1⟫ * (uStar 1).ofLp 1
        ≤ (128499 / 1000000 : ℝ) := by
  have hdy := stmCol0_y_one
  have hm := inn_uy_stmCol0_one
  constructor <;> nlinarith [hdy.1, hdy.2, hm.1, hm.2]

lemma dlosCol0_x_one :
    (7728 / 1000000 : ℝ) ≤ (dlosCol 0 1).ofLp 0 ∧
      (dlosCol 0 1).ofLp 0 ≤ (7823 / 1000000 : ℝ) := by
  rw [(dlosCol_ofLp01 0 1).1]
  have hp := proj_x_stmCol0_one
  have hr := inv_rhoStar_one_tight
  have h := mul_nonneg_bounds (by norm_num) (by norm_num) hr.1 hr.2 hp.1 hp.2
  constructor <;> nlinarith [h.1, h.2]

lemma dlosCol0_y_one :
    (67879 / 1000000 : ℝ) ≤ (dlosCol 0 1).ofLp 1 ∧
      (dlosCol 0 1).ofLp 1 ≤ (67902 / 1000000 : ℝ) := by
  rw [(dlosCol_ofLp01 0 1).2]
  have hp := proj_y_stmCol0_one
  have hr := inv_rhoStar_one_tight
  have h := mul_nonneg_bounds (by norm_num) (by norm_num) hr.1 hr.2 hp.1 hp.2
  constructor <;> nlinarith [h.1, h.2]

lemma inn_ux_stmCol1_div4 :
    (-58139 / 1000000 : ℝ) ≤ ⟪uStar (1 / 4), stmCol 1 (1 / 4)⟫ * (uStar (1 / 4)).ofLp 0 ∧
      ⟪uStar (1 / 4), stmCol 1 (1 / 4)⟫ * (uStar (1 / 4)).ofLp 0 ≤ (-58132 / 1000000 : ℝ) := by
  have hinn := inner_uStar_stmCol1_div4
  have hux := uStar_x_div4
  have h := mul_nonpos_nonneg_bounds (by norm_num) (by norm_num) hinn.1 hinn.2 hux.1 hux.2
  constructor <;> nlinarith [h.1, h.2]

lemma inn_uy_stmCol1_div4 :
    (3405 / 1000000 : ℝ) ≤ ⟪uStar (1 / 4), stmCol 1 (1 / 4)⟫ * (uStar (1 / 4)).ofLp 1 ∧
      ⟪uStar (1 / 4), stmCol 1 (1 / 4)⟫ * (uStar (1 / 4)).ofLp 1 ≤ (3406 / 1000000 : ℝ) := by
  have hinn := inner_uStar_stmCol1_div4
  have huy := uStar_y_div4
  have h := mul_nonpos_nonpos_bounds (by norm_num) (by norm_num) hinn.1 hinn.2 huy.1 huy.2
  constructor <;> nlinarith [h.1, h.2]

lemma proj_x_stmCol1_div4 :
    (58258 / 1000000 : ℝ) ≤
      (stmCol 1 (1 / 4)).ofLp 0
        - ⟪uStar (1 / 4), stmCol 1 (1 / 4)⟫ * (uStar (1 / 4)).ofLp 0 ∧
      (stmCol 1 (1 / 4)).ofLp 0
        - ⟪uStar (1 / 4), stmCol 1 (1 / 4)⟫ * (uStar (1 / 4)).ofLp 0
        ≤ (58266 / 1000000 : ℝ) := by
  have hdx := stmCol1_x_div4
  have hm := inn_ux_stmCol1_div4
  constructor <;> nlinarith [hdx.1, hdx.2, hm.1, hm.2]

lemma proj_y_stmCol1_div4 :
    (994597 / 1000000 : ℝ) ≤
      (stmCol 1 (1 / 4)).ofLp 1
        - ⟪uStar (1 / 4), stmCol 1 (1 / 4)⟫ * (uStar (1 / 4)).ofLp 1 ∧
      (stmCol 1 (1 / 4)).ofLp 1
        - ⟪uStar (1 / 4), stmCol 1 (1 / 4)⟫ * (uStar (1 / 4)).ofLp 1
        ≤ (994601 / 1000000 : ℝ) := by
  have hdy := stmCol1_y_div4
  have hm := inn_uy_stmCol1_div4
  constructor <;> nlinarith [hdy.1, hdy.2, hm.1, hm.2]

lemma dlosCol1_x_div4 :
    (38109 / 1000000 : ℝ) ≤ (dlosCol 1 (1 / 4)).ofLp 0 ∧
      (dlosCol 1 (1 / 4)).ofLp 0 ≤ (38115 / 1000000 : ℝ) := by
  rw [(dlosCol_ofLp01 1 (1 / 4)).1]
  have hp := proj_x_stmCol1_div4
  have hr := inv_rhoStar_div4_tight
  have h := mul_nonneg_bounds (by norm_num) (by norm_num) hr.1 hr.2 hp.1 hp.2
  constructor <;> nlinarith [h.1, h.2]

lemma dlosCol1_y_div4 :
    (650612 / 1000000 : ℝ) ≤ (dlosCol 1 (1 / 4)).ofLp 1 ∧
      (dlosCol 1 (1 / 4)).ofLp 1 ≤ (650619 / 1000000 : ℝ) := by
  rw [(dlosCol_ofLp01 1 (1 / 4)).2]
  have hp := proj_y_stmCol1_div4
  have hr := inv_rhoStar_div4_tight
  have h := mul_nonneg_bounds (by norm_num) (by norm_num) hr.1 hr.2 hp.1 hp.2
  constructor <;> nlinarith [h.1, h.2]

lemma inn_ux_stmCol1_div2 :
    (-99513 / 1000000 : ℝ) ≤ ⟪uStar (1 / 2), stmCol 1 (1 / 2)⟫ * (uStar (1 / 2)).ofLp 0 ∧
      ⟪uStar (1 / 2), stmCol 1 (1 / 2)⟫ * (uStar (1 / 2)).ofLp 0 ≤ (-99502 / 1000000 : ℝ) := by
  have hinn := inner_uStar_stmCol1_div2
  have hux := uStar_x_div2
  have h := mul_nonpos_nonneg_bounds (by norm_num) (by norm_num) hinn.1 hinn.2 hux.1 hux.2
  constructor <;> nlinarith [h.1, h.2]

lemma inn_uy_stmCol1_div2 :
    (10185 / 1000000 : ℝ) ≤ ⟪uStar (1 / 2), stmCol 1 (1 / 2)⟫ * (uStar (1 / 2)).ofLp 1 ∧
      ⟪uStar (1 / 2), stmCol 1 (1 / 2)⟫ * (uStar (1 / 2)).ofLp 1 ≤ (10188 / 1000000 : ℝ) := by
  have hinn := inner_uStar_stmCol1_div2
  have huy := uStar_y_div2
  have h := mul_nonpos_nonpos_bounds (by norm_num) (by norm_num) hinn.1 hinn.2 huy.1 huy.2
  constructor <;> nlinarith [h.1, h.2]

lemma proj_x_stmCol1_div2 :
    (100509 / 1000000 : ℝ) ≤
      (stmCol 1 (1 / 2)).ofLp 0
        - ⟪uStar (1 / 2), stmCol 1 (1 / 2)⟫ * (uStar (1 / 2)).ofLp 0 ∧
      (stmCol 1 (1 / 2)).ofLp 0
        - ⟪uStar (1 / 2), stmCol 1 (1 / 2)⟫ * (uStar (1 / 2)).ofLp 0
        ≤ (100521 / 1000000 : ℝ) := by
  have hdx := stmCol1_x_div2
  have hm := inn_ux_stmCol1_div2
  constructor <;> nlinarith [hdx.1, hdx.2, hm.1, hm.2]

lemma proj_y_stmCol1_div2 :
    (981884 / 1000000 : ℝ) ≤
      (stmCol 1 (1 / 2)).ofLp 1
        - ⟪uStar (1 / 2), stmCol 1 (1 / 2)⟫ * (uStar (1 / 2)).ofLp 1 ∧
      (stmCol 1 (1 / 2)).ofLp 1
        - ⟪uStar (1 / 2), stmCol 1 (1 / 2)⟫ * (uStar (1 / 2)).ofLp 1
        ≤ (981891 / 1000000 : ℝ) := by
  have hdy := stmCol1_y_div2
  have hm := inn_uy_stmCol1_div2
  constructor <;> nlinarith [hdy.1, hdy.2, hm.1, hm.2]

lemma dlosCol1_x_div2 :
    (62396 / 1000000 : ℝ) ≤ (dlosCol 1 (1 / 2)).ofLp 0 ∧
      (dlosCol 1 (1 / 2)).ofLp 0 ≤ (62404 / 1000000 : ℝ) := by
  rw [(dlosCol_ofLp01 1 (1 / 2)).1]
  have hp := proj_x_stmCol1_div2
  have hr := inv_rhoStar_div2_tight
  have h := mul_nonneg_bounds (by norm_num) (by norm_num) hr.1 hr.2 hp.1 hp.2
  constructor <;> nlinarith [h.1, h.2]

lemma dlosCol1_y_div2 :
    (609554 / 1000000 : ℝ) ≤ (dlosCol 1 (1 / 2)).ofLp 1 ∧
      (dlosCol 1 (1 / 2)).ofLp 1 ≤ (609562 / 1000000 : ℝ) := by
  rw [(dlosCol_ofLp01 1 (1 / 2)).2]
  have hp := proj_y_stmCol1_div2
  have hr := inv_rhoStar_div2_tight
  have h := mul_nonneg_bounds (by norm_num) (by norm_num) hr.1 hr.2 hp.1 hp.2
  constructor <;> nlinarith [h.1, h.2]

lemma inn_ux_stmCol1_one :
    (-101915 / 1000000 : ℝ) ≤ ⟪uStar 1, stmCol 1 1⟫ * (uStar 1).ofLp 0 ∧
      ⟪uStar 1, stmCol 1 1⟫ * (uStar 1).ofLp 0 ≤ (-101890 / 1000000 : ℝ) := by
  have hinn := inner_uStar_stmCol1_one
  have hux := uStar_x_one
  have h := mul_nonpos_nonneg_bounds (by norm_num) (by norm_num) hinn.1 hinn.2 hux.1 hux.2
  constructor <;> nlinarith [h.1, h.2]

lemma inn_uy_stmCol1_one :
    (11691 / 1000000 : ℝ) ≤ ⟪uStar 1, stmCol 1 1⟫ * (uStar 1).ofLp 1 ∧
      ⟪uStar 1, stmCol 1 1⟫ * (uStar 1).ofLp 1 ≤ (11695 / 1000000 : ℝ) := by
  have hinn := inner_uStar_stmCol1_one
  have huy := uStar_y_one
  have h := mul_nonpos_nonpos_bounds (by norm_num) (by norm_num) hinn.1 hinn.2 huy.1 huy.2
  constructor <;> nlinarith [h.1, h.2]

lemma proj_x_stmCol1_one :
    (109856 / 1000000 : ℝ) ≤
      (stmCol 1 1).ofLp 0
        - ⟪uStar 1, stmCol 1 1⟫ * (uStar 1).ofLp 0 ∧
      (stmCol 1 1).ofLp 0
        - ⟪uStar 1, stmCol 1 1⟫ * (uStar 1).ofLp 0
        ≤ (109882 / 1000000 : ℝ) := by
  have hdx := stmCol1_x_one
  have hm := inn_ux_stmCol1_one
  constructor <;> nlinarith [hdx.1, hdx.2, hm.1, hm.2]

lemma proj_y_stmCol1_one :
    (957487 / 1000000 : ℝ) ≤
      (stmCol 1 1).ofLp 1
        - ⟪uStar 1, stmCol 1 1⟫ * (uStar 1).ofLp 1 ∧
      (stmCol 1 1).ofLp 1
        - ⟪uStar 1, stmCol 1 1⟫ * (uStar 1).ofLp 1
        ≤ (957495 / 1000000 : ℝ) := by
  have hdy := stmCol1_y_one
  have hm := inn_uy_stmCol1_one
  constructor <;> nlinarith [hdy.1, hdy.2, hm.1, hm.2]

lemma dlosCol1_x_one :
    (58048 / 1000000 : ℝ) ≤ (dlosCol 1 1).ofLp 0 ∧
      (dlosCol 1 1).ofLp 0 ≤ (58065 / 1000000 : ℝ) := by
  rw [(dlosCol_ofLp01 1 1).1]
  have hp := proj_x_stmCol1_one
  have hr := inv_rhoStar_one_tight
  have h := mul_nonneg_bounds (by norm_num) (by norm_num) hr.1 hr.2 hp.1 hp.2
  constructor <;> nlinarith [h.1, h.2]

lemma dlosCol1_y_one :
    (505937 / 1000000 : ℝ) ≤ (dlosCol 1 1).ofLp 1 ∧
      (dlosCol 1 1).ofLp 1 ≤ (505964 / 1000000 : ℝ) := by
  rw [(dlosCol_ofLp01 1 1).2]
  have hp := proj_y_stmCol1_one
  have hr := inv_rhoStar_one_tight
  have h := mul_nonneg_bounds (by norm_num) (by norm_num) hr.1 hr.2 hp.1 hp.2
  constructor <;> nlinarith [h.1, h.2]

lemma inn_ux_stmCol2_div4 :
    (249469 / 1000000 : ℝ) ≤ ⟪uStar (1 / 4), stmCol 2 (1 / 4)⟫ * (uStar (1 / 4)).ofLp 0 ∧
      ⟪uStar (1 / 4), stmCol 2 (1 / 4)⟫ * (uStar (1 / 4)).ofLp 0 ≤ (249486 / 1000000 : ℝ) := by
  have hinn := inner_uStar_stmCol2_div4
  have hux := uStar_x_div4
  have h := mul_nonneg_bounds (by norm_num) (by norm_num) hinn.1 hinn.2 hux.1 hux.2
  constructor <;> nlinarith [h.1, h.2]

lemma inn_uy_stmCol2_div4 :
    (-14615 / 1000000 : ℝ) ≤ ⟪uStar (1 / 4), stmCol 2 (1 / 4)⟫ * (uStar (1 / 4)).ofLp 1 ∧
      ⟪uStar (1 / 4), stmCol 2 (1 / 4)⟫ * (uStar (1 / 4)).ofLp 1 ≤ (-14613 / 1000000 : ℝ) := by
  have hinn := inner_uStar_stmCol2_div4
  have huy := uStar_y_div4
  have h := mul_nonneg_nonpos_bounds (by norm_num) (by norm_num) hinn.1 hinn.2 huy.1 huy.2
  constructor <;> nlinarith [h.1, h.2]

lemma proj_x_stmCol2_div4 :
    (843 / 1000000 : ℝ) ≤
      (stmCol 2 (1 / 4)).ofLp 0
        - ⟪uStar (1 / 4), stmCol 2 (1 / 4)⟫ * (uStar (1 / 4)).ofLp 0 ∧
      (stmCol 2 (1 / 4)).ofLp 0
        - ⟪uStar (1 / 4), stmCol 2 (1 / 4)⟫ * (uStar (1 / 4)).ofLp 0
        ≤ (870 / 1000000 : ℝ) := by
  have hdx := stmCol2_x_div4
  have hm := inn_ux_stmCol2_div4
  constructor <;> nlinarith [hdx.1, hdx.2, hm.1, hm.2]

lemma proj_y_stmCol2_div4 :
    (14616 / 1000000 : ℝ) ≤
      (stmCol 2 (1 / 4)).ofLp 1
        - ⟪uStar (1 / 4), stmCol 2 (1 / 4)⟫ * (uStar (1 / 4)).ofLp 1 ∧
      (stmCol 2 (1 / 4)).ofLp 1
        - ⟪uStar (1 / 4), stmCol 2 (1 / 4)⟫ * (uStar (1 / 4)).ofLp 1
        ≤ (14635 / 1000000 : ℝ) := by
  have hdy := stmCol2_y_div4
  have hm := inn_uy_stmCol2_div4
  constructor <;> nlinarith [hdy.1, hdy.2, hm.1, hm.2]

lemma dlosCol2_x_div4 :
    (551 / 1000000 : ℝ) ≤ (dlosCol 2 (1 / 4)).ofLp 0 ∧
      (dlosCol 2 (1 / 4)).ofLp 0 ≤ (570 / 1000000 : ℝ) := by
  rw [(dlosCol_ofLp01 2 (1 / 4)).1]
  have hp := proj_x_stmCol2_div4
  have hr := inv_rhoStar_div4_tight
  have h := mul_nonneg_bounds (by norm_num) (by norm_num) hr.1 hr.2 hp.1 hp.2
  constructor <;> nlinarith [h.1, h.2]

lemma dlosCol2_y_div4 :
    (9561 / 1000000 : ℝ) ≤ (dlosCol 2 (1 / 4)).ofLp 1 ∧
      (dlosCol 2 (1 / 4)).ofLp 1 ≤ (9574 / 1000000 : ℝ) := by
  rw [(dlosCol_ofLp01 2 (1 / 4)).2]
  have hp := proj_y_stmCol2_div4
  have hr := inv_rhoStar_div4_tight
  have h := mul_nonneg_bounds (by norm_num) (by norm_num) hr.1 hr.2 hp.1 hp.2
  constructor <;> nlinarith [h.1, h.2]

lemma inn_ux_stmCol2_div2 :
    (497398 / 1000000 : ℝ) ≤ ⟪uStar (1 / 2), stmCol 2 (1 / 2)⟫ * (uStar (1 / 2)).ofLp 0 ∧
      ⟪uStar (1 / 2), stmCol 2 (1 / 2)⟫ * (uStar (1 / 2)).ofLp 0 ≤ (497425 / 1000000 : ℝ) := by
  have hinn := inner_uStar_stmCol2_div2
  have hux := uStar_x_div2
  have h := mul_nonneg_bounds (by norm_num) (by norm_num) hinn.1 hinn.2 hux.1 hux.2
  constructor <;> nlinarith [h.1, h.2]

lemma inn_uy_stmCol2_div2 :
    (-50923 / 1000000 : ℝ) ≤ ⟪uStar (1 / 2), stmCol 2 (1 / 2)⟫ * (uStar (1 / 2)).ofLp 1 ∧
      ⟪uStar (1 / 2), stmCol 2 (1 / 2)⟫ * (uStar (1 / 2)).ofLp 1 ≤ (-50917 / 1000000 : ℝ) := by
  have hinn := inner_uStar_stmCol2_div2
  have huy := uStar_y_div2
  have h := mul_nonneg_nonpos_bounds (by norm_num) (by norm_num) hinn.1 hinn.2 huy.1 huy.2
  constructor <;> nlinarith [h.1, h.2]

lemma proj_x_stmCol2_div2 :
    (5217 / 1000000 : ℝ) ≤
      (stmCol 2 (1 / 2)).ofLp 0
        - ⟪uStar (1 / 2), stmCol 2 (1 / 2)⟫ * (uStar (1 / 2)).ofLp 0 ∧
      (stmCol 2 (1 / 2)).ofLp 0
        - ⟪uStar (1 / 2), stmCol 2 (1 / 2)⟫ * (uStar (1 / 2)).ofLp 0
        ≤ (5259 / 1000000 : ℝ) := by
  have hdx := stmCol2_x_div2
  have hm := inn_ux_stmCol2_div2
  constructor <;> nlinarith [hdx.1, hdx.2, hm.1, hm.2]

lemma proj_y_stmCol2_div2 :
    (51158 / 1000000 : ℝ) ≤
      (stmCol 2 (1 / 2)).ofLp 1
        - ⟪uStar (1 / 2), stmCol 2 (1 / 2)⟫ * (uStar (1 / 2)).ofLp 1 ∧
      (stmCol 2 (1 / 2)).ofLp 1
        - ⟪uStar (1 / 2), stmCol 2 (1 / 2)⟫ * (uStar (1 / 2)).ofLp 1
        ≤ (51184 / 1000000 : ℝ) := by
  have hdy := stmCol2_y_div2
  have hm := inn_uy_stmCol2_div2
  constructor <;> nlinarith [hdy.1, hdy.2, hm.1, hm.2]

lemma dlosCol2_x_div2 :
    (3238 / 1000000 : ℝ) ≤ (dlosCol 2 (1 / 2)).ofLp 0 ∧
      (dlosCol 2 (1 / 2)).ofLp 0 ≤ (3265 / 1000000 : ℝ) := by
  rw [(dlosCol_ofLp01 2 (1 / 2)).1]
  have hp := proj_x_stmCol2_div2
  have hr := inv_rhoStar_div2_tight
  have h := mul_nonneg_bounds (by norm_num) (by norm_num) hr.1 hr.2 hp.1 hp.2
  constructor <;> nlinarith [h.1, h.2]

lemma dlosCol2_y_div2 :
    (31758 / 1000000 : ℝ) ≤ (dlosCol 2 (1 / 2)).ofLp 1 ∧
      (dlosCol 2 (1 / 2)).ofLp 1 ≤ (31776 / 1000000 : ℝ) := by
  rw [(dlosCol_ofLp01 2 (1 / 2)).2]
  have hp := proj_y_stmCol2_div2
  have hr := inv_rhoStar_div2_tight
  have h := mul_nonneg_bounds (by norm_num) (by norm_num) hr.1 hr.2 hp.1 hp.2
  constructor <;> nlinarith [h.1, h.2]

lemma inn_ux_stmCol2_one :
    (1007078 / 1000000 : ℝ) ≤ ⟪uStar 1, stmCol 2 1⟫ * (uStar 1).ofLp 0 ∧
      ⟪uStar 1, stmCol 2 1⟫ * (uStar 1).ofLp 0 ≤ (1007253 / 1000000 : ℝ) := by
  have hinn := inner_uStar_stmCol2_one
  have hux := uStar_x_one
  have h := mul_nonneg_bounds (by norm_num) (by norm_num) hinn.1 hinn.2 hux.1 hux.2
  constructor <;> nlinarith [h.1, h.2]

lemma inn_uy_stmCol2_one :
    (-115579 / 1000000 : ℝ) ≤ ⟪uStar 1, stmCol 2 1⟫ * (uStar 1).ofLp 1 ∧
      ⟪uStar 1, stmCol 2 1⟫ * (uStar 1).ofLp 1 ≤ (-115554 / 1000000 : ℝ) := by
  have hinn := inner_uStar_stmCol2_one
  have huy := uStar_y_one
  have h := mul_nonneg_nonpos_bounds (by norm_num) (by norm_num) hinn.1 hinn.2 huy.1 huy.2
  constructor <;> nlinarith [h.1, h.2]

lemma proj_x_stmCol2_one :
    (13598 / 1000000 : ℝ) ≤
      (stmCol 2 1).ofLp 0
        - ⟪uStar 1, stmCol 2 1⟫ * (uStar 1).ofLp 0 ∧
      (stmCol 2 1).ofLp 0
        - ⟪uStar 1, stmCol 2 1⟫ * (uStar 1).ofLp 0
        ≤ (13790 / 1000000 : ℝ) := by
  have hdx := stmCol2_x_one
  have hm := inn_ux_stmCol2_one
  constructor <;> nlinarith [hdx.1, hdx.2, hm.1, hm.2]

lemma proj_y_stmCol2_one :
    (119554 / 1000000 : ℝ) ≤
      (stmCol 2 1).ofLp 1
        - ⟪uStar 1, stmCol 2 1⟫ * (uStar 1).ofLp 1 ∧
      (stmCol 2 1).ofLp 1
        - ⟪uStar 1, stmCol 2 1⟫ * (uStar 1).ofLp 1
        ≤ (119600 / 1000000 : ℝ) := by
  have hdy := stmCol2_y_one
  have hm := inn_uy_stmCol2_one
  constructor <;> nlinarith [hdy.1, hdy.2, hm.1, hm.2]

lemma dlosCol2_x_one :
    (7185 / 1000000 : ℝ) ≤ (dlosCol 2 1).ofLp 0 ∧
      (dlosCol 2 1).ofLp 0 ≤ (7287 / 1000000 : ℝ) := by
  rw [(dlosCol_ofLp01 2 1).1]
  have hp := proj_x_stmCol2_one
  have hr := inv_rhoStar_one_tight
  have h := mul_nonneg_bounds (by norm_num) (by norm_num) hr.1 hr.2 hp.1 hp.2
  constructor <;> nlinarith [h.1, h.2]

lemma dlosCol2_y_one :
    (63172 / 1000000 : ℝ) ≤ (dlosCol 2 1).ofLp 1 ∧
      (dlosCol 2 1).ofLp 1 ≤ (63200 / 1000000 : ℝ) := by
  rw [(dlosCol_ofLp01 2 1).2]
  have hp := proj_y_stmCol2_one
  have hr := inv_rhoStar_one_tight
  have h := mul_nonneg_bounds (by norm_num) (by norm_num) hr.1 hr.2 hp.1 hp.2
  constructor <;> nlinarith [h.1, h.2]

lemma inn_ux_stmCol3_div4 :
    (-14577 / 1000000 : ℝ) ≤ ⟪uStar (1 / 4), stmCol 3 (1 / 4)⟫ * (uStar (1 / 4)).ofLp 0 ∧
      ⟪uStar (1 / 4), stmCol 3 (1 / 4)⟫ * (uStar (1 / 4)).ofLp 0 ≤ (-14554 / 1000000 : ℝ) := by
  have hinn := inner_uStar_stmCol3_div4
  have hux := uStar_x_div4
  have h := mul_nonpos_nonneg_bounds (by norm_num) (by norm_num) hinn.1 hinn.2 hux.1 hux.2
  constructor <;> nlinarith [h.1, h.2]

lemma inn_uy_stmCol3_div4 :
    (852 / 1000000 : ℝ) ≤ ⟪uStar (1 / 4), stmCol 3 (1 / 4)⟫ * (uStar (1 / 4)).ofLp 1 ∧
      ⟪uStar (1 / 4), stmCol 3 (1 / 4)⟫ * (uStar (1 / 4)).ofLp 1 ≤ (854 / 1000000 : ℝ) := by
  have hinn := inner_uStar_stmCol3_div4
  have huy := uStar_y_div4
  have h := mul_nonpos_nonpos_bounds (by norm_num) (by norm_num) hinn.1 hinn.2 huy.1 huy.2
  constructor <;> nlinarith [h.1, h.2]

lemma proj_x_stmCol3_div4 :
    (14565 / 1000000 : ℝ) ≤
      (stmCol 3 (1 / 4)).ofLp 0
        - ⟪uStar (1 / 4), stmCol 3 (1 / 4)⟫ * (uStar (1 / 4)).ofLp 0 ∧
      (stmCol 3 (1 / 4)).ofLp 0
        - ⟪uStar (1 / 4), stmCol 3 (1 / 4)⟫ * (uStar (1 / 4)).ofLp 0
        ≤ (14605 / 1000000 : ℝ) := by
  have hdx := stmCol3_x_div4
  have hm := inn_ux_stmCol3_div4
  constructor <;> nlinarith [hdx.1, hdx.2, hm.1, hm.2]

lemma proj_y_stmCol3_div4 :
    (248961 / 1000000 : ℝ) ≤
      (stmCol 3 (1 / 4)).ofLp 1
        - ⟪uStar (1 / 4), stmCol 3 (1 / 4)⟫ * (uStar (1 / 4)).ofLp 1 ∧
      (stmCol 3 (1 / 4)).ofLp 1
        - ⟪uStar (1 / 4), stmCol 3 (1 / 4)⟫ * (uStar (1 / 4)).ofLp 1
        ≤ (248996 / 1000000 : ℝ) := by
  have hdy := stmCol3_y_div4
  have hm := inn_uy_stmCol3_div4
  constructor <;> nlinarith [hdy.1, hdy.2, hm.1, hm.2]

lemma dlosCol3_x_div4 :
    (9527 / 1000000 : ℝ) ≤ (dlosCol 3 (1 / 4)).ofLp 0 ∧
      (dlosCol 3 (1 / 4)).ofLp 0 ≤ (9554 / 1000000 : ℝ) := by
  rw [(dlosCol_ofLp01 3 (1 / 4)).1]
  have hp := proj_x_stmCol3_div4
  have hr := inv_rhoStar_div4_tight
  have h := mul_nonneg_bounds (by norm_num) (by norm_num) hr.1 hr.2 hp.1 hp.2
  constructor <;> nlinarith [h.1, h.2]

lemma dlosCol3_y_div4 :
    (162857 / 1000000 : ℝ) ≤ (dlosCol 3 (1 / 4)).ofLp 1 ∧
      (dlosCol 3 (1 / 4)).ofLp 1 ≤ (162881 / 1000000 : ℝ) := by
  rw [(dlosCol_ofLp01 3 (1 / 4)).2]
  have hp := proj_y_stmCol3_div4
  have hr := inv_rhoStar_div4_tight
  have h := mul_nonneg_bounds (by norm_num) (by norm_num) hr.1 hr.2 hp.1 hp.2
  constructor <;> nlinarith [h.1, h.2]

lemma inn_ux_stmCol3_div2 :
    (-50283 / 1000000 : ℝ) ≤ ⟪uStar (1 / 2), stmCol 3 (1 / 2)⟫ * (uStar (1 / 2)).ofLp 0 ∧
      ⟪uStar (1 / 2), stmCol 3 (1 / 2)⟫ * (uStar (1 / 2)).ofLp 0 ≤ (-50253 / 1000000 : ℝ) := by
  have hinn := inner_uStar_stmCol3_div2
  have hux := uStar_x_div2
  have h := mul_nonpos_nonneg_bounds (by norm_num) (by norm_num) hinn.1 hinn.2 hux.1 hux.2
  constructor <;> nlinarith [h.1, h.2]

lemma inn_uy_stmCol3_div2 :
    (5144 / 1000000 : ℝ) ≤ ⟪uStar (1 / 2), stmCol 3 (1 / 2)⟫ * (uStar (1 / 2)).ofLp 1 ∧
      ⟪uStar (1 / 2), stmCol 3 (1 / 2)⟫ * (uStar (1 / 2)).ofLp 1 ≤ (5148 / 1000000 : ℝ) := by
  have hinn := inner_uStar_stmCol3_div2
  have huy := uStar_y_div2
  have h := mul_nonpos_nonpos_bounds (by norm_num) (by norm_num) hinn.1 hinn.2 huy.1 huy.2
  constructor <;> nlinarith [h.1, h.2]

lemma proj_x_stmCol3_div2 :
    (50498 / 1000000 : ℝ) ≤
      (stmCol 3 (1 / 2)).ofLp 0
        - ⟪uStar (1 / 2), stmCol 3 (1 / 2)⟫ * (uStar (1 / 2)).ofLp 0 ∧
      (stmCol 3 (1 / 2)).ofLp 0
        - ⟪uStar (1 / 2), stmCol 3 (1 / 2)⟫ * (uStar (1 / 2)).ofLp 0
        ≤ (50548 / 1000000 : ℝ) := by
  have hdx := stmCol3_x_div2
  have hm := inn_ux_stmCol3_div2
  constructor <;> nlinarith [hdx.1, hdx.2, hm.1, hm.2]

lemma proj_y_stmCol3_div2 :
    (493509 / 1000000 : ℝ) ≤
      (stmCol 3 (1 / 2)).ofLp 1
        - ⟪uStar (1 / 2), stmCol 3 (1 / 2)⟫ * (uStar (1 / 2)).ofLp 1 ∧
      (stmCol 3 (1 / 2)).ofLp 1
        - ⟪uStar (1 / 2), stmCol 3 (1 / 2)⟫ * (uStar (1 / 2)).ofLp 1
        ≤ (493564 / 1000000 : ℝ) := by
  have hdy := stmCol3_y_div2
  have hm := inn_uy_stmCol3_div2
  constructor <;> nlinarith [hdy.1, hdy.2, hm.1, hm.2]

lemma dlosCol3_x_div2 :
    (31349 / 1000000 : ℝ) ≤ (dlosCol 3 (1 / 2)).ofLp 0 ∧
      (dlosCol 3 (1 / 2)).ofLp 0 ≤ (31381 / 1000000 : ℝ) := by
  rw [(dlosCol_ofLp01 3 (1 / 2)).1]
  have hp := proj_x_stmCol3_div2
  have hr := inv_rhoStar_div2_tight
  have h := mul_nonneg_bounds (by norm_num) (by norm_num) hr.1 hr.2 hp.1 hp.2
  constructor <;> nlinarith [h.1, h.2]

lemma dlosCol3_y_div2 :
    (306370 / 1000000 : ℝ) ≤ (dlosCol 3 (1 / 2)).ofLp 1 ∧
      (dlosCol 3 (1 / 2)).ofLp 1 ≤ (306407 / 1000000 : ℝ) := by
  rw [(dlosCol_ofLp01 3 (1 / 2)).2]
  have hp := proj_y_stmCol3_div2
  have hr := inv_rhoStar_div2_tight
  have h := mul_nonneg_bounds (by norm_num) (by norm_num) hr.1 hr.2 hp.1 hp.2
  constructor <;> nlinarith [h.1, h.2]

lemma inn_ux_stmCol3_one :
    (-108228 / 1000000 : ℝ) ≤ ⟪uStar 1, stmCol 3 1⟫ * (uStar 1).ofLp 0 ∧
      ⟪uStar 1, stmCol 3 1⟫ * (uStar 1).ofLp 0 ≤ (-108169 / 1000000 : ℝ) := by
  have hinn := inner_uStar_stmCol3_one
  have hux := uStar_x_one
  have h := mul_nonpos_nonneg_bounds (by norm_num) (by norm_num) hinn.1 hinn.2 hux.1 hux.2
  constructor <;> nlinarith [h.1, h.2]

lemma inn_uy_stmCol3_one :
    (12411 / 1000000 : ℝ) ≤ ⟪uStar 1, stmCol 3 1⟫ * (uStar 1).ofLp 1 ∧
      ⟪uStar 1, stmCol 3 1⟫ * (uStar 1).ofLp 1 ≤ (12419 / 1000000 : ℝ) := by
  have hinn := inner_uStar_stmCol3_one
  have huy := uStar_y_one
  have h := mul_nonpos_nonpos_bounds (by norm_num) (by norm_num) hinn.1 hinn.2 huy.1 huy.2
  constructor <;> nlinarith [h.1, h.2]

lemma proj_x_stmCol3_one :
    (112129 / 1000000 : ℝ) ≤
      (stmCol 3 1).ofLp 0
        - ⟪uStar 1, stmCol 3 1⟫ * (uStar 1).ofLp 0 ∧
      (stmCol 3 1).ofLp 0
        - ⟪uStar 1, stmCol 3 1⟫ * (uStar 1).ofLp 0
        ≤ (112217 / 1000000 : ℝ) := by
  have hdx := stmCol3_x_one
  have hm := inn_ux_stmCol3_one
  constructor <;> nlinarith [hdx.1, hdx.2, hm.1, hm.2]

lemma proj_y_stmCol3_one :
    (977536 / 1000000 : ℝ) ≤
      (stmCol 3 1).ofLp 1
        - ⟪uStar 1, stmCol 3 1⟫ * (uStar 1).ofLp 1 ∧
      (stmCol 3 1).ofLp 1
        - ⟪uStar 1, stmCol 3 1⟫ * (uStar 1).ofLp 1
        ≤ (977601 / 1000000 : ℝ) := by
  have hdy := stmCol3_y_one
  have hm := inn_uy_stmCol3_one
  constructor <;> nlinarith [hdy.1, hdy.2, hm.1, hm.2]

lemma dlosCol3_x_one :
    (59249 / 1000000 : ℝ) ≤ (dlosCol 3 1).ofLp 0 ∧
      (dlosCol 3 1).ofLp 0 ≤ (59299 / 1000000 : ℝ) := by
  rw [(dlosCol_ofLp01 3 1).1]
  have hp := proj_x_stmCol3_one
  have hr := inv_rhoStar_one_tight
  have h := mul_nonneg_bounds (by norm_num) (by norm_num) hr.1 hr.2 hp.1 hp.2
  constructor <;> nlinarith [h.1, h.2]

lemma dlosCol3_y_one :
    (516530 / 1000000 : ℝ) ≤ (dlosCol 3 1).ofLp 1 ∧
      (dlosCol 3 1).ofLp 1 ≤ (516588 / 1000000 : ℝ) := by
  rw [(dlosCol_ofLp01 3 1).2]
  have hp := proj_y_stmCol3_one
  have hr := inv_rhoStar_one_tight
  have h := mul_nonneg_bounds (by norm_num) (by norm_num) hr.1 hr.2 hp.1 hp.2
  constructor <;> nlinarith [h.1, h.2]

lemma xyBlkSTM_00_eq :
    xyBlkSTM 0 0 = (dlosCol 0 0).ofLp 0 - 2 * (dlosCol 0 (1 / 4)).ofLp 0 + (dlosCol 0 (1 / 2)).ofLp 0 := by
  have ht : (2 : ℝ) * (4 : ℝ)⁻¹ = (2 : ℝ)⁻¹ := by norm_num
  rw [xyBlkSTM_apply]
  simp [hSD1, sdPairCoord, inPlaneOut, secondDiff_dlosCol]
  rw [ht]

lemma xyBlkSTM_10_eq :
    xyBlkSTM 1 0 = (dlosCol 0 0).ofLp 1 - 2 * (dlosCol 0 (1 / 4)).ofLp 1 + (dlosCol 0 (1 / 2)).ofLp 1 := by
  have ht : (2 : ℝ) * (4 : ℝ)⁻¹ = (2 : ℝ)⁻¹ := by norm_num
  rw [xyBlkSTM_apply]
  simp [hSD1, sdPairCoord, inPlaneOut, secondDiff_dlosCol]
  rw [ht]

lemma xyBlkSTM_20_eq :
    xyBlkSTM 2 0 = (dlosCol 0 0).ofLp 0 - 2 * (dlosCol 0 (1 / 2)).ofLp 0 + (dlosCol 0 1).ofLp 0 := by
  rw [xyBlkSTM_apply]
  simp [hSD2, sdPairCoord, inPlaneOut, secondDiff_dlosCol,
    ofLp_add, ofLp_sub, ofLp_smul]

lemma xyBlkSTM_30_eq :
    xyBlkSTM 3 0 = (dlosCol 0 0).ofLp 1 - 2 * (dlosCol 0 (1 / 2)).ofLp 1 + (dlosCol 0 1).ofLp 1 := by
  rw [xyBlkSTM_apply]
  simp [hSD2, sdPairCoord, inPlaneOut, secondDiff_dlosCol,
    ofLp_add, ofLp_sub, ofLp_smul]

lemma xyBlkSTM_01_eq :
    xyBlkSTM 0 1 = (dlosCol 1 0).ofLp 0 - 2 * (dlosCol 1 (1 / 4)).ofLp 0 + (dlosCol 1 (1 / 2)).ofLp 0 := by
  have ht : (2 : ℝ) * (4 : ℝ)⁻¹ = (2 : ℝ)⁻¹ := by norm_num
  rw [xyBlkSTM_apply]
  simp [hSD1, sdPairCoord, inPlaneOut, secondDiff_dlosCol]
  rw [ht]

lemma xyBlkSTM_11_eq :
    xyBlkSTM 1 1 = (dlosCol 1 0).ofLp 1 - 2 * (dlosCol 1 (1 / 4)).ofLp 1 + (dlosCol 1 (1 / 2)).ofLp 1 := by
  have ht : (2 : ℝ) * (4 : ℝ)⁻¹ = (2 : ℝ)⁻¹ := by norm_num
  rw [xyBlkSTM_apply]
  simp [hSD1, sdPairCoord, inPlaneOut, secondDiff_dlosCol]
  rw [ht]

lemma xyBlkSTM_21_eq :
    xyBlkSTM 2 1 = (dlosCol 1 0).ofLp 0 - 2 * (dlosCol 1 (1 / 2)).ofLp 0 + (dlosCol 1 1).ofLp 0 := by
  rw [xyBlkSTM_apply]
  simp [hSD2, sdPairCoord, inPlaneOut, secondDiff_dlosCol,
    ofLp_add, ofLp_sub, ofLp_smul]

lemma xyBlkSTM_31_eq :
    xyBlkSTM 3 1 = (dlosCol 1 0).ofLp 1 - 2 * (dlosCol 1 (1 / 2)).ofLp 1 + (dlosCol 1 1).ofLp 1 := by
  rw [xyBlkSTM_apply]
  simp [hSD2, sdPairCoord, inPlaneOut, secondDiff_dlosCol,
    ofLp_add, ofLp_sub, ofLp_smul]

lemma xyBlkSTM_02_eq :
    xyBlkSTM 0 2 = (dlosCol 2 0).ofLp 0 - 2 * (dlosCol 2 (1 / 4)).ofLp 0 + (dlosCol 2 (1 / 2)).ofLp 0 := by
  have ht : (2 : ℝ) * (4 : ℝ)⁻¹ = (2 : ℝ)⁻¹ := by norm_num
  rw [xyBlkSTM_apply]
  simp [hSD1, sdPairCoord, inPlaneOut, secondDiff_dlosCol]
  rw [ht]

lemma xyBlkSTM_12_eq :
    xyBlkSTM 1 2 = (dlosCol 2 0).ofLp 1 - 2 * (dlosCol 2 (1 / 4)).ofLp 1 + (dlosCol 2 (1 / 2)).ofLp 1 := by
  have ht : (2 : ℝ) * (4 : ℝ)⁻¹ = (2 : ℝ)⁻¹ := by norm_num
  rw [xyBlkSTM_apply]
  simp [hSD1, sdPairCoord, inPlaneOut, secondDiff_dlosCol]
  rw [ht]

lemma xyBlkSTM_22_eq :
    xyBlkSTM 2 2 = (dlosCol 2 0).ofLp 0 - 2 * (dlosCol 2 (1 / 2)).ofLp 0 + (dlosCol 2 1).ofLp 0 := by
  rw [xyBlkSTM_apply]
  simp [hSD2, sdPairCoord, inPlaneOut, secondDiff_dlosCol,
    ofLp_add, ofLp_sub, ofLp_smul]

lemma xyBlkSTM_32_eq :
    xyBlkSTM 3 2 = (dlosCol 2 0).ofLp 1 - 2 * (dlosCol 2 (1 / 2)).ofLp 1 + (dlosCol 2 1).ofLp 1 := by
  rw [xyBlkSTM_apply]
  simp [hSD2, sdPairCoord, inPlaneOut, secondDiff_dlosCol,
    ofLp_add, ofLp_sub, ofLp_smul]

lemma xyBlkSTM_03_eq :
    xyBlkSTM 0 3 = (dlosCol 3 0).ofLp 0 - 2 * (dlosCol 3 (1 / 4)).ofLp 0 + (dlosCol 3 (1 / 2)).ofLp 0 := by
  have ht : (2 : ℝ) * (4 : ℝ)⁻¹ = (2 : ℝ)⁻¹ := by norm_num
  rw [xyBlkSTM_apply]
  simp [hSD1, sdPairCoord, inPlaneOut, secondDiff_dlosCol]
  rw [ht]

lemma xyBlkSTM_13_eq :
    xyBlkSTM 1 3 = (dlosCol 3 0).ofLp 1 - 2 * (dlosCol 3 (1 / 4)).ofLp 1 + (dlosCol 3 (1 / 2)).ofLp 1 := by
  have ht : (2 : ℝ) * (4 : ℝ)⁻¹ = (2 : ℝ)⁻¹ := by norm_num
  rw [xyBlkSTM_apply]
  simp [hSD1, sdPairCoord, inPlaneOut, secondDiff_dlosCol]
  rw [ht]

lemma xyBlkSTM_23_eq :
    xyBlkSTM 2 3 = (dlosCol 3 0).ofLp 0 - 2 * (dlosCol 3 (1 / 2)).ofLp 0 + (dlosCol 3 1).ofLp 0 := by
  rw [xyBlkSTM_apply]
  simp [hSD2, sdPairCoord, inPlaneOut, secondDiff_dlosCol,
    ofLp_add, ofLp_sub, ofLp_smul]

lemma xyBlkSTM_33_eq :
    xyBlkSTM 3 3 = (dlosCol 3 0).ofLp 1 - 2 * (dlosCol 3 (1 / 2)).ofLp 1 + (dlosCol 3 1).ofLp 1 := by
  rw [xyBlkSTM_apply]
  simp [hSD2, sdPairCoord, inPlaneOut, secondDiff_dlosCol,
    ofLp_add, ofLp_sub, ofLp_smul]

lemma xyBlkSTM_00 :
    (2077 / 1000000 : ℝ) ≤ xyBlkSTM 0 0 ∧ xyBlkSTM 0 0 ≤ (2133 / 1000000 : ℝ) := by
  rw [xyBlkSTM_00_eq]
  have hz : (dlosCol 0 0).ofLp 0 = 0 := by simpa using dlosCol0_zero_ofLp 0
  have ha := dlosCol0_x_div4
  have hb := dlosCol0_x_div2
  rw [hz]
  constructor <;> nlinarith [ha.1, ha.2, hb.1, hb.2]

lemma xyBlkSTM_10 :
    (-12344 / 1000000 : ℝ) ≤ xyBlkSTM 1 0 ∧ xyBlkSTM 1 0 ≤ (-12311 / 1000000 : ℝ) := by
  rw [xyBlkSTM_10_eq]
  have hz : (dlosCol 0 0).ofLp 1 = 0 := by simpa using dlosCol0_zero_ofLp 1
  have ha := dlosCol0_y_div4
  have hb := dlosCol0_y_div2
  rw [hz]
  constructor <;> nlinarith [ha.1, ha.2, hb.1, hb.2]

lemma xyBlkSTM_20 :
    (-5502 / 1000000 : ℝ) ≤ xyBlkSTM 2 0 ∧ xyBlkSTM 2 0 ≤ (-5367 / 1000000 : ℝ) := by
  rw [xyBlkSTM_20_eq]
  have hz : (dlosCol 0 0).ofLp 0 = 0 := by simpa using dlosCol0_zero_ofLp 0
  have ha := dlosCol0_x_div2
  have hb := dlosCol0_x_one
  rw [hz]
  constructor <;> nlinarith [ha.1, ha.2, hb.1, hb.2]

lemma xyBlkSTM_30 :
    (-61171 / 1000000 : ℝ) ≤ xyBlkSTM 3 0 ∧ xyBlkSTM 3 0 ≤ (-61122 / 1000000 : ℝ) := by
  rw [xyBlkSTM_30_eq]
  have hz : (dlosCol 0 0).ofLp 1 = 0 := by simpa using dlosCol0_zero_ofLp 1
  have ha := dlosCol0_y_div2
  have hb := dlosCol0_y_one
  rw [hz]
  constructor <;> nlinarith [ha.1, ha.2, hb.1, hb.2]

lemma xyBlkSTM_01 :
    (-13834 / 1000000 : ℝ) ≤ xyBlkSTM 0 1 ∧ xyBlkSTM 0 1 ≤ (-13814 / 1000000 : ℝ) := by
  rw [xyBlkSTM_01_eq]
  have hz : (dlosCol 1 0).ofLp 0 = 0 := dlosCol1_zero_ofLp.1
  have ha := dlosCol1_x_div4
  have hb := dlosCol1_x_div2
  rw [hz]
  constructor <;> nlinarith [ha.1, ha.2, hb.1, hb.2]

lemma xyBlkSTM_11 :
    (-25018 / 1000000 : ℝ) ≤ xyBlkSTM 1 1 ∧ xyBlkSTM 1 1 ≤ (-24995 / 1000000 : ℝ) := by
  rw [xyBlkSTM_11_eq]
  have hz : (dlosCol 1 0).ofLp 1 = (2 / 3 : ℝ) := dlosCol1_zero_ofLp.2.1
  have ha := dlosCol1_y_div4
  have hb := dlosCol1_y_div2
  rw [hz]
  constructor <;> nlinarith [ha.1, ha.2, hb.1, hb.2]

lemma xyBlkSTM_21 :
    (-66760 / 1000000 : ℝ) ≤ xyBlkSTM 2 1 ∧ xyBlkSTM 2 1 ≤ (-66727 / 1000000 : ℝ) := by
  rw [xyBlkSTM_21_eq]
  have hz : (dlosCol 1 0).ofLp 0 = 0 := dlosCol1_zero_ofLp.1
  have ha := dlosCol1_x_div2
  have hb := dlosCol1_x_one
  rw [hz]
  constructor <;> nlinarith [ha.1, ha.2, hb.1, hb.2]

lemma xyBlkSTM_31 :
    (-46521 / 1000000 : ℝ) ≤ xyBlkSTM 3 1 ∧ xyBlkSTM 3 1 ≤ (-46477 / 1000000 : ℝ) := by
  rw [xyBlkSTM_31_eq]
  have hz : (dlosCol 1 0).ofLp 1 = (2 / 3 : ℝ) := dlosCol1_zero_ofLp.2.1
  have ha := dlosCol1_y_div2
  have hb := dlosCol1_y_one
  rw [hz]
  constructor <;> nlinarith [ha.1, ha.2, hb.1, hb.2]

lemma xyBlkSTM_02 :
    (2098 / 1000000 : ℝ) ≤ xyBlkSTM 0 2 ∧ xyBlkSTM 0 2 ≤ (2163 / 1000000 : ℝ) := by
  rw [xyBlkSTM_02_eq]
  have hz : (dlosCol 2 0).ofLp 0 = 0 := by simp [dlosCol2_zero, PiLp.zero_apply]
  have ha := dlosCol2_x_div4
  have hb := dlosCol2_x_div2
  rw [hz]
  constructor <;> nlinarith [ha.1, ha.2, hb.1, hb.2]

lemma xyBlkSTM_12 :
    (12610 / 1000000 : ℝ) ≤ xyBlkSTM 1 2 ∧ xyBlkSTM 1 2 ≤ (12654 / 1000000 : ℝ) := by
  rw [xyBlkSTM_12_eq]
  have hz : (dlosCol 2 0).ofLp 1 = 0 := by simp [dlosCol2_zero, PiLp.zero_apply]
  have ha := dlosCol2_y_div4
  have hb := dlosCol2_y_div2
  rw [hz]
  constructor <;> nlinarith [ha.1, ha.2, hb.1, hb.2]

lemma xyBlkSTM_22 :
    (655 / 1000000 : ℝ) ≤ xyBlkSTM 2 2 ∧ xyBlkSTM 2 2 ≤ (811 / 1000000 : ℝ) := by
  rw [xyBlkSTM_22_eq]
  have hz : (dlosCol 2 0).ofLp 0 = 0 := by simp [dlosCol2_zero, PiLp.zero_apply]
  have ha := dlosCol2_x_div2
  have hb := dlosCol2_x_one
  rw [hz]
  constructor <;> nlinarith [ha.1, ha.2, hb.1, hb.2]

lemma xyBlkSTM_32 :
    (-380 / 1000000 : ℝ) ≤ xyBlkSTM 3 2 ∧ xyBlkSTM 3 2 ≤ (-316 / 1000000 : ℝ) := by
  rw [xyBlkSTM_32_eq]
  have hz : (dlosCol 2 0).ofLp 1 = 0 := by simp [dlosCol2_zero, PiLp.zero_apply]
  have ha := dlosCol2_y_div2
  have hb := dlosCol2_y_one
  rw [hz]
  constructor <;> nlinarith [ha.1, ha.2, hb.1, hb.2]

lemma xyBlkSTM_03 :
    (12241 / 1000000 : ℝ) ≤ xyBlkSTM 0 3 ∧ xyBlkSTM 0 3 ≤ (12327 / 1000000 : ℝ) := by
  rw [xyBlkSTM_03_eq]
  have hz : (dlosCol 3 0).ofLp 0 = 0 := by simp [dlosCol3_zero, PiLp.zero_apply]
  have ha := dlosCol3_x_div4
  have hb := dlosCol3_x_div2
  rw [hz]
  constructor <;> nlinarith [ha.1, ha.2, hb.1, hb.2]

lemma xyBlkSTM_13 :
    (-19392 / 1000000 : ℝ) ≤ xyBlkSTM 1 3 ∧ xyBlkSTM 1 3 ≤ (-19307 / 1000000 : ℝ) := by
  rw [xyBlkSTM_13_eq]
  have hz : (dlosCol 3 0).ofLp 1 = 0 := by simp [dlosCol3_zero, PiLp.zero_apply]
  have ha := dlosCol3_y_div4
  have hb := dlosCol3_y_div2
  rw [hz]
  constructor <;> nlinarith [ha.1, ha.2, hb.1, hb.2]

lemma xyBlkSTM_23 :
    (-3513 / 1000000 : ℝ) ≤ xyBlkSTM 2 3 ∧ xyBlkSTM 2 3 ≤ (-3399 / 1000000 : ℝ) := by
  rw [xyBlkSTM_23_eq]
  have hz : (dlosCol 3 0).ofLp 0 = 0 := by simp [dlosCol3_zero, PiLp.zero_apply]
  have ha := dlosCol3_x_div2
  have hb := dlosCol3_x_one
  rw [hz]
  constructor <;> nlinarith [ha.1, ha.2, hb.1, hb.2]

lemma xyBlkSTM_33 :
    (-96284 / 1000000 : ℝ) ≤ xyBlkSTM 3 3 ∧ xyBlkSTM 3 3 ≤ (-96152 / 1000000 : ℝ) := by
  rw [xyBlkSTM_33_eq]
  have hz : (dlosCol 3 0).ofLp 1 = 0 := by simp [dlosCol3_zero, PiLp.zero_apply]
  have ha := dlosCol3_y_div2
  have hb := dlosCol3_y_one
  rw [hz]
  constructor <;> nlinarith [ha.1, ha.2, hb.1, hb.2]

lemma det_fin_four (A : Matrix (Fin 4) (Fin 4) ℝ) :
    det A =
      A 0 0 * A 1 1 * A 2 2 * A 3 3
    - A 0 0 * A 1 1 * A 2 3 * A 3 2
    - A 0 0 * A 1 2 * A 2 1 * A 3 3
    + A 0 0 * A 1 2 * A 2 3 * A 3 1
    + A 0 0 * A 1 3 * A 2 1 * A 3 2
    - A 0 0 * A 1 3 * A 2 2 * A 3 1
    - A 0 1 * A 1 0 * A 2 2 * A 3 3
    + A 0 1 * A 1 0 * A 2 3 * A 3 2
    + A 0 1 * A 1 2 * A 2 0 * A 3 3
    - A 0 1 * A 1 2 * A 2 3 * A 3 0
    - A 0 1 * A 1 3 * A 2 0 * A 3 2
    + A 0 1 * A 1 3 * A 2 2 * A 3 0
    + A 0 2 * A 1 0 * A 2 1 * A 3 3
    - A 0 2 * A 1 0 * A 2 3 * A 3 1
    - A 0 2 * A 1 1 * A 2 0 * A 3 3
    + A 0 2 * A 1 1 * A 2 3 * A 3 0
    + A 0 2 * A 1 3 * A 2 0 * A 3 1
    - A 0 2 * A 1 3 * A 2 1 * A 3 0
    - A 0 3 * A 1 0 * A 2 1 * A 3 2
    + A 0 3 * A 1 0 * A 2 2 * A 3 1
    + A 0 3 * A 1 1 * A 2 0 * A 3 2
    - A 0 3 * A 1 1 * A 2 2 * A 3 0
    - A 0 3 * A 1 2 * A 2 0 * A 3 1
    + A 0 3 * A 1 2 * A 2 1 * A 3 0 := by
  rw [Matrix.det_succ_row_zero]
  simp [Fin.sum_univ_four, Matrix.submatrix_apply, pow_zero, pow_succ]
  rw [Matrix.det_fin_three, Matrix.det_fin_three, Matrix.det_fin_three,
    Matrix.det_fin_three]
  simp [Matrix.submatrix_apply, Fin.succ_zero_eq_one, Fin.succ_one_eq_two]
  -- succAbove on Fin 4
  have h00 : (0 : Fin 4).succAbove 0 = 1 := rfl
  have h01 : (0 : Fin 4).succAbove 1 = 2 := rfl
  have h02 : (0 : Fin 4).succAbove 2 = 3 := rfl
  have h10 : (1 : Fin 4).succAbove 0 = 0 := rfl
  have h11 : (1 : Fin 4).succAbove 1 = 2 := rfl
  have h12 : (1 : Fin 4).succAbove 2 = 3 := rfl
  have h20 : (2 : Fin 4).succAbove 0 = 0 := rfl
  have h21 : (2 : Fin 4).succAbove 1 = 1 := rfl
  have h22 : (2 : Fin 4).succAbove 2 = 3 := rfl
  have h30 : (3 : Fin 4).succAbove 0 = 0 := rfl
  have h31 : (3 : Fin 4).succAbove 1 = 1 := rfl
  have h32 : (3 : Fin 4).succAbove 2 = 2 := rfl
  have hs0 : (0 : Fin 3).succ = 1 := rfl
  have hs1 : (1 : Fin 3).succ = 2 := rfl
  have hs2 : (2 : Fin 3).succ = 3 := rfl
  simp [h00, h01, h02, h10, h11, h12, h20, h21, h22, h30, h31, h32,
    hs0, hs1, hs2]
  ring

lemma xyBlkSTM_prod_0 :
    (3269559610269400 / 1000000000000000000000000 : ℝ) ≤ (xyBlkSTM 0 0 * xyBlkSTM 1 1 * xyBlkSTM 2 2 * xyBlkSTM 3 3) ∧
      (xyBlkSTM 0 0 * xyBlkSTM 1 1 * xyBlkSTM 2 2 * xyBlkSTM 3 3) ≤ (4166951273623656 / 1000000000000000000000000 : ℝ) := by
  have e0 := xyBlkSTM_00
  have e1 := xyBlkSTM_11
  have e2 := xyBlkSTM_22
  have e3 := xyBlkSTM_33
  have p1 : (-53363394 / 1000000000000 : ℝ) ≤ (xyBlkSTM 0 0 * xyBlkSTM 1 1) ∧
      (xyBlkSTM 0 0 * xyBlkSTM 1 1) ≤ (-51914615 / 1000000000000 : ℝ) := by
    have hm := mul_nonneg_nonpos_bounds (by norm_num : (0 : ℝ) ≤ (2077 / 1000000 : ℝ)) (by norm_num : (-24995 / 1000000 : ℝ) ≤ (0 : ℝ)) e0.1 e0.2 e1.1 e1.2
    convert hm using 1 <;> norm_num
  have p2 : (-43277712534 / 1000000000000000000 : ℝ) ≤ (xyBlkSTM 0 0 * xyBlkSTM 1 1 * xyBlkSTM 2 2) ∧
      (xyBlkSTM 0 0 * xyBlkSTM 1 1 * xyBlkSTM 2 2) ≤ (-34004072825 / 1000000000000000000 : ℝ) := by
    have hm := mul_nonpos_nonneg_bounds (by norm_num : (-51914615 / 1000000000000 : ℝ) ≤ (0 : ℝ)) (by norm_num : (0 : ℝ) ≤ (655 / 1000000 : ℝ)) p1.1 p1.2 e2.1 e2.2
    convert hm using 1 <;> norm_num
  have p3 : (3269559610269400 / 1000000000000000000000000 : ℝ) ≤ (xyBlkSTM 0 0 * xyBlkSTM 1 1 * xyBlkSTM 2 2 * xyBlkSTM 3 3) ∧
      (xyBlkSTM 0 0 * xyBlkSTM 1 1 * xyBlkSTM 2 2 * xyBlkSTM 3 3) ≤ (4166951273623656 / 1000000000000000000000000 : ℝ) := by
    have hm := mul_nonpos_nonpos_bounds (by norm_num : (-34004072825 / 1000000000000000000 : ℝ) ≤ (0 : ℝ)) (by norm_num : (-96152 / 1000000 : ℝ) ≤ (0 : ℝ)) p2.1 p2.2 e3.1 e3.2
    convert hm using 1 <;> norm_num
  exact p3

lemma xyBlkSTM_prod_1 :
    (-71236929186360 / 1000000000000000000000000 : ℝ) ≤ (xyBlkSTM 0 0 * xyBlkSTM 1 1 * xyBlkSTM 2 3 * xyBlkSTM 3 2) ∧
      (xyBlkSTM 0 0 * xyBlkSTM 1 1 * xyBlkSTM 2 3 * xyBlkSTM 3 2) ≤ (-55760657337660 / 1000000000000000000000000 : ℝ) := by
  have e0 := xyBlkSTM_00
  have e1 := xyBlkSTM_11
  have e2 := xyBlkSTM_23
  have e3 := xyBlkSTM_32
  have p1 : (-53363394 / 1000000000000 : ℝ) ≤ (xyBlkSTM 0 0 * xyBlkSTM 1 1) ∧
      (xyBlkSTM 0 0 * xyBlkSTM 1 1) ≤ (-51914615 / 1000000000000 : ℝ) := by
    have hm := mul_nonneg_nonpos_bounds (by norm_num : (0 : ℝ) ≤ (2077 / 1000000 : ℝ)) (by norm_num : (-24995 / 1000000 : ℝ) ≤ (0 : ℝ)) e0.1 e0.2 e1.1 e1.2
    convert hm using 1 <;> norm_num
  have p2 : (176457776385 / 1000000000000000000 : ℝ) ≤ (xyBlkSTM 0 0 * xyBlkSTM 1 1 * xyBlkSTM 2 3) ∧
      (xyBlkSTM 0 0 * xyBlkSTM 1 1 * xyBlkSTM 2 3) ≤ (187465603122 / 1000000000000000000 : ℝ) := by
    have hm := mul_nonpos_nonpos_bounds (by norm_num : (-51914615 / 1000000000000 : ℝ) ≤ (0 : ℝ)) (by norm_num : (-3399 / 1000000 : ℝ) ≤ (0 : ℝ)) p1.1 p1.2 e2.1 e2.2
    convert hm using 1 <;> norm_num
  have p3 : (-71236929186360 / 1000000000000000000000000 : ℝ) ≤ (xyBlkSTM 0 0 * xyBlkSTM 1 1 * xyBlkSTM 2 3 * xyBlkSTM 3 2) ∧
      (xyBlkSTM 0 0 * xyBlkSTM 1 1 * xyBlkSTM 2 3 * xyBlkSTM 3 2) ≤ (-55760657337660 / 1000000000000000000000000 : ℝ) := by
    have hm := mul_nonneg_nonpos_bounds (by norm_num : (0 : ℝ) ≤ (176457776385 / 1000000000000000000 : ℝ)) (by norm_num : (-316 / 1000000 : ℝ) ≤ (0 : ℝ)) p2.1 p2.2 e3.1 e3.2
    convert hm using 1 <;> norm_num
  exact p3

lemma xyBlkSTM_prod_2 :
    (168039548116228880 / 1000000000000000000000000 : ℝ) ≤ (xyBlkSTM 0 0 * xyBlkSTM 1 2 * xyBlkSTM 2 1 * xyBlkSTM 3 3) ∧
      (xyBlkSTM 0 0 * xyBlkSTM 1 2 * xyBlkSTM 2 1 * xyBlkSTM 3 3) ≤ (173495868698882880 / 1000000000000000000000000 : ℝ) := by
  have e0 := xyBlkSTM_00
  have e1 := xyBlkSTM_12
  have e2 := xyBlkSTM_21
  have e3 := xyBlkSTM_33
  have p1 : (26190970 / 1000000000000 : ℝ) ≤ (xyBlkSTM 0 0 * xyBlkSTM 1 2) ∧
      (xyBlkSTM 0 0 * xyBlkSTM 1 2) ≤ (26990982 / 1000000000000 : ℝ) := by
    have hm := mul_nonneg_bounds (by norm_num : (0 : ℝ) ≤ (2077 / 1000000 : ℝ)) (by norm_num : (0 : ℝ) ≤ (12610 / 1000000 : ℝ)) e0.1 e0.2 e1.1 e1.2
    convert hm using 1 <;> norm_num
  have p2 : (-1801917958320 / 1000000000000000000 : ℝ) ≤ (xyBlkSTM 0 0 * xyBlkSTM 1 2 * xyBlkSTM 2 1) ∧
      (xyBlkSTM 0 0 * xyBlkSTM 1 2 * xyBlkSTM 2 1) ≤ (-1747644855190 / 1000000000000000000 : ℝ) := by
    have hm := mul_nonneg_nonpos_bounds (by norm_num : (0 : ℝ) ≤ (26190970 / 1000000000000 : ℝ)) (by norm_num : (-66727 / 1000000 : ℝ) ≤ (0 : ℝ)) p1.1 p1.2 e2.1 e2.2
    convert hm using 1 <;> norm_num
  have p3 : (168039548116228880 / 1000000000000000000000000 : ℝ) ≤ (xyBlkSTM 0 0 * xyBlkSTM 1 2 * xyBlkSTM 2 1 * xyBlkSTM 3 3) ∧
      (xyBlkSTM 0 0 * xyBlkSTM 1 2 * xyBlkSTM 2 1 * xyBlkSTM 3 3) ≤ (173495868698882880 / 1000000000000000000000000 : ℝ) := by
    have hm := mul_nonpos_nonpos_bounds (by norm_num : (-1747644855190 / 1000000000000000000 : ℝ) ≤ (0 : ℝ)) (by norm_num : (-96152 / 1000000 : ℝ) ≤ (0 : ℝ)) p2.1 p2.2 e3.1 e3.2
    convert hm using 1 <;> norm_num
  exact p3

lemma xyBlkSTM_prod_3 :
    (4137526945433310 / 1000000000000000000000000 : ℝ) ≤ (xyBlkSTM 0 0 * xyBlkSTM 1 2 * xyBlkSTM 2 3 * xyBlkSTM 3 1) ∧
      (xyBlkSTM 0 0 * xyBlkSTM 1 2 * xyBlkSTM 2 3 * xyBlkSTM 3 1) ≤ (4411089574834086 / 1000000000000000000000000 : ℝ) := by
  have e0 := xyBlkSTM_00
  have e1 := xyBlkSTM_12
  have e2 := xyBlkSTM_23
  have e3 := xyBlkSTM_31
  have p1 : (26190970 / 1000000000000 : ℝ) ≤ (xyBlkSTM 0 0 * xyBlkSTM 1 2) ∧
      (xyBlkSTM 0 0 * xyBlkSTM 1 2) ≤ (26990982 / 1000000000000 : ℝ) := by
    have hm := mul_nonneg_bounds (by norm_num : (0 : ℝ) ≤ (2077 / 1000000 : ℝ)) (by norm_num : (0 : ℝ) ≤ (12610 / 1000000 : ℝ)) e0.1 e0.2 e1.1 e1.2
    convert hm using 1 <;> norm_num
  have p2 : (-94819319766 / 1000000000000000000 : ℝ) ≤ (xyBlkSTM 0 0 * xyBlkSTM 1 2 * xyBlkSTM 2 3) ∧
      (xyBlkSTM 0 0 * xyBlkSTM 1 2 * xyBlkSTM 2 3) ≤ (-89023107030 / 1000000000000000000 : ℝ) := by
    have hm := mul_nonneg_nonpos_bounds (by norm_num : (0 : ℝ) ≤ (26190970 / 1000000000000 : ℝ)) (by norm_num : (-3399 / 1000000 : ℝ) ≤ (0 : ℝ)) p1.1 p1.2 e2.1 e2.2
    convert hm using 1 <;> norm_num
  have p3 : (4137526945433310 / 1000000000000000000000000 : ℝ) ≤ (xyBlkSTM 0 0 * xyBlkSTM 1 2 * xyBlkSTM 2 3 * xyBlkSTM 3 1) ∧
      (xyBlkSTM 0 0 * xyBlkSTM 1 2 * xyBlkSTM 2 3 * xyBlkSTM 3 1) ≤ (4411089574834086 / 1000000000000000000000000 : ℝ) := by
    have hm := mul_nonpos_nonpos_bounds (by norm_num : (-89023107030 / 1000000000000000000 : ℝ) ≤ (0 : ℝ)) (by norm_num : (-46477 / 1000000 : ℝ) ≤ (0 : ℝ)) p2.1 p2.2 e3.1 e3.2
    convert hm using 1 <;> norm_num
  exact p3

lemma xyBlkSTM_prod_4 :
    (-1049333124556800 / 1000000000000000000000000 : ℝ) ≤ (xyBlkSTM 0 0 * xyBlkSTM 1 3 * xyBlkSTM 2 1 * xyBlkSTM 3 2) ∧
      (xyBlkSTM 0 0 * xyBlkSTM 1 3 * xyBlkSTM 2 1 * xyBlkSTM 3 2) ≤ (-845551326982748 / 1000000000000000000000000 : ℝ) := by
  have e0 := xyBlkSTM_00
  have e1 := xyBlkSTM_13
  have e2 := xyBlkSTM_21
  have e3 := xyBlkSTM_32
  have p1 : (-41363136 / 1000000000000 : ℝ) ≤ (xyBlkSTM 0 0 * xyBlkSTM 1 3) ∧
      (xyBlkSTM 0 0 * xyBlkSTM 1 3) ≤ (-40100639 / 1000000000000 : ℝ) := by
    have hm := mul_nonneg_nonpos_bounds (by norm_num : (0 : ℝ) ≤ (2077 / 1000000 : ℝ)) (by norm_num : (-19307 / 1000000 : ℝ) ≤ (0 : ℝ)) e0.1 e0.2 e1.1 e1.2
    convert hm using 1 <;> norm_num
  have p2 : (2675795338553 / 1000000000000000000 : ℝ) ≤ (xyBlkSTM 0 0 * xyBlkSTM 1 3 * xyBlkSTM 2 1) ∧
      (xyBlkSTM 0 0 * xyBlkSTM 1 3 * xyBlkSTM 2 1) ≤ (2761402959360 / 1000000000000000000 : ℝ) := by
    have hm := mul_nonpos_nonpos_bounds (by norm_num : (-40100639 / 1000000000000 : ℝ) ≤ (0 : ℝ)) (by norm_num : (-66727 / 1000000 : ℝ) ≤ (0 : ℝ)) p1.1 p1.2 e2.1 e2.2
    convert hm using 1 <;> norm_num
  have p3 : (-1049333124556800 / 1000000000000000000000000 : ℝ) ≤ (xyBlkSTM 0 0 * xyBlkSTM 1 3 * xyBlkSTM 2 1 * xyBlkSTM 3 2) ∧
      (xyBlkSTM 0 0 * xyBlkSTM 1 3 * xyBlkSTM 2 1 * xyBlkSTM 3 2) ≤ (-845551326982748 / 1000000000000000000000000 : ℝ) := by
    have hm := mul_nonneg_nonpos_bounds (by norm_num : (0 : ℝ) ≤ (2675795338553 / 1000000000000000000 : ℝ)) (by norm_num : (-316 / 1000000 : ℝ) ≤ (0 : ℝ)) p2.1 p2.2 e3.1 e3.2
    convert hm using 1 <;> norm_num
  exact p3

lemma xyBlkSTM_prod_5 :
    (1220761096215965 / 1000000000000000000000000 : ℝ) ≤ (xyBlkSTM 0 0 * xyBlkSTM 1 3 * xyBlkSTM 2 2 * xyBlkSTM 3 1) ∧
      (xyBlkSTM 0 0 * xyBlkSTM 1 3 * xyBlkSTM 2 2 * xyBlkSTM 3 1) ≤ (1560570358833216 / 1000000000000000000000000 : ℝ) := by
  have e0 := xyBlkSTM_00
  have e1 := xyBlkSTM_13
  have e2 := xyBlkSTM_22
  have e3 := xyBlkSTM_31
  have p1 : (-41363136 / 1000000000000 : ℝ) ≤ (xyBlkSTM 0 0 * xyBlkSTM 1 3) ∧
      (xyBlkSTM 0 0 * xyBlkSTM 1 3) ≤ (-40100639 / 1000000000000 : ℝ) := by
    have hm := mul_nonneg_nonpos_bounds (by norm_num : (0 : ℝ) ≤ (2077 / 1000000 : ℝ)) (by norm_num : (-19307 / 1000000 : ℝ) ≤ (0 : ℝ)) e0.1 e0.2 e1.1 e1.2
    convert hm using 1 <;> norm_num
  have p2 : (-33545503296 / 1000000000000000000 : ℝ) ≤ (xyBlkSTM 0 0 * xyBlkSTM 1 3 * xyBlkSTM 2 2) ∧
      (xyBlkSTM 0 0 * xyBlkSTM 1 3 * xyBlkSTM 2 2) ≤ (-26265918545 / 1000000000000000000 : ℝ) := by
    have hm := mul_nonpos_nonneg_bounds (by norm_num : (-40100639 / 1000000000000 : ℝ) ≤ (0 : ℝ)) (by norm_num : (0 : ℝ) ≤ (655 / 1000000 : ℝ)) p1.1 p1.2 e2.1 e2.2
    convert hm using 1 <;> norm_num
  have p3 : (1220761096215965 / 1000000000000000000000000 : ℝ) ≤ (xyBlkSTM 0 0 * xyBlkSTM 1 3 * xyBlkSTM 2 2 * xyBlkSTM 3 1) ∧
      (xyBlkSTM 0 0 * xyBlkSTM 1 3 * xyBlkSTM 2 2 * xyBlkSTM 3 1) ≤ (1560570358833216 / 1000000000000000000000000 : ℝ) := by
    have hm := mul_nonpos_nonpos_bounds (by norm_num : (-26265918545 / 1000000000000000000 : ℝ) ≤ (0 : ℝ)) (by norm_num : (-46477 / 1000000 : ℝ) ≤ (0 : ℝ)) p2.1 p2.2 e3.1 e3.2
    convert hm using 1 <;> norm_num
  exact p3

lemma xyBlkSTM_prod_6 :
    (-13334559169530304 / 1000000000000000000000000 : ℝ) ≤ (xyBlkSTM 0 1 * xyBlkSTM 1 0 * xyBlkSTM 2 2 * xyBlkSTM 3 3) ∧
      (xyBlkSTM 0 1 * xyBlkSTM 1 0 * xyBlkSTM 2 2 * xyBlkSTM 3 3) ≤ (-10710565590692240 / 1000000000000000000000000 : ℝ) := by
  have e0 := xyBlkSTM_01
  have e1 := xyBlkSTM_10
  have e2 := xyBlkSTM_22
  have e3 := xyBlkSTM_33
  have p1 : (170064154 / 1000000000000 : ℝ) ≤ (xyBlkSTM 0 1 * xyBlkSTM 1 0) ∧
      (xyBlkSTM 0 1 * xyBlkSTM 1 0) ≤ (170766896 / 1000000000000 : ℝ) := by
    have hm := mul_nonpos_nonpos_bounds (by norm_num : (-13814 / 1000000 : ℝ) ≤ (0 : ℝ)) (by norm_num : (-12311 / 1000000 : ℝ) ≤ (0 : ℝ)) e0.1 e0.2 e1.1 e1.2
    convert hm using 1 <;> norm_num
  have p2 : (111392020870 / 1000000000000000000 : ℝ) ≤ (xyBlkSTM 0 1 * xyBlkSTM 1 0 * xyBlkSTM 2 2) ∧
      (xyBlkSTM 0 1 * xyBlkSTM 1 0 * xyBlkSTM 2 2) ≤ (138491952656 / 1000000000000000000 : ℝ) := by
    have hm := mul_nonneg_bounds (by norm_num : (0 : ℝ) ≤ (170064154 / 1000000000000 : ℝ)) (by norm_num : (0 : ℝ) ≤ (655 / 1000000 : ℝ)) p1.1 p1.2 e2.1 e2.2
    convert hm using 1 <;> norm_num
  have p3 : (-13334559169530304 / 1000000000000000000000000 : ℝ) ≤ (xyBlkSTM 0 1 * xyBlkSTM 1 0 * xyBlkSTM 2 2 * xyBlkSTM 3 3) ∧
      (xyBlkSTM 0 1 * xyBlkSTM 1 0 * xyBlkSTM 2 2 * xyBlkSTM 3 3) ≤ (-10710565590692240 / 1000000000000000000000000 : ℝ) := by
    have hm := mul_nonneg_nonpos_bounds (by norm_num : (0 : ℝ) ≤ (111392020870 / 1000000000000000000 : ℝ)) (by norm_num : (-96152 / 1000000 : ℝ) ≤ (0 : ℝ)) p2.1 p2.2 e3.1 e3.2
    convert hm using 1 <;> norm_num
  exact p3

lemma xyBlkSTM_prod_7 :
    (182663186784936 / 1000000000000000000000000 : ℝ) ≤ (xyBlkSTM 0 1 * xyBlkSTM 1 0 * xyBlkSTM 2 3 * xyBlkSTM 3 2) ∧
      (xyBlkSTM 0 1 * xyBlkSTM 1 0 * xyBlkSTM 2 3 * xyBlkSTM 3 2) ≤ (227963560146240 / 1000000000000000000000000 : ℝ) := by
  have e0 := xyBlkSTM_01
  have e1 := xyBlkSTM_10
  have e2 := xyBlkSTM_23
  have e3 := xyBlkSTM_32
  have p1 : (170064154 / 1000000000000 : ℝ) ≤ (xyBlkSTM 0 1 * xyBlkSTM 1 0) ∧
      (xyBlkSTM 0 1 * xyBlkSTM 1 0) ≤ (170766896 / 1000000000000 : ℝ) := by
    have hm := mul_nonpos_nonpos_bounds (by norm_num : (-13814 / 1000000 : ℝ) ≤ (0 : ℝ)) (by norm_num : (-12311 / 1000000 : ℝ) ≤ (0 : ℝ)) e0.1 e0.2 e1.1 e1.2
    convert hm using 1 <;> norm_num
  have p2 : (-599904105648 / 1000000000000000000 : ℝ) ≤ (xyBlkSTM 0 1 * xyBlkSTM 1 0 * xyBlkSTM 2 3) ∧
      (xyBlkSTM 0 1 * xyBlkSTM 1 0 * xyBlkSTM 2 3) ≤ (-578048059446 / 1000000000000000000 : ℝ) := by
    have hm := mul_nonneg_nonpos_bounds (by norm_num : (0 : ℝ) ≤ (170064154 / 1000000000000 : ℝ)) (by norm_num : (-3399 / 1000000 : ℝ) ≤ (0 : ℝ)) p1.1 p1.2 e2.1 e2.2
    convert hm using 1 <;> norm_num
  have p3 : (182663186784936 / 1000000000000000000000000 : ℝ) ≤ (xyBlkSTM 0 1 * xyBlkSTM 1 0 * xyBlkSTM 2 3 * xyBlkSTM 3 2) ∧
      (xyBlkSTM 0 1 * xyBlkSTM 1 0 * xyBlkSTM 2 3 * xyBlkSTM 3 2) ≤ (227963560146240 / 1000000000000000000000000 : ℝ) := by
    have hm := mul_nonpos_nonpos_bounds (by norm_num : (-578048059446 / 1000000000000000000 : ℝ) ≤ (0 : ℝ)) (by norm_num : (-316 / 1000000 : ℝ) ≤ (0 : ℝ)) p2.1 p2.2 e3.1 e3.2
    convert hm using 1 <;> norm_num
  exact p3

lemma xyBlkSTM_prod_8 :
    (-92736416874231648 / 1000000000000000000000000 : ℝ) ≤ (xyBlkSTM 0 1 * xyBlkSTM 1 2 * xyBlkSTM 2 0 * xyBlkSTM 3 3) ∧
      (xyBlkSTM 0 1 * xyBlkSTM 1 2 * xyBlkSTM 2 0 * xyBlkSTM 3 3) ≤ (-89892706351899360 / 1000000000000000000000000 : ℝ) := by
  have e0 := xyBlkSTM_01
  have e1 := xyBlkSTM_12
  have e2 := xyBlkSTM_20
  have e3 := xyBlkSTM_33
  have p1 : (-175055436 / 1000000000000 : ℝ) ≤ (xyBlkSTM 0 1 * xyBlkSTM 1 2) ∧
      (xyBlkSTM 0 1 * xyBlkSTM 1 2) ≤ (-174194540 / 1000000000000 : ℝ) := by
    have hm := mul_nonpos_nonneg_bounds (by norm_num : (-13814 / 1000000 : ℝ) ≤ (0 : ℝ)) (by norm_num : (0 : ℝ) ≤ (12610 / 1000000 : ℝ)) e0.1 e0.2 e1.1 e1.2
    convert hm using 1 <;> norm_num
  have p2 : (934902096180 / 1000000000000000000 : ℝ) ≤ (xyBlkSTM 0 1 * xyBlkSTM 1 2 * xyBlkSTM 2 0) ∧
      (xyBlkSTM 0 1 * xyBlkSTM 1 2 * xyBlkSTM 2 0) ≤ (963155008872 / 1000000000000000000 : ℝ) := by
    have hm := mul_nonpos_nonpos_bounds (by norm_num : (-174194540 / 1000000000000 : ℝ) ≤ (0 : ℝ)) (by norm_num : (-5367 / 1000000 : ℝ) ≤ (0 : ℝ)) p1.1 p1.2 e2.1 e2.2
    convert hm using 1 <;> norm_num
  have p3 : (-92736416874231648 / 1000000000000000000000000 : ℝ) ≤ (xyBlkSTM 0 1 * xyBlkSTM 1 2 * xyBlkSTM 2 0 * xyBlkSTM 3 3) ∧
      (xyBlkSTM 0 1 * xyBlkSTM 1 2 * xyBlkSTM 2 0 * xyBlkSTM 3 3) ≤ (-89892706351899360 / 1000000000000000000000000 : ℝ) := by
    have hm := mul_nonneg_nonpos_bounds (by norm_num : (0 : ℝ) ≤ (934902096180 / 1000000000000000000 : ℝ)) (by norm_num : (-96152 / 1000000 : ℝ) ≤ (0 : ℝ)) p2.1 p2.2 e3.1 e3.2
    convert hm using 1 <;> norm_num
  exact p3

lemma xyBlkSTM_prod_9 :
    (-37618314373428228 / 1000000000000000000000000 : ℝ) ≤ (xyBlkSTM 0 1 * xyBlkSTM 1 2 * xyBlkSTM 2 3 * xyBlkSTM 3 0) ∧
      (xyBlkSTM 0 1 * xyBlkSTM 1 2 * xyBlkSTM 2 3 * xyBlkSTM 3 0) ≤ (-36189556372518120 / 1000000000000000000000000 : ℝ) := by
  have e0 := xyBlkSTM_01
  have e1 := xyBlkSTM_12
  have e2 := xyBlkSTM_23
  have e3 := xyBlkSTM_30
  have p1 : (-175055436 / 1000000000000 : ℝ) ≤ (xyBlkSTM 0 1 * xyBlkSTM 1 2) ∧
      (xyBlkSTM 0 1 * xyBlkSTM 1 2) ≤ (-174194540 / 1000000000000 : ℝ) := by
    have hm := mul_nonpos_nonneg_bounds (by norm_num : (-13814 / 1000000 : ℝ) ≤ (0 : ℝ)) (by norm_num : (0 : ℝ) ≤ (12610 / 1000000 : ℝ)) e0.1 e0.2 e1.1 e1.2
    convert hm using 1 <;> norm_num
  have p2 : (592087241460 / 1000000000000000000 : ℝ) ≤ (xyBlkSTM 0 1 * xyBlkSTM 1 2 * xyBlkSTM 2 3) ∧
      (xyBlkSTM 0 1 * xyBlkSTM 1 2 * xyBlkSTM 2 3) ≤ (614969746668 / 1000000000000000000 : ℝ) := by
    have hm := mul_nonpos_nonpos_bounds (by norm_num : (-174194540 / 1000000000000 : ℝ) ≤ (0 : ℝ)) (by norm_num : (-3399 / 1000000 : ℝ) ≤ (0 : ℝ)) p1.1 p1.2 e2.1 e2.2
    convert hm using 1 <;> norm_num
  have p3 : (-37618314373428228 / 1000000000000000000000000 : ℝ) ≤ (xyBlkSTM 0 1 * xyBlkSTM 1 2 * xyBlkSTM 2 3 * xyBlkSTM 3 0) ∧
      (xyBlkSTM 0 1 * xyBlkSTM 1 2 * xyBlkSTM 2 3 * xyBlkSTM 3 0) ≤ (-36189556372518120 / 1000000000000000000000000 : ℝ) := by
    have hm := mul_nonneg_nonpos_bounds (by norm_num : (0 : ℝ) ≤ (592087241460 / 1000000000000000000 : ℝ)) (by norm_num : (-61122 / 1000000 : ℝ) ≤ (0 : ℝ)) p2.1 p2.2 e3.1 e3.2
    convert hm using 1 <;> norm_num
  exact p3

lemma xyBlkSTM_prod_10 :
    (452327431214856 / 1000000000000000000000000 : ℝ) ≤ (xyBlkSTM 0 1 * xyBlkSTM 1 3 * xyBlkSTM 2 0 * xyBlkSTM 3 2) ∧
      (xyBlkSTM 0 1 * xyBlkSTM 1 3 * xyBlkSTM 2 0 * xyBlkSTM 3 2) ≤ (560885943905280 / 1000000000000000000000000 : ℝ) := by
  have e0 := xyBlkSTM_01
  have e1 := xyBlkSTM_13
  have e2 := xyBlkSTM_20
  have e3 := xyBlkSTM_32
  have p1 : (266706898 / 1000000000000 : ℝ) ≤ (xyBlkSTM 0 1 * xyBlkSTM 1 3) ∧
      (xyBlkSTM 0 1 * xyBlkSTM 1 3) ≤ (268268928 / 1000000000000 : ℝ) := by
    have hm := mul_nonpos_nonpos_bounds (by norm_num : (-13814 / 1000000 : ℝ) ≤ (0 : ℝ)) (by norm_num : (-19307 / 1000000 : ℝ) ≤ (0 : ℝ)) e0.1 e0.2 e1.1 e1.2
    convert hm using 1 <;> norm_num
  have p2 : (-1476015641856 / 1000000000000000000 : ℝ) ≤ (xyBlkSTM 0 1 * xyBlkSTM 1 3 * xyBlkSTM 2 0) ∧
      (xyBlkSTM 0 1 * xyBlkSTM 1 3 * xyBlkSTM 2 0) ≤ (-1431415921566 / 1000000000000000000 : ℝ) := by
    have hm := mul_nonneg_nonpos_bounds (by norm_num : (0 : ℝ) ≤ (266706898 / 1000000000000 : ℝ)) (by norm_num : (-5367 / 1000000 : ℝ) ≤ (0 : ℝ)) p1.1 p1.2 e2.1 e2.2
    convert hm using 1 <;> norm_num
  have p3 : (452327431214856 / 1000000000000000000000000 : ℝ) ≤ (xyBlkSTM 0 1 * xyBlkSTM 1 3 * xyBlkSTM 2 0 * xyBlkSTM 3 2) ∧
      (xyBlkSTM 0 1 * xyBlkSTM 1 3 * xyBlkSTM 2 0 * xyBlkSTM 3 2) ≤ (560885943905280 / 1000000000000000000000000 : ℝ) := by
    have hm := mul_nonpos_nonpos_bounds (by norm_num : (-1431415921566 / 1000000000000000000 : ℝ) ≤ (0 : ℝ)) (by norm_num : (-316 / 1000000 : ℝ) ≤ (0 : ℝ)) p2.1 p2.2 e3.1 e3.2
    convert hm using 1 <;> norm_num
  exact p3

lemma xyBlkSTM_prod_11 :
    (-13308735940291968 / 1000000000000000000000000 : ℝ) ≤ (xyBlkSTM 0 1 * xyBlkSTM 1 3 * xyBlkSTM 2 2 * xyBlkSTM 3 0) ∧
      (xyBlkSTM 0 1 * xyBlkSTM 1 3 * xyBlkSTM 2 2 * xyBlkSTM 3 0) ≤ (-10677586657809180 / 1000000000000000000000000 : ℝ) := by
  have e0 := xyBlkSTM_01
  have e1 := xyBlkSTM_13
  have e2 := xyBlkSTM_22
  have e3 := xyBlkSTM_30
  have p1 : (266706898 / 1000000000000 : ℝ) ≤ (xyBlkSTM 0 1 * xyBlkSTM 1 3) ∧
      (xyBlkSTM 0 1 * xyBlkSTM 1 3) ≤ (268268928 / 1000000000000 : ℝ) := by
    have hm := mul_nonpos_nonpos_bounds (by norm_num : (-13814 / 1000000 : ℝ) ≤ (0 : ℝ)) (by norm_num : (-19307 / 1000000 : ℝ) ≤ (0 : ℝ)) e0.1 e0.2 e1.1 e1.2
    convert hm using 1 <;> norm_num
  have p2 : (174693018190 / 1000000000000000000 : ℝ) ≤ (xyBlkSTM 0 1 * xyBlkSTM 1 3 * xyBlkSTM 2 2) ∧
      (xyBlkSTM 0 1 * xyBlkSTM 1 3 * xyBlkSTM 2 2) ≤ (217566100608 / 1000000000000000000 : ℝ) := by
    have hm := mul_nonneg_bounds (by norm_num : (0 : ℝ) ≤ (266706898 / 1000000000000 : ℝ)) (by norm_num : (0 : ℝ) ≤ (655 / 1000000 : ℝ)) p1.1 p1.2 e2.1 e2.2
    convert hm using 1 <;> norm_num
  have p3 : (-13308735940291968 / 1000000000000000000000000 : ℝ) ≤ (xyBlkSTM 0 1 * xyBlkSTM 1 3 * xyBlkSTM 2 2 * xyBlkSTM 3 0) ∧
      (xyBlkSTM 0 1 * xyBlkSTM 1 3 * xyBlkSTM 2 2 * xyBlkSTM 3 0) ≤ (-10677586657809180 / 1000000000000000000000000 : ℝ) := by
    have hm := mul_nonneg_nonpos_bounds (by norm_num : (0 : ℝ) ≤ (174693018190 / 1000000000000000000 : ℝ)) (by norm_num : (-61122 / 1000000 : ℝ) ≤ (0 : ℝ)) p2.1 p2.2 e3.1 e3.2
    convert hm using 1 <;> norm_num
  exact p3

lemma xyBlkSTM_prod_12 :
    (-171625922538228480 / 1000000000000000000000000 : ℝ) ≤ (xyBlkSTM 0 2 * xyBlkSTM 1 0 * xyBlkSTM 2 1 * xyBlkSTM 3 3) ∧
      (xyBlkSTM 0 2 * xyBlkSTM 1 0 * xyBlkSTM 2 1 * xyBlkSTM 3 3) ≤ (-165713823186004912 / 1000000000000000000000000 : ℝ) := by
  have e0 := xyBlkSTM_02
  have e1 := xyBlkSTM_10
  have e2 := xyBlkSTM_21
  have e3 := xyBlkSTM_33
  have p1 : (-26700072 / 1000000000000 : ℝ) ≤ (xyBlkSTM 0 2 * xyBlkSTM 1 0) ∧
      (xyBlkSTM 0 2 * xyBlkSTM 1 0) ≤ (-25828478 / 1000000000000 : ℝ) := by
    have hm := mul_nonneg_nonpos_bounds (by norm_num : (0 : ℝ) ≤ (2098 / 1000000 : ℝ)) (by norm_num : (-12311 / 1000000 : ℝ) ≤ (0 : ℝ)) e0.1 e0.2 e1.1 e1.2
    convert hm using 1 <;> norm_num
  have p2 : (1723456851506 / 1000000000000000000 : ℝ) ≤ (xyBlkSTM 0 2 * xyBlkSTM 1 0 * xyBlkSTM 2 1) ∧
      (xyBlkSTM 0 2 * xyBlkSTM 1 0 * xyBlkSTM 2 1) ≤ (1782496806720 / 1000000000000000000 : ℝ) := by
    have hm := mul_nonpos_nonpos_bounds (by norm_num : (-25828478 / 1000000000000 : ℝ) ≤ (0 : ℝ)) (by norm_num : (-66727 / 1000000 : ℝ) ≤ (0 : ℝ)) p1.1 p1.2 e2.1 e2.2
    convert hm using 1 <;> norm_num
  have p3 : (-171625922538228480 / 1000000000000000000000000 : ℝ) ≤ (xyBlkSTM 0 2 * xyBlkSTM 1 0 * xyBlkSTM 2 1 * xyBlkSTM 3 3) ∧
      (xyBlkSTM 0 2 * xyBlkSTM 1 0 * xyBlkSTM 2 1 * xyBlkSTM 3 3) ≤ (-165713823186004912 / 1000000000000000000000000 : ℝ) := by
    have hm := mul_nonneg_nonpos_bounds (by norm_num : (0 : ℝ) ≤ (1723456851506 / 1000000000000000000 : ℝ)) (by norm_num : (-96152 / 1000000 : ℝ) ≤ (0 : ℝ)) p2.1 p2.2 e3.1 e3.2
    convert hm using 1 <;> norm_num
  exact p3

lemma xyBlkSTM_prod_13 :
    (-4363546655935656 / 1000000000000000000000000 : ℝ) ≤ (xyBlkSTM 0 2 * xyBlkSTM 1 0 * xyBlkSTM 2 3 * xyBlkSTM 3 1) ∧
      (xyBlkSTM 0 2 * xyBlkSTM 1 0 * xyBlkSTM 2 3 * xyBlkSTM 3 1) ≤ (-4080262154648394 / 1000000000000000000000000 : ℝ) := by
  have e0 := xyBlkSTM_02
  have e1 := xyBlkSTM_10
  have e2 := xyBlkSTM_23
  have e3 := xyBlkSTM_31
  have p1 : (-26700072 / 1000000000000 : ℝ) ≤ (xyBlkSTM 0 2 * xyBlkSTM 1 0) ∧
      (xyBlkSTM 0 2 * xyBlkSTM 1 0) ≤ (-25828478 / 1000000000000 : ℝ) := by
    have hm := mul_nonneg_nonpos_bounds (by norm_num : (0 : ℝ) ≤ (2098 / 1000000 : ℝ)) (by norm_num : (-12311 / 1000000 : ℝ) ≤ (0 : ℝ)) e0.1 e0.2 e1.1 e1.2
    convert hm using 1 <;> norm_num
  have p2 : (87790996722 / 1000000000000000000 : ℝ) ≤ (xyBlkSTM 0 2 * xyBlkSTM 1 0 * xyBlkSTM 2 3) ∧
      (xyBlkSTM 0 2 * xyBlkSTM 1 0 * xyBlkSTM 2 3) ≤ (93797352936 / 1000000000000000000 : ℝ) := by
    have hm := mul_nonpos_nonpos_bounds (by norm_num : (-25828478 / 1000000000000 : ℝ) ≤ (0 : ℝ)) (by norm_num : (-3399 / 1000000 : ℝ) ≤ (0 : ℝ)) p1.1 p1.2 e2.1 e2.2
    convert hm using 1 <;> norm_num
  have p3 : (-4363546655935656 / 1000000000000000000000000 : ℝ) ≤ (xyBlkSTM 0 2 * xyBlkSTM 1 0 * xyBlkSTM 2 3 * xyBlkSTM 3 1) ∧
      (xyBlkSTM 0 2 * xyBlkSTM 1 0 * xyBlkSTM 2 3 * xyBlkSTM 3 1) ≤ (-4080262154648394 / 1000000000000000000000000 : ℝ) := by
    have hm := mul_nonneg_nonpos_bounds (by norm_num : (0 : ℝ) ≤ (87790996722 / 1000000000000000000 : ℝ)) (by norm_num : (-46477 / 1000000 : ℝ) ≤ (0 : ℝ)) p2.1 p2.2 e3.1 e3.2
    convert hm using 1 <;> norm_num
  exact p3

lemma xyBlkSTM_prod_14 :
    (-28667103728950512 / 1000000000000000000000000 : ℝ) ≤ (xyBlkSTM 0 2 * xyBlkSTM 1 1 * xyBlkSTM 2 0 * xyBlkSTM 3 3) ∧
      (xyBlkSTM 0 2 * xyBlkSTM 1 1 * xyBlkSTM 2 0 * xyBlkSTM 3 3) ≤ (-27061292929545840 / 1000000000000000000000000 : ℝ) := by
  have e0 := xyBlkSTM_02
  have e1 := xyBlkSTM_11
  have e2 := xyBlkSTM_20
  have e3 := xyBlkSTM_33
  have p1 : (-54113934 / 1000000000000 : ℝ) ≤ (xyBlkSTM 0 2 * xyBlkSTM 1 1) ∧
      (xyBlkSTM 0 2 * xyBlkSTM 1 1) ≤ (-52439510 / 1000000000000 : ℝ) := by
    have hm := mul_nonneg_nonpos_bounds (by norm_num : (0 : ℝ) ≤ (2098 / 1000000 : ℝ)) (by norm_num : (-24995 / 1000000 : ℝ) ≤ (0 : ℝ)) e0.1 e0.2 e1.1 e1.2
    convert hm using 1 <;> norm_num
  have p2 : (281442850170 / 1000000000000000000 : ℝ) ≤ (xyBlkSTM 0 2 * xyBlkSTM 1 1 * xyBlkSTM 2 0) ∧
      (xyBlkSTM 0 2 * xyBlkSTM 1 1 * xyBlkSTM 2 0) ≤ (297734864868 / 1000000000000000000 : ℝ) := by
    have hm := mul_nonpos_nonpos_bounds (by norm_num : (-52439510 / 1000000000000 : ℝ) ≤ (0 : ℝ)) (by norm_num : (-5367 / 1000000 : ℝ) ≤ (0 : ℝ)) p1.1 p1.2 e2.1 e2.2
    convert hm using 1 <;> norm_num
  have p3 : (-28667103728950512 / 1000000000000000000000000 : ℝ) ≤ (xyBlkSTM 0 2 * xyBlkSTM 1 1 * xyBlkSTM 2 0 * xyBlkSTM 3 3) ∧
      (xyBlkSTM 0 2 * xyBlkSTM 1 1 * xyBlkSTM 2 0 * xyBlkSTM 3 3) ≤ (-27061292929545840 / 1000000000000000000000000 : ℝ) := by
    have hm := mul_nonneg_nonpos_bounds (by norm_num : (0 : ℝ) ≤ (281442850170 / 1000000000000000000 : ℝ)) (by norm_num : (-96152 / 1000000 : ℝ) ≤ (0 : ℝ)) p2.1 p2.2 e3.1 e3.2
    convert hm using 1 <;> norm_num
  exact p3

lemma xyBlkSTM_prod_15 :
    (-11628744743436282 / 1000000000000000000000000 : ℝ) ≤ (xyBlkSTM 0 2 * xyBlkSTM 1 1 * xyBlkSTM 2 3 * xyBlkSTM 3 0) ∧
      (xyBlkSTM 0 2 * xyBlkSTM 1 1 * xyBlkSTM 2 3 * xyBlkSTM 3 0) ≤ (-10894501075017780 / 1000000000000000000000000 : ℝ) := by
  have e0 := xyBlkSTM_02
  have e1 := xyBlkSTM_11
  have e2 := xyBlkSTM_23
  have e3 := xyBlkSTM_30
  have p1 : (-54113934 / 1000000000000 : ℝ) ≤ (xyBlkSTM 0 2 * xyBlkSTM 1 1) ∧
      (xyBlkSTM 0 2 * xyBlkSTM 1 1) ≤ (-52439510 / 1000000000000 : ℝ) := by
    have hm := mul_nonneg_nonpos_bounds (by norm_num : (0 : ℝ) ≤ (2098 / 1000000 : ℝ)) (by norm_num : (-24995 / 1000000 : ℝ) ≤ (0 : ℝ)) e0.1 e0.2 e1.1 e1.2
    convert hm using 1 <;> norm_num
  have p2 : (178241894490 / 1000000000000000000 : ℝ) ≤ (xyBlkSTM 0 2 * xyBlkSTM 1 1 * xyBlkSTM 2 3) ∧
      (xyBlkSTM 0 2 * xyBlkSTM 1 1 * xyBlkSTM 2 3) ≤ (190102250142 / 1000000000000000000 : ℝ) := by
    have hm := mul_nonpos_nonpos_bounds (by norm_num : (-52439510 / 1000000000000 : ℝ) ≤ (0 : ℝ)) (by norm_num : (-3399 / 1000000 : ℝ) ≤ (0 : ℝ)) p1.1 p1.2 e2.1 e2.2
    convert hm using 1 <;> norm_num
  have p3 : (-11628744743436282 / 1000000000000000000000000 : ℝ) ≤ (xyBlkSTM 0 2 * xyBlkSTM 1 1 * xyBlkSTM 2 3 * xyBlkSTM 3 0) ∧
      (xyBlkSTM 0 2 * xyBlkSTM 1 1 * xyBlkSTM 2 3 * xyBlkSTM 3 0) ≤ (-10894501075017780 / 1000000000000000000000000 : ℝ) := by
    have hm := mul_nonneg_nonpos_bounds (by norm_num : (0 : ℝ) ≤ (178241894490 / 1000000000000000000 : ℝ)) (by norm_num : (-61122 / 1000000 : ℝ) ≤ (0 : ℝ)) p2.1 p2.2 e3.1 e3.2
    convert hm using 1 <;> norm_num
  exact p3

lemma xyBlkSTM_prod_16 :
    (-10736154424501632 / 1000000000000000000000000 : ℝ) ≤ (xyBlkSTM 0 2 * xyBlkSTM 1 3 * xyBlkSTM 2 0 * xyBlkSTM 3 1) ∧
      (xyBlkSTM 0 2 * xyBlkSTM 1 3 * xyBlkSTM 2 0 * xyBlkSTM 3 1) ≤ (-10103921493871074 / 1000000000000000000000000 : ℝ) := by
  have e0 := xyBlkSTM_02
  have e1 := xyBlkSTM_13
  have e2 := xyBlkSTM_20
  have e3 := xyBlkSTM_31
  have p1 : (-41944896 / 1000000000000 : ℝ) ≤ (xyBlkSTM 0 2 * xyBlkSTM 1 3) ∧
      (xyBlkSTM 0 2 * xyBlkSTM 1 3) ≤ (-40506086 / 1000000000000 : ℝ) := by
    have hm := mul_nonneg_nonpos_bounds (by norm_num : (0 : ℝ) ≤ (2098 / 1000000 : ℝ)) (by norm_num : (-19307 / 1000000 : ℝ) ≤ (0 : ℝ)) e0.1 e0.2 e1.1 e1.2
    convert hm using 1 <;> norm_num
  have p2 : (217396163562 / 1000000000000000000 : ℝ) ≤ (xyBlkSTM 0 2 * xyBlkSTM 1 3 * xyBlkSTM 2 0) ∧
      (xyBlkSTM 0 2 * xyBlkSTM 1 3 * xyBlkSTM 2 0) ≤ (230780817792 / 1000000000000000000 : ℝ) := by
    have hm := mul_nonpos_nonpos_bounds (by norm_num : (-40506086 / 1000000000000 : ℝ) ≤ (0 : ℝ)) (by norm_num : (-5367 / 1000000 : ℝ) ≤ (0 : ℝ)) p1.1 p1.2 e2.1 e2.2
    convert hm using 1 <;> norm_num
  have p3 : (-10736154424501632 / 1000000000000000000000000 : ℝ) ≤ (xyBlkSTM 0 2 * xyBlkSTM 1 3 * xyBlkSTM 2 0 * xyBlkSTM 3 1) ∧
      (xyBlkSTM 0 2 * xyBlkSTM 1 3 * xyBlkSTM 2 0 * xyBlkSTM 3 1) ≤ (-10103921493871074 / 1000000000000000000000000 : ℝ) := by
    have hm := mul_nonneg_nonpos_bounds (by norm_num : (0 : ℝ) ≤ (217396163562 / 1000000000000000000 : ℝ)) (by norm_num : (-46477 / 1000000 : ℝ) ≤ (0 : ℝ)) p2.1 p2.2 e3.1 e3.2
    convert hm using 1 <;> norm_num
  exact p3

lemma xyBlkSTM_prod_17 :
    (-171293557929500160 / 1000000000000000000000000 : ℝ) ≤ (xyBlkSTM 0 2 * xyBlkSTM 1 3 * xyBlkSTM 2 1 * xyBlkSTM 3 0) ∧
      (xyBlkSTM 0 2 * xyBlkSTM 1 3 * xyBlkSTM 2 1 * xyBlkSTM 3 0) ≤ (-165203573283105684 / 1000000000000000000000000 : ℝ) := by
  have e0 := xyBlkSTM_02
  have e1 := xyBlkSTM_13
  have e2 := xyBlkSTM_21
  have e3 := xyBlkSTM_30
  have p1 : (-41944896 / 1000000000000 : ℝ) ≤ (xyBlkSTM 0 2 * xyBlkSTM 1 3) ∧
      (xyBlkSTM 0 2 * xyBlkSTM 1 3) ≤ (-40506086 / 1000000000000 : ℝ) := by
    have hm := mul_nonneg_nonpos_bounds (by norm_num : (0 : ℝ) ≤ (2098 / 1000000 : ℝ)) (by norm_num : (-19307 / 1000000 : ℝ) ≤ (0 : ℝ)) e0.1 e0.2 e1.1 e1.2
    convert hm using 1 <;> norm_num
  have p2 : (2702849600522 / 1000000000000000000 : ℝ) ≤ (xyBlkSTM 0 2 * xyBlkSTM 1 3 * xyBlkSTM 2 1) ∧
      (xyBlkSTM 0 2 * xyBlkSTM 1 3 * xyBlkSTM 2 1) ≤ (2800241256960 / 1000000000000000000 : ℝ) := by
    have hm := mul_nonpos_nonpos_bounds (by norm_num : (-40506086 / 1000000000000 : ℝ) ≤ (0 : ℝ)) (by norm_num : (-66727 / 1000000 : ℝ) ≤ (0 : ℝ)) p1.1 p1.2 e2.1 e2.2
    convert hm using 1 <;> norm_num
  have p3 : (-171293557929500160 / 1000000000000000000000000 : ℝ) ≤ (xyBlkSTM 0 2 * xyBlkSTM 1 3 * xyBlkSTM 2 1 * xyBlkSTM 3 0) ∧
      (xyBlkSTM 0 2 * xyBlkSTM 1 3 * xyBlkSTM 2 1 * xyBlkSTM 3 0) ≤ (-165203573283105684 / 1000000000000000000000000 : ℝ) := by
    have hm := mul_nonneg_nonpos_bounds (by norm_num : (0 : ℝ) ≤ (2702849600522 / 1000000000000000000 : ℝ)) (by norm_num : (-61122 / 1000000 : ℝ) ≤ (0 : ℝ)) p2.1 p2.2 e3.1 e3.2
    convert hm using 1 <;> norm_num
  exact p3

lemma xyBlkSTM_prod_18 :
    (-3860230463174400 / 1000000000000000000000000 : ℝ) ≤ (xyBlkSTM 0 3 * xyBlkSTM 1 0 * xyBlkSTM 2 1 * xyBlkSTM 3 2) ∧
      (xyBlkSTM 0 3 * xyBlkSTM 1 0 * xyBlkSTM 2 1 * xyBlkSTM 3 2) ≤ (-3177597693467132 / 1000000000000000000000000 : ℝ) := by
  have e0 := xyBlkSTM_03
  have e1 := xyBlkSTM_10
  have e2 := xyBlkSTM_21
  have e3 := xyBlkSTM_32
  have p1 : (-152164488 / 1000000000000 : ℝ) ≤ (xyBlkSTM 0 3 * xyBlkSTM 1 0) ∧
      (xyBlkSTM 0 3 * xyBlkSTM 1 0) ≤ (-150698951 / 1000000000000 : ℝ) := by
    have hm := mul_nonneg_nonpos_bounds (by norm_num : (0 : ℝ) ≤ (12241 / 1000000 : ℝ)) (by norm_num : (-12311 / 1000000 : ℝ) ≤ (0 : ℝ)) e0.1 e0.2 e1.1 e1.2
    convert hm using 1 <;> norm_num
  have p2 : (10055688903377 / 1000000000000000000 : ℝ) ≤ (xyBlkSTM 0 3 * xyBlkSTM 1 0 * xyBlkSTM 2 1) ∧
      (xyBlkSTM 0 3 * xyBlkSTM 1 0 * xyBlkSTM 2 1) ≤ (10158501218880 / 1000000000000000000 : ℝ) := by
    have hm := mul_nonpos_nonpos_bounds (by norm_num : (-150698951 / 1000000000000 : ℝ) ≤ (0 : ℝ)) (by norm_num : (-66727 / 1000000 : ℝ) ≤ (0 : ℝ)) p1.1 p1.2 e2.1 e2.2
    convert hm using 1 <;> norm_num
  have p3 : (-3860230463174400 / 1000000000000000000000000 : ℝ) ≤ (xyBlkSTM 0 3 * xyBlkSTM 1 0 * xyBlkSTM 2 1 * xyBlkSTM 3 2) ∧
      (xyBlkSTM 0 3 * xyBlkSTM 1 0 * xyBlkSTM 2 1 * xyBlkSTM 3 2) ≤ (-3177597693467132 / 1000000000000000000000000 : ℝ) := by
    have hm := mul_nonneg_nonpos_bounds (by norm_num : (0 : ℝ) ≤ (10055688903377 / 1000000000000000000 : ℝ)) (by norm_num : (-316 / 1000000 : ℝ) ≤ (0 : ℝ)) p2.1 p2.2 e3.1 e3.2
    convert hm using 1 <;> norm_num
  exact p3

lemma xyBlkSTM_prod_19 :
    (4587643020385685 / 1000000000000000000000000 : ℝ) ≤ (xyBlkSTM 0 3 * xyBlkSTM 1 0 * xyBlkSTM 2 2 * xyBlkSTM 3 1) ∧
      (xyBlkSTM 0 3 * xyBlkSTM 1 0 * xyBlkSTM 2 2 * xyBlkSTM 3 1) ≤ (5740942602607128 / 1000000000000000000000000 : ℝ) := by
  have e0 := xyBlkSTM_03
  have e1 := xyBlkSTM_10
  have e2 := xyBlkSTM_22
  have e3 := xyBlkSTM_31
  have p1 : (-152164488 / 1000000000000 : ℝ) ≤ (xyBlkSTM 0 3 * xyBlkSTM 1 0) ∧
      (xyBlkSTM 0 3 * xyBlkSTM 1 0) ≤ (-150698951 / 1000000000000 : ℝ) := by
    have hm := mul_nonneg_nonpos_bounds (by norm_num : (0 : ℝ) ≤ (12241 / 1000000 : ℝ)) (by norm_num : (-12311 / 1000000 : ℝ) ≤ (0 : ℝ)) e0.1 e0.2 e1.1 e1.2
    convert hm using 1 <;> norm_num
  have p2 : (-123405399768 / 1000000000000000000 : ℝ) ≤ (xyBlkSTM 0 3 * xyBlkSTM 1 0 * xyBlkSTM 2 2) ∧
      (xyBlkSTM 0 3 * xyBlkSTM 1 0 * xyBlkSTM 2 2) ≤ (-98707812905 / 1000000000000000000 : ℝ) := by
    have hm := mul_nonpos_nonneg_bounds (by norm_num : (-150698951 / 1000000000000 : ℝ) ≤ (0 : ℝ)) (by norm_num : (0 : ℝ) ≤ (655 / 1000000 : ℝ)) p1.1 p1.2 e2.1 e2.2
    convert hm using 1 <;> norm_num
  have p3 : (4587643020385685 / 1000000000000000000000000 : ℝ) ≤ (xyBlkSTM 0 3 * xyBlkSTM 1 0 * xyBlkSTM 2 2 * xyBlkSTM 3 1) ∧
      (xyBlkSTM 0 3 * xyBlkSTM 1 0 * xyBlkSTM 2 2 * xyBlkSTM 3 1) ≤ (5740942602607128 / 1000000000000000000000000 : ℝ) := by
    have hm := mul_nonpos_nonpos_bounds (by norm_num : (-98707812905 / 1000000000000000000 : ℝ) ≤ (0 : ℝ)) (by norm_num : (-46477 / 1000000 : ℝ) ≤ (0 : ℝ)) p2.1 p2.2 e3.1 e3.2
    convert hm using 1 <;> norm_num
  exact p3

lemma xyBlkSTM_prod_20 :
    (-644783873373360 / 1000000000000000000000000 : ℝ) ≤ (xyBlkSTM 0 3 * xyBlkSTM 1 1 * xyBlkSTM 2 0 * xyBlkSTM 3 2) ∧
      (xyBlkSTM 0 3 * xyBlkSTM 1 1 * xyBlkSTM 2 0 * xyBlkSTM 3 2) ≤ (-518906029333740 / 1000000000000000000000000 : ℝ) := by
  have e0 := xyBlkSTM_03
  have e1 := xyBlkSTM_11
  have e2 := xyBlkSTM_20
  have e3 := xyBlkSTM_32
  have p1 : (-308396886 / 1000000000000 : ℝ) ≤ (xyBlkSTM 0 3 * xyBlkSTM 1 1) ∧
      (xyBlkSTM 0 3 * xyBlkSTM 1 1) ≤ (-305963795 / 1000000000000 : ℝ) := by
    have hm := mul_nonneg_nonpos_bounds (by norm_num : (0 : ℝ) ≤ (12241 / 1000000 : ℝ)) (by norm_num : (-24995 / 1000000 : ℝ) ≤ (0 : ℝ)) e0.1 e0.2 e1.1 e1.2
    convert hm using 1 <;> norm_num
  have p2 : (1642107687765 / 1000000000000000000 : ℝ) ≤ (xyBlkSTM 0 3 * xyBlkSTM 1 1 * xyBlkSTM 2 0) ∧
      (xyBlkSTM 0 3 * xyBlkSTM 1 1 * xyBlkSTM 2 0) ≤ (1696799666772 / 1000000000000000000 : ℝ) := by
    have hm := mul_nonpos_nonpos_bounds (by norm_num : (-305963795 / 1000000000000 : ℝ) ≤ (0 : ℝ)) (by norm_num : (-5367 / 1000000 : ℝ) ≤ (0 : ℝ)) p1.1 p1.2 e2.1 e2.2
    convert hm using 1 <;> norm_num
  have p3 : (-644783873373360 / 1000000000000000000000000 : ℝ) ≤ (xyBlkSTM 0 3 * xyBlkSTM 1 1 * xyBlkSTM 2 0 * xyBlkSTM 3 2) ∧
      (xyBlkSTM 0 3 * xyBlkSTM 1 1 * xyBlkSTM 2 0 * xyBlkSTM 3 2) ≤ (-518906029333740 / 1000000000000000000000000 : ℝ) := by
    have hm := mul_nonneg_nonpos_bounds (by norm_num : (0 : ℝ) ≤ (1642107687765 / 1000000000000000000 : ℝ)) (by norm_num : (-316 / 1000000 : ℝ) ≤ (0 : ℝ)) p2.1 p2.2 e3.1 e3.2
    convert hm using 1 <;> norm_num
  exact p3

lemma xyBlkSTM_prod_21 :
    (12249232996083450 / 1000000000000000000000000 : ℝ) ≤ (xyBlkSTM 0 3 * xyBlkSTM 1 1 * xyBlkSTM 2 2 * xyBlkSTM 3 0) ∧
      (xyBlkSTM 0 3 * xyBlkSTM 1 1 * xyBlkSTM 2 2 * xyBlkSTM 3 0) ≤ (15299471135853366 / 1000000000000000000000000 : ℝ) := by
  have e0 := xyBlkSTM_03
  have e1 := xyBlkSTM_11
  have e2 := xyBlkSTM_22
  have e3 := xyBlkSTM_30
  have p1 : (-308396886 / 1000000000000 : ℝ) ≤ (xyBlkSTM 0 3 * xyBlkSTM 1 1) ∧
      (xyBlkSTM 0 3 * xyBlkSTM 1 1) ≤ (-305963795 / 1000000000000 : ℝ) := by
    have hm := mul_nonneg_nonpos_bounds (by norm_num : (0 : ℝ) ≤ (12241 / 1000000 : ℝ)) (by norm_num : (-24995 / 1000000 : ℝ) ≤ (0 : ℝ)) e0.1 e0.2 e1.1 e1.2
    convert hm using 1 <;> norm_num
  have p2 : (-250109874546 / 1000000000000000000 : ℝ) ≤ (xyBlkSTM 0 3 * xyBlkSTM 1 1 * xyBlkSTM 2 2) ∧
      (xyBlkSTM 0 3 * xyBlkSTM 1 1 * xyBlkSTM 2 2) ≤ (-200406285725 / 1000000000000000000 : ℝ) := by
    have hm := mul_nonpos_nonneg_bounds (by norm_num : (-305963795 / 1000000000000 : ℝ) ≤ (0 : ℝ)) (by norm_num : (0 : ℝ) ≤ (655 / 1000000 : ℝ)) p1.1 p1.2 e2.1 e2.2
    convert hm using 1 <;> norm_num
  have p3 : (12249232996083450 / 1000000000000000000000000 : ℝ) ≤ (xyBlkSTM 0 3 * xyBlkSTM 1 1 * xyBlkSTM 2 2 * xyBlkSTM 3 0) ∧
      (xyBlkSTM 0 3 * xyBlkSTM 1 1 * xyBlkSTM 2 2 * xyBlkSTM 3 0) ≤ (15299471135853366 / 1000000000000000000000000 : ℝ) := by
    have hm := mul_nonpos_nonpos_bounds (by norm_num : (-200406285725 / 1000000000000000000 : ℝ) ≤ (0 : ℝ)) (by norm_num : (-61122 / 1000000 : ℝ) ≤ (0 : ℝ)) p2.1 p2.2 e3.1 e3.2
    convert hm using 1 <;> norm_num
  exact p3

lemma xyBlkSTM_prod_22 :
    (38503629279601590 / 1000000000000000000000000 : ℝ) ≤ (xyBlkSTM 0 3 * xyBlkSTM 1 2 * xyBlkSTM 2 0 * xyBlkSTM 3 1) ∧
      (xyBlkSTM 0 3 * xyBlkSTM 1 2 * xyBlkSTM 2 0 * xyBlkSTM 3 1) ≤ (39925912786299036 / 1000000000000000000000000 : ℝ) := by
  have e0 := xyBlkSTM_03
  have e1 := xyBlkSTM_12
  have e2 := xyBlkSTM_20
  have e3 := xyBlkSTM_31
  have p1 : (154359010 / 1000000000000 : ℝ) ≤ (xyBlkSTM 0 3 * xyBlkSTM 1 2) ∧
      (xyBlkSTM 0 3 * xyBlkSTM 1 2) ≤ (155985858 / 1000000000000 : ℝ) := by
    have hm := mul_nonneg_bounds (by norm_num : (0 : ℝ) ≤ (12241 / 1000000 : ℝ)) (by norm_num : (0 : ℝ) ≤ (12610 / 1000000 : ℝ)) e0.1 e0.2 e1.1 e1.2
    convert hm using 1 <;> norm_num
  have p2 : (-858234190716 / 1000000000000000000 : ℝ) ≤ (xyBlkSTM 0 3 * xyBlkSTM 1 2 * xyBlkSTM 2 0) ∧
      (xyBlkSTM 0 3 * xyBlkSTM 1 2 * xyBlkSTM 2 0) ≤ (-828444806670 / 1000000000000000000 : ℝ) := by
    have hm := mul_nonneg_nonpos_bounds (by norm_num : (0 : ℝ) ≤ (154359010 / 1000000000000 : ℝ)) (by norm_num : (-5367 / 1000000 : ℝ) ≤ (0 : ℝ)) p1.1 p1.2 e2.1 e2.2
    convert hm using 1 <;> norm_num
  have p3 : (38503629279601590 / 1000000000000000000000000 : ℝ) ≤ (xyBlkSTM 0 3 * xyBlkSTM 1 2 * xyBlkSTM 2 0 * xyBlkSTM 3 1) ∧
      (xyBlkSTM 0 3 * xyBlkSTM 1 2 * xyBlkSTM 2 0 * xyBlkSTM 3 1) ≤ (39925912786299036 / 1000000000000000000000000 : ℝ) := by
    have hm := mul_nonpos_nonpos_bounds (by norm_num : (-828444806670 / 1000000000000000000 : ℝ) ≤ (0 : ℝ)) (by norm_num : (-46477 / 1000000 : ℝ) ≤ (0 : ℝ)) p2.1 p2.2 e3.1 e3.2
    convert hm using 1 <;> norm_num
  exact p3

lemma xyBlkSTM_prod_23 :
    (629551322743022940 / 1000000000000000000000000 : ℝ) ≤ (xyBlkSTM 0 3 * xyBlkSTM 1 2 * xyBlkSTM 2 1 * xyBlkSTM 3 0) ∧
      (xyBlkSTM 0 3 * xyBlkSTM 1 2 * xyBlkSTM 2 1 * xyBlkSTM 3 0) ≤ (637011297000373680 / 1000000000000000000000000 : ℝ) := by
  have e0 := xyBlkSTM_03
  have e1 := xyBlkSTM_12
  have e2 := xyBlkSTM_21
  have e3 := xyBlkSTM_30
  have p1 : (154359010 / 1000000000000 : ℝ) ≤ (xyBlkSTM 0 3 * xyBlkSTM 1 2) ∧
      (xyBlkSTM 0 3 * xyBlkSTM 1 2) ≤ (155985858 / 1000000000000 : ℝ) := by
    have hm := mul_nonneg_bounds (by norm_num : (0 : ℝ) ≤ (12241 / 1000000 : ℝ)) (by norm_num : (0 : ℝ) ≤ (12610 / 1000000 : ℝ)) e0.1 e0.2 e1.1 e1.2
    convert hm using 1 <;> norm_num
  have p2 : (-10413615880080 / 1000000000000000000 : ℝ) ≤ (xyBlkSTM 0 3 * xyBlkSTM 1 2 * xyBlkSTM 2 1) ∧
      (xyBlkSTM 0 3 * xyBlkSTM 1 2 * xyBlkSTM 2 1) ≤ (-10299913660270 / 1000000000000000000 : ℝ) := by
    have hm := mul_nonneg_nonpos_bounds (by norm_num : (0 : ℝ) ≤ (154359010 / 1000000000000 : ℝ)) (by norm_num : (-66727 / 1000000 : ℝ) ≤ (0 : ℝ)) p1.1 p1.2 e2.1 e2.2
    convert hm using 1 <;> norm_num
  have p3 : (629551322743022940 / 1000000000000000000000000 : ℝ) ≤ (xyBlkSTM 0 3 * xyBlkSTM 1 2 * xyBlkSTM 2 1 * xyBlkSTM 3 0) ∧
      (xyBlkSTM 0 3 * xyBlkSTM 1 2 * xyBlkSTM 2 1 * xyBlkSTM 3 0) ≤ (637011297000373680 / 1000000000000000000000000 : ℝ) := by
    have hm := mul_nonpos_nonpos_bounds (by norm_num : (-10299913660270 / 1000000000000000000 : ℝ) ≤ (0 : ℝ)) (by norm_num : (-61122 / 1000000 : ℝ) ≤ (0 : ℝ)) p2.1 p2.2 e3.1 e3.2
    convert hm using 1 <;> norm_num
  exact p3

lemma xyBlkSTM_term_0 :
    (3269559610269400 / 1000000000000000000000000 : ℝ) ≤ (xyBlkSTM 0 0 * xyBlkSTM 1 1 * xyBlkSTM 2 2 * xyBlkSTM 3 3) ∧ (xyBlkSTM 0 0 * xyBlkSTM 1 1 * xyBlkSTM 2 2 * xyBlkSTM 3 3) ≤ (4166951273623656 / 1000000000000000000000000 : ℝ) :=
  xyBlkSTM_prod_0

lemma xyBlkSTM_term_1 :
    (55760657337660 / 1000000000000000000000000 : ℝ) ≤ -(xyBlkSTM 0 0 * xyBlkSTM 1 1 * xyBlkSTM 2 3 * xyBlkSTM 3 2) ∧ -(xyBlkSTM 0 0 * xyBlkSTM 1 1 * xyBlkSTM 2 3 * xyBlkSTM 3 2) ≤ (71236929186360 / 1000000000000000000000000 : ℝ) := by
  have h := xyBlkSTM_prod_1
  constructor <;> linarith [h.1, h.2]

lemma xyBlkSTM_term_2 :
    (-173495868698882880 / 1000000000000000000000000 : ℝ) ≤ -(xyBlkSTM 0 0 * xyBlkSTM 1 2 * xyBlkSTM 2 1 * xyBlkSTM 3 3) ∧ -(xyBlkSTM 0 0 * xyBlkSTM 1 2 * xyBlkSTM 2 1 * xyBlkSTM 3 3) ≤ (-168039548116228880 / 1000000000000000000000000 : ℝ) := by
  have h := xyBlkSTM_prod_2
  constructor <;> linarith [h.1, h.2]

lemma xyBlkSTM_term_3 :
    (4137526945433310 / 1000000000000000000000000 : ℝ) ≤ (xyBlkSTM 0 0 * xyBlkSTM 1 2 * xyBlkSTM 2 3 * xyBlkSTM 3 1) ∧ (xyBlkSTM 0 0 * xyBlkSTM 1 2 * xyBlkSTM 2 3 * xyBlkSTM 3 1) ≤ (4411089574834086 / 1000000000000000000000000 : ℝ) :=
  xyBlkSTM_prod_3

lemma xyBlkSTM_term_4 :
    (-1049333124556800 / 1000000000000000000000000 : ℝ) ≤ (xyBlkSTM 0 0 * xyBlkSTM 1 3 * xyBlkSTM 2 1 * xyBlkSTM 3 2) ∧ (xyBlkSTM 0 0 * xyBlkSTM 1 3 * xyBlkSTM 2 1 * xyBlkSTM 3 2) ≤ (-845551326982748 / 1000000000000000000000000 : ℝ) :=
  xyBlkSTM_prod_4

lemma xyBlkSTM_term_5 :
    (-1560570358833216 / 1000000000000000000000000 : ℝ) ≤ -(xyBlkSTM 0 0 * xyBlkSTM 1 3 * xyBlkSTM 2 2 * xyBlkSTM 3 1) ∧ -(xyBlkSTM 0 0 * xyBlkSTM 1 3 * xyBlkSTM 2 2 * xyBlkSTM 3 1) ≤ (-1220761096215965 / 1000000000000000000000000 : ℝ) := by
  have h := xyBlkSTM_prod_5
  constructor <;> linarith [h.1, h.2]

lemma xyBlkSTM_term_6 :
    (10710565590692240 / 1000000000000000000000000 : ℝ) ≤ -(xyBlkSTM 0 1 * xyBlkSTM 1 0 * xyBlkSTM 2 2 * xyBlkSTM 3 3) ∧ -(xyBlkSTM 0 1 * xyBlkSTM 1 0 * xyBlkSTM 2 2 * xyBlkSTM 3 3) ≤ (13334559169530304 / 1000000000000000000000000 : ℝ) := by
  have h := xyBlkSTM_prod_6
  constructor <;> linarith [h.1, h.2]

lemma xyBlkSTM_term_7 :
    (182663186784936 / 1000000000000000000000000 : ℝ) ≤ (xyBlkSTM 0 1 * xyBlkSTM 1 0 * xyBlkSTM 2 3 * xyBlkSTM 3 2) ∧ (xyBlkSTM 0 1 * xyBlkSTM 1 0 * xyBlkSTM 2 3 * xyBlkSTM 3 2) ≤ (227963560146240 / 1000000000000000000000000 : ℝ) :=
  xyBlkSTM_prod_7

lemma xyBlkSTM_term_8 :
    (-92736416874231648 / 1000000000000000000000000 : ℝ) ≤ (xyBlkSTM 0 1 * xyBlkSTM 1 2 * xyBlkSTM 2 0 * xyBlkSTM 3 3) ∧ (xyBlkSTM 0 1 * xyBlkSTM 1 2 * xyBlkSTM 2 0 * xyBlkSTM 3 3) ≤ (-89892706351899360 / 1000000000000000000000000 : ℝ) :=
  xyBlkSTM_prod_8

lemma xyBlkSTM_term_9 :
    (36189556372518120 / 1000000000000000000000000 : ℝ) ≤ -(xyBlkSTM 0 1 * xyBlkSTM 1 2 * xyBlkSTM 2 3 * xyBlkSTM 3 0) ∧ -(xyBlkSTM 0 1 * xyBlkSTM 1 2 * xyBlkSTM 2 3 * xyBlkSTM 3 0) ≤ (37618314373428228 / 1000000000000000000000000 : ℝ) := by
  have h := xyBlkSTM_prod_9
  constructor <;> linarith [h.1, h.2]

lemma xyBlkSTM_term_10 :
    (-560885943905280 / 1000000000000000000000000 : ℝ) ≤ -(xyBlkSTM 0 1 * xyBlkSTM 1 3 * xyBlkSTM 2 0 * xyBlkSTM 3 2) ∧ -(xyBlkSTM 0 1 * xyBlkSTM 1 3 * xyBlkSTM 2 0 * xyBlkSTM 3 2) ≤ (-452327431214856 / 1000000000000000000000000 : ℝ) := by
  have h := xyBlkSTM_prod_10
  constructor <;> linarith [h.1, h.2]

lemma xyBlkSTM_term_11 :
    (-13308735940291968 / 1000000000000000000000000 : ℝ) ≤ (xyBlkSTM 0 1 * xyBlkSTM 1 3 * xyBlkSTM 2 2 * xyBlkSTM 3 0) ∧ (xyBlkSTM 0 1 * xyBlkSTM 1 3 * xyBlkSTM 2 2 * xyBlkSTM 3 0) ≤ (-10677586657809180 / 1000000000000000000000000 : ℝ) :=
  xyBlkSTM_prod_11

lemma xyBlkSTM_term_12 :
    (-171625922538228480 / 1000000000000000000000000 : ℝ) ≤ (xyBlkSTM 0 2 * xyBlkSTM 1 0 * xyBlkSTM 2 1 * xyBlkSTM 3 3) ∧ (xyBlkSTM 0 2 * xyBlkSTM 1 0 * xyBlkSTM 2 1 * xyBlkSTM 3 3) ≤ (-165713823186004912 / 1000000000000000000000000 : ℝ) :=
  xyBlkSTM_prod_12

lemma xyBlkSTM_term_13 :
    (4080262154648394 / 1000000000000000000000000 : ℝ) ≤ -(xyBlkSTM 0 2 * xyBlkSTM 1 0 * xyBlkSTM 2 3 * xyBlkSTM 3 1) ∧ -(xyBlkSTM 0 2 * xyBlkSTM 1 0 * xyBlkSTM 2 3 * xyBlkSTM 3 1) ≤ (4363546655935656 / 1000000000000000000000000 : ℝ) := by
  have h := xyBlkSTM_prod_13
  constructor <;> linarith [h.1, h.2]

lemma xyBlkSTM_term_14 :
    (27061292929545840 / 1000000000000000000000000 : ℝ) ≤ -(xyBlkSTM 0 2 * xyBlkSTM 1 1 * xyBlkSTM 2 0 * xyBlkSTM 3 3) ∧ -(xyBlkSTM 0 2 * xyBlkSTM 1 1 * xyBlkSTM 2 0 * xyBlkSTM 3 3) ≤ (28667103728950512 / 1000000000000000000000000 : ℝ) := by
  have h := xyBlkSTM_prod_14
  constructor <;> linarith [h.1, h.2]

lemma xyBlkSTM_term_15 :
    (-11628744743436282 / 1000000000000000000000000 : ℝ) ≤ (xyBlkSTM 0 2 * xyBlkSTM 1 1 * xyBlkSTM 2 3 * xyBlkSTM 3 0) ∧ (xyBlkSTM 0 2 * xyBlkSTM 1 1 * xyBlkSTM 2 3 * xyBlkSTM 3 0) ≤ (-10894501075017780 / 1000000000000000000000000 : ℝ) :=
  xyBlkSTM_prod_15

lemma xyBlkSTM_term_16 :
    (-10736154424501632 / 1000000000000000000000000 : ℝ) ≤ (xyBlkSTM 0 2 * xyBlkSTM 1 3 * xyBlkSTM 2 0 * xyBlkSTM 3 1) ∧ (xyBlkSTM 0 2 * xyBlkSTM 1 3 * xyBlkSTM 2 0 * xyBlkSTM 3 1) ≤ (-10103921493871074 / 1000000000000000000000000 : ℝ) :=
  xyBlkSTM_prod_16

lemma xyBlkSTM_term_17 :
    (165203573283105684 / 1000000000000000000000000 : ℝ) ≤ -(xyBlkSTM 0 2 * xyBlkSTM 1 3 * xyBlkSTM 2 1 * xyBlkSTM 3 0) ∧ -(xyBlkSTM 0 2 * xyBlkSTM 1 3 * xyBlkSTM 2 1 * xyBlkSTM 3 0) ≤ (171293557929500160 / 1000000000000000000000000 : ℝ) := by
  have h := xyBlkSTM_prod_17
  constructor <;> linarith [h.1, h.2]

lemma xyBlkSTM_term_18 :
    (3177597693467132 / 1000000000000000000000000 : ℝ) ≤ -(xyBlkSTM 0 3 * xyBlkSTM 1 0 * xyBlkSTM 2 1 * xyBlkSTM 3 2) ∧ -(xyBlkSTM 0 3 * xyBlkSTM 1 0 * xyBlkSTM 2 1 * xyBlkSTM 3 2) ≤ (3860230463174400 / 1000000000000000000000000 : ℝ) := by
  have h := xyBlkSTM_prod_18
  constructor <;> linarith [h.1, h.2]

lemma xyBlkSTM_term_19 :
    (4587643020385685 / 1000000000000000000000000 : ℝ) ≤ (xyBlkSTM 0 3 * xyBlkSTM 1 0 * xyBlkSTM 2 2 * xyBlkSTM 3 1) ∧ (xyBlkSTM 0 3 * xyBlkSTM 1 0 * xyBlkSTM 2 2 * xyBlkSTM 3 1) ≤ (5740942602607128 / 1000000000000000000000000 : ℝ) :=
  xyBlkSTM_prod_19

lemma xyBlkSTM_term_20 :
    (-644783873373360 / 1000000000000000000000000 : ℝ) ≤ (xyBlkSTM 0 3 * xyBlkSTM 1 1 * xyBlkSTM 2 0 * xyBlkSTM 3 2) ∧ (xyBlkSTM 0 3 * xyBlkSTM 1 1 * xyBlkSTM 2 0 * xyBlkSTM 3 2) ≤ (-518906029333740 / 1000000000000000000000000 : ℝ) :=
  xyBlkSTM_prod_20

lemma xyBlkSTM_term_21 :
    (-15299471135853366 / 1000000000000000000000000 : ℝ) ≤ -(xyBlkSTM 0 3 * xyBlkSTM 1 1 * xyBlkSTM 2 2 * xyBlkSTM 3 0) ∧ -(xyBlkSTM 0 3 * xyBlkSTM 1 1 * xyBlkSTM 2 2 * xyBlkSTM 3 0) ≤ (-12249232996083450 / 1000000000000000000000000 : ℝ) := by
  have h := xyBlkSTM_prod_21
  constructor <;> linarith [h.1, h.2]

lemma xyBlkSTM_term_22 :
    (-39925912786299036 / 1000000000000000000000000 : ℝ) ≤ -(xyBlkSTM 0 3 * xyBlkSTM 1 2 * xyBlkSTM 2 0 * xyBlkSTM 3 1) ∧ -(xyBlkSTM 0 3 * xyBlkSTM 1 2 * xyBlkSTM 2 0 * xyBlkSTM 3 1) ≤ (-38503629279601590 / 1000000000000000000000000 : ℝ) := by
  have h := xyBlkSTM_prod_22
  constructor <;> linarith [h.1, h.2]

lemma xyBlkSTM_term_23 :
    (629551322743022940 / 1000000000000000000000000 : ℝ) ≤ (xyBlkSTM 0 3 * xyBlkSTM 1 2 * xyBlkSTM 2 1 * xyBlkSTM 3 0) ∧ (xyBlkSTM 0 3 * xyBlkSTM 1 2 * xyBlkSTM 2 1 * xyBlkSTM 3 0) ≤ (637011297000373680 / 1000000000000000000000000 : ℝ) :=
  xyBlkSTM_prod_23

lemma xyBlkSTM_det_bounds :
    (355 / 1000000000 : ℝ) ≤ xyBlkSTM.det ∧
      xyBlkSTM.det ≤ (402 / 1000000000 : ℝ) := by
  rw [det_fin_four]
  have t0 := xyBlkSTM_term_0
  have t1 := xyBlkSTM_term_1
  have t2 := xyBlkSTM_term_2
  have t3 := xyBlkSTM_term_3
  have t4 := xyBlkSTM_term_4
  have t5 := xyBlkSTM_term_5
  have t6 := xyBlkSTM_term_6
  have t7 := xyBlkSTM_term_7
  have t8 := xyBlkSTM_term_8
  have t9 := xyBlkSTM_term_9
  have t10 := xyBlkSTM_term_10
  have t11 := xyBlkSTM_term_11
  have t12 := xyBlkSTM_term_12
  have t13 := xyBlkSTM_term_13
  have t14 := xyBlkSTM_term_14
  have t15 := xyBlkSTM_term_15
  have t16 := xyBlkSTM_term_16
  have t17 := xyBlkSTM_term_17
  have t18 := xyBlkSTM_term_18
  have t19 := xyBlkSTM_term_19
  have t20 := xyBlkSTM_term_20
  have t21 := xyBlkSTM_term_21
  have t22 := xyBlkSTM_term_22
  have t23 := xyBlkSTM_term_23
  have s0 := t0
  have s1 : (3325320267607060 / 1000000000000000000000000 : ℝ) ≤ ((xyBlkSTM 0 0 * xyBlkSTM 1 1 * xyBlkSTM 2 2 * xyBlkSTM 3 3) + -(xyBlkSTM 0 0 * xyBlkSTM 1 1 * xyBlkSTM 2 3 * xyBlkSTM 3 2)) ∧ ((xyBlkSTM 0 0 * xyBlkSTM 1 1 * xyBlkSTM 2 2 * xyBlkSTM 3 3) + -(xyBlkSTM 0 0 * xyBlkSTM 1 1 * xyBlkSTM 2 3 * xyBlkSTM 3 2)) ≤ (4238188202810016 / 1000000000000000000000000 : ℝ) := by
    have hm := add_bounds s0.1 s0.2 t1.1 t1.2
    convert hm using 1 <;> first | ring | norm_num
  have s2 : (-170170548431275820 / 1000000000000000000000000 : ℝ) ≤ ((xyBlkSTM 0 0 * xyBlkSTM 1 1 * xyBlkSTM 2 2 * xyBlkSTM 3 3) + -(xyBlkSTM 0 0 * xyBlkSTM 1 1 * xyBlkSTM 2 3 * xyBlkSTM 3 2) + -(xyBlkSTM 0 0 * xyBlkSTM 1 2 * xyBlkSTM 2 1 * xyBlkSTM 3 3)) ∧ ((xyBlkSTM 0 0 * xyBlkSTM 1 1 * xyBlkSTM 2 2 * xyBlkSTM 3 3) + -(xyBlkSTM 0 0 * xyBlkSTM 1 1 * xyBlkSTM 2 3 * xyBlkSTM 3 2) + -(xyBlkSTM 0 0 * xyBlkSTM 1 2 * xyBlkSTM 2 1 * xyBlkSTM 3 3)) ≤ (-163801359913418864 / 1000000000000000000000000 : ℝ) := by
    have hm := add_bounds s1.1 s1.2 t2.1 t2.2
    convert hm using 1 <;> first | ring | norm_num
  have s3 : (-166033021485842510 / 1000000000000000000000000 : ℝ) ≤ ((xyBlkSTM 0 0 * xyBlkSTM 1 1 * xyBlkSTM 2 2 * xyBlkSTM 3 3) + -(xyBlkSTM 0 0 * xyBlkSTM 1 1 * xyBlkSTM 2 3 * xyBlkSTM 3 2) + -(xyBlkSTM 0 0 * xyBlkSTM 1 2 * xyBlkSTM 2 1 * xyBlkSTM 3 3) + (xyBlkSTM 0 0 * xyBlkSTM 1 2 * xyBlkSTM 2 3 * xyBlkSTM 3 1)) ∧ ((xyBlkSTM 0 0 * xyBlkSTM 1 1 * xyBlkSTM 2 2 * xyBlkSTM 3 3) + -(xyBlkSTM 0 0 * xyBlkSTM 1 1 * xyBlkSTM 2 3 * xyBlkSTM 3 2) + -(xyBlkSTM 0 0 * xyBlkSTM 1 2 * xyBlkSTM 2 1 * xyBlkSTM 3 3) + (xyBlkSTM 0 0 * xyBlkSTM 1 2 * xyBlkSTM 2 3 * xyBlkSTM 3 1)) ≤ (-159390270338584778 / 1000000000000000000000000 : ℝ) := by
    have hm := add_bounds s2.1 s2.2 t3.1 t3.2
    convert hm using 1 <;> first | ring | norm_num
  have s4 : (-167082354610399310 / 1000000000000000000000000 : ℝ) ≤ ((xyBlkSTM 0 0 * xyBlkSTM 1 1 * xyBlkSTM 2 2 * xyBlkSTM 3 3) + -(xyBlkSTM 0 0 * xyBlkSTM 1 1 * xyBlkSTM 2 3 * xyBlkSTM 3 2) + -(xyBlkSTM 0 0 * xyBlkSTM 1 2 * xyBlkSTM 2 1 * xyBlkSTM 3 3) + (xyBlkSTM 0 0 * xyBlkSTM 1 2 * xyBlkSTM 2 3 * xyBlkSTM 3 1) + (xyBlkSTM 0 0 * xyBlkSTM 1 3 * xyBlkSTM 2 1 * xyBlkSTM 3 2)) ∧ ((xyBlkSTM 0 0 * xyBlkSTM 1 1 * xyBlkSTM 2 2 * xyBlkSTM 3 3) + -(xyBlkSTM 0 0 * xyBlkSTM 1 1 * xyBlkSTM 2 3 * xyBlkSTM 3 2) + -(xyBlkSTM 0 0 * xyBlkSTM 1 2 * xyBlkSTM 2 1 * xyBlkSTM 3 3) + (xyBlkSTM 0 0 * xyBlkSTM 1 2 * xyBlkSTM 2 3 * xyBlkSTM 3 1) + (xyBlkSTM 0 0 * xyBlkSTM 1 3 * xyBlkSTM 2 1 * xyBlkSTM 3 2)) ≤ (-160235821665567526 / 1000000000000000000000000 : ℝ) := by
    have hm := add_bounds s3.1 s3.2 t4.1 t4.2
    convert hm using 1 <;> first | ring | norm_num
  have s5 : (-168642924969232526 / 1000000000000000000000000 : ℝ) ≤ ((xyBlkSTM 0 0 * xyBlkSTM 1 1 * xyBlkSTM 2 2 * xyBlkSTM 3 3) + -(xyBlkSTM 0 0 * xyBlkSTM 1 1 * xyBlkSTM 2 3 * xyBlkSTM 3 2) + -(xyBlkSTM 0 0 * xyBlkSTM 1 2 * xyBlkSTM 2 1 * xyBlkSTM 3 3) + (xyBlkSTM 0 0 * xyBlkSTM 1 2 * xyBlkSTM 2 3 * xyBlkSTM 3 1) + (xyBlkSTM 0 0 * xyBlkSTM 1 3 * xyBlkSTM 2 1 * xyBlkSTM 3 2) + -(xyBlkSTM 0 0 * xyBlkSTM 1 3 * xyBlkSTM 2 2 * xyBlkSTM 3 1)) ∧ ((xyBlkSTM 0 0 * xyBlkSTM 1 1 * xyBlkSTM 2 2 * xyBlkSTM 3 3) + -(xyBlkSTM 0 0 * xyBlkSTM 1 1 * xyBlkSTM 2 3 * xyBlkSTM 3 2) + -(xyBlkSTM 0 0 * xyBlkSTM 1 2 * xyBlkSTM 2 1 * xyBlkSTM 3 3) + (xyBlkSTM 0 0 * xyBlkSTM 1 2 * xyBlkSTM 2 3 * xyBlkSTM 3 1) + (xyBlkSTM 0 0 * xyBlkSTM 1 3 * xyBlkSTM 2 1 * xyBlkSTM 3 2) + -(xyBlkSTM 0 0 * xyBlkSTM 1 3 * xyBlkSTM 2 2 * xyBlkSTM 3 1)) ≤ (-161456582761783491 / 1000000000000000000000000 : ℝ) := by
    have hm := add_bounds s4.1 s4.2 t5.1 t5.2
    convert hm using 1 <;> first | ring | norm_num
  have s6 : (-157932359378540286 / 1000000000000000000000000 : ℝ) ≤ ((xyBlkSTM 0 0 * xyBlkSTM 1 1 * xyBlkSTM 2 2 * xyBlkSTM 3 3) + -(xyBlkSTM 0 0 * xyBlkSTM 1 1 * xyBlkSTM 2 3 * xyBlkSTM 3 2) + -(xyBlkSTM 0 0 * xyBlkSTM 1 2 * xyBlkSTM 2 1 * xyBlkSTM 3 3) + (xyBlkSTM 0 0 * xyBlkSTM 1 2 * xyBlkSTM 2 3 * xyBlkSTM 3 1) + (xyBlkSTM 0 0 * xyBlkSTM 1 3 * xyBlkSTM 2 1 * xyBlkSTM 3 2) + -(xyBlkSTM 0 0 * xyBlkSTM 1 3 * xyBlkSTM 2 2 * xyBlkSTM 3 1) + -(xyBlkSTM 0 1 * xyBlkSTM 1 0 * xyBlkSTM 2 2 * xyBlkSTM 3 3)) ∧ ((xyBlkSTM 0 0 * xyBlkSTM 1 1 * xyBlkSTM 2 2 * xyBlkSTM 3 3) + -(xyBlkSTM 0 0 * xyBlkSTM 1 1 * xyBlkSTM 2 3 * xyBlkSTM 3 2) + -(xyBlkSTM 0 0 * xyBlkSTM 1 2 * xyBlkSTM 2 1 * xyBlkSTM 3 3) + (xyBlkSTM 0 0 * xyBlkSTM 1 2 * xyBlkSTM 2 3 * xyBlkSTM 3 1) + (xyBlkSTM 0 0 * xyBlkSTM 1 3 * xyBlkSTM 2 1 * xyBlkSTM 3 2) + -(xyBlkSTM 0 0 * xyBlkSTM 1 3 * xyBlkSTM 2 2 * xyBlkSTM 3 1) + -(xyBlkSTM 0 1 * xyBlkSTM 1 0 * xyBlkSTM 2 2 * xyBlkSTM 3 3)) ≤ (-148122023592253187 / 1000000000000000000000000 : ℝ) := by
    have hm := add_bounds s5.1 s5.2 t6.1 t6.2
    convert hm using 1 <;> first | ring | norm_num
  have s7 : (-157749696191755350 / 1000000000000000000000000 : ℝ) ≤ ((xyBlkSTM 0 0 * xyBlkSTM 1 1 * xyBlkSTM 2 2 * xyBlkSTM 3 3) + -(xyBlkSTM 0 0 * xyBlkSTM 1 1 * xyBlkSTM 2 3 * xyBlkSTM 3 2) + -(xyBlkSTM 0 0 * xyBlkSTM 1 2 * xyBlkSTM 2 1 * xyBlkSTM 3 3) + (xyBlkSTM 0 0 * xyBlkSTM 1 2 * xyBlkSTM 2 3 * xyBlkSTM 3 1) + (xyBlkSTM 0 0 * xyBlkSTM 1 3 * xyBlkSTM 2 1 * xyBlkSTM 3 2) + -(xyBlkSTM 0 0 * xyBlkSTM 1 3 * xyBlkSTM 2 2 * xyBlkSTM 3 1) + -(xyBlkSTM 0 1 * xyBlkSTM 1 0 * xyBlkSTM 2 2 * xyBlkSTM 3 3) + (xyBlkSTM 0 1 * xyBlkSTM 1 0 * xyBlkSTM 2 3 * xyBlkSTM 3 2)) ∧ ((xyBlkSTM 0 0 * xyBlkSTM 1 1 * xyBlkSTM 2 2 * xyBlkSTM 3 3) + -(xyBlkSTM 0 0 * xyBlkSTM 1 1 * xyBlkSTM 2 3 * xyBlkSTM 3 2) + -(xyBlkSTM 0 0 * xyBlkSTM 1 2 * xyBlkSTM 2 1 * xyBlkSTM 3 3) + (xyBlkSTM 0 0 * xyBlkSTM 1 2 * xyBlkSTM 2 3 * xyBlkSTM 3 1) + (xyBlkSTM 0 0 * xyBlkSTM 1 3 * xyBlkSTM 2 1 * xyBlkSTM 3 2) + -(xyBlkSTM 0 0 * xyBlkSTM 1 3 * xyBlkSTM 2 2 * xyBlkSTM 3 1) + -(xyBlkSTM 0 1 * xyBlkSTM 1 0 * xyBlkSTM 2 2 * xyBlkSTM 3 3) + (xyBlkSTM 0 1 * xyBlkSTM 1 0 * xyBlkSTM 2 3 * xyBlkSTM 3 2)) ≤ (-147894060032106947 / 1000000000000000000000000 : ℝ) := by
    have hm := add_bounds s6.1 s6.2 t7.1 t7.2
    convert hm using 1 <;> first | ring | norm_num
  have s8 : (-250486113065986998 / 1000000000000000000000000 : ℝ) ≤ ((xyBlkSTM 0 0 * xyBlkSTM 1 1 * xyBlkSTM 2 2 * xyBlkSTM 3 3) + -(xyBlkSTM 0 0 * xyBlkSTM 1 1 * xyBlkSTM 2 3 * xyBlkSTM 3 2) + -(xyBlkSTM 0 0 * xyBlkSTM 1 2 * xyBlkSTM 2 1 * xyBlkSTM 3 3) + (xyBlkSTM 0 0 * xyBlkSTM 1 2 * xyBlkSTM 2 3 * xyBlkSTM 3 1) + (xyBlkSTM 0 0 * xyBlkSTM 1 3 * xyBlkSTM 2 1 * xyBlkSTM 3 2) + -(xyBlkSTM 0 0 * xyBlkSTM 1 3 * xyBlkSTM 2 2 * xyBlkSTM 3 1) + -(xyBlkSTM 0 1 * xyBlkSTM 1 0 * xyBlkSTM 2 2 * xyBlkSTM 3 3) + (xyBlkSTM 0 1 * xyBlkSTM 1 0 * xyBlkSTM 2 3 * xyBlkSTM 3 2) + (xyBlkSTM 0 1 * xyBlkSTM 1 2 * xyBlkSTM 2 0 * xyBlkSTM 3 3)) ∧ ((xyBlkSTM 0 0 * xyBlkSTM 1 1 * xyBlkSTM 2 2 * xyBlkSTM 3 3) + -(xyBlkSTM 0 0 * xyBlkSTM 1 1 * xyBlkSTM 2 3 * xyBlkSTM 3 2) + -(xyBlkSTM 0 0 * xyBlkSTM 1 2 * xyBlkSTM 2 1 * xyBlkSTM 3 3) + (xyBlkSTM 0 0 * xyBlkSTM 1 2 * xyBlkSTM 2 3 * xyBlkSTM 3 1) + (xyBlkSTM 0 0 * xyBlkSTM 1 3 * xyBlkSTM 2 1 * xyBlkSTM 3 2) + -(xyBlkSTM 0 0 * xyBlkSTM 1 3 * xyBlkSTM 2 2 * xyBlkSTM 3 1) + -(xyBlkSTM 0 1 * xyBlkSTM 1 0 * xyBlkSTM 2 2 * xyBlkSTM 3 3) + (xyBlkSTM 0 1 * xyBlkSTM 1 0 * xyBlkSTM 2 3 * xyBlkSTM 3 2) + (xyBlkSTM 0 1 * xyBlkSTM 1 2 * xyBlkSTM 2 0 * xyBlkSTM 3 3)) ≤ (-237786766384006307 / 1000000000000000000000000 : ℝ) := by
    have hm := add_bounds s7.1 s7.2 t8.1 t8.2
    convert hm using 1 <;> first | ring | norm_num
  have s9 : (-214296556693468878 / 1000000000000000000000000 : ℝ) ≤ ((xyBlkSTM 0 0 * xyBlkSTM 1 1 * xyBlkSTM 2 2 * xyBlkSTM 3 3) + -(xyBlkSTM 0 0 * xyBlkSTM 1 1 * xyBlkSTM 2 3 * xyBlkSTM 3 2) + -(xyBlkSTM 0 0 * xyBlkSTM 1 2 * xyBlkSTM 2 1 * xyBlkSTM 3 3) + (xyBlkSTM 0 0 * xyBlkSTM 1 2 * xyBlkSTM 2 3 * xyBlkSTM 3 1) + (xyBlkSTM 0 0 * xyBlkSTM 1 3 * xyBlkSTM 2 1 * xyBlkSTM 3 2) + -(xyBlkSTM 0 0 * xyBlkSTM 1 3 * xyBlkSTM 2 2 * xyBlkSTM 3 1) + -(xyBlkSTM 0 1 * xyBlkSTM 1 0 * xyBlkSTM 2 2 * xyBlkSTM 3 3) + (xyBlkSTM 0 1 * xyBlkSTM 1 0 * xyBlkSTM 2 3 * xyBlkSTM 3 2) + (xyBlkSTM 0 1 * xyBlkSTM 1 2 * xyBlkSTM 2 0 * xyBlkSTM 3 3) + -(xyBlkSTM 0 1 * xyBlkSTM 1 2 * xyBlkSTM 2 3 * xyBlkSTM 3 0)) ∧ ((xyBlkSTM 0 0 * xyBlkSTM 1 1 * xyBlkSTM 2 2 * xyBlkSTM 3 3) + -(xyBlkSTM 0 0 * xyBlkSTM 1 1 * xyBlkSTM 2 3 * xyBlkSTM 3 2) + -(xyBlkSTM 0 0 * xyBlkSTM 1 2 * xyBlkSTM 2 1 * xyBlkSTM 3 3) + (xyBlkSTM 0 0 * xyBlkSTM 1 2 * xyBlkSTM 2 3 * xyBlkSTM 3 1) + (xyBlkSTM 0 0 * xyBlkSTM 1 3 * xyBlkSTM 2 1 * xyBlkSTM 3 2) + -(xyBlkSTM 0 0 * xyBlkSTM 1 3 * xyBlkSTM 2 2 * xyBlkSTM 3 1) + -(xyBlkSTM 0 1 * xyBlkSTM 1 0 * xyBlkSTM 2 2 * xyBlkSTM 3 3) + (xyBlkSTM 0 1 * xyBlkSTM 1 0 * xyBlkSTM 2 3 * xyBlkSTM 3 2) + (xyBlkSTM 0 1 * xyBlkSTM 1 2 * xyBlkSTM 2 0 * xyBlkSTM 3 3) + -(xyBlkSTM 0 1 * xyBlkSTM 1 2 * xyBlkSTM 2 3 * xyBlkSTM 3 0)) ≤ (-200168452010578079 / 1000000000000000000000000 : ℝ) := by
    have hm := add_bounds s8.1 s8.2 t9.1 t9.2
    convert hm using 1 <;> first | ring | norm_num
  have s10 : (-214857442637374158 / 1000000000000000000000000 : ℝ) ≤ ((xyBlkSTM 0 0 * xyBlkSTM 1 1 * xyBlkSTM 2 2 * xyBlkSTM 3 3) + -(xyBlkSTM 0 0 * xyBlkSTM 1 1 * xyBlkSTM 2 3 * xyBlkSTM 3 2) + -(xyBlkSTM 0 0 * xyBlkSTM 1 2 * xyBlkSTM 2 1 * xyBlkSTM 3 3) + (xyBlkSTM 0 0 * xyBlkSTM 1 2 * xyBlkSTM 2 3 * xyBlkSTM 3 1) + (xyBlkSTM 0 0 * xyBlkSTM 1 3 * xyBlkSTM 2 1 * xyBlkSTM 3 2) + -(xyBlkSTM 0 0 * xyBlkSTM 1 3 * xyBlkSTM 2 2 * xyBlkSTM 3 1) + -(xyBlkSTM 0 1 * xyBlkSTM 1 0 * xyBlkSTM 2 2 * xyBlkSTM 3 3) + (xyBlkSTM 0 1 * xyBlkSTM 1 0 * xyBlkSTM 2 3 * xyBlkSTM 3 2) + (xyBlkSTM 0 1 * xyBlkSTM 1 2 * xyBlkSTM 2 0 * xyBlkSTM 3 3) + -(xyBlkSTM 0 1 * xyBlkSTM 1 2 * xyBlkSTM 2 3 * xyBlkSTM 3 0) + -(xyBlkSTM 0 1 * xyBlkSTM 1 3 * xyBlkSTM 2 0 * xyBlkSTM 3 2)) ∧ ((xyBlkSTM 0 0 * xyBlkSTM 1 1 * xyBlkSTM 2 2 * xyBlkSTM 3 3) + -(xyBlkSTM 0 0 * xyBlkSTM 1 1 * xyBlkSTM 2 3 * xyBlkSTM 3 2) + -(xyBlkSTM 0 0 * xyBlkSTM 1 2 * xyBlkSTM 2 1 * xyBlkSTM 3 3) + (xyBlkSTM 0 0 * xyBlkSTM 1 2 * xyBlkSTM 2 3 * xyBlkSTM 3 1) + (xyBlkSTM 0 0 * xyBlkSTM 1 3 * xyBlkSTM 2 1 * xyBlkSTM 3 2) + -(xyBlkSTM 0 0 * xyBlkSTM 1 3 * xyBlkSTM 2 2 * xyBlkSTM 3 1) + -(xyBlkSTM 0 1 * xyBlkSTM 1 0 * xyBlkSTM 2 2 * xyBlkSTM 3 3) + (xyBlkSTM 0 1 * xyBlkSTM 1 0 * xyBlkSTM 2 3 * xyBlkSTM 3 2) + (xyBlkSTM 0 1 * xyBlkSTM 1 2 * xyBlkSTM 2 0 * xyBlkSTM 3 3) + -(xyBlkSTM 0 1 * xyBlkSTM 1 2 * xyBlkSTM 2 3 * xyBlkSTM 3 0) + -(xyBlkSTM 0 1 * xyBlkSTM 1 3 * xyBlkSTM 2 0 * xyBlkSTM 3 2)) ≤ (-200620779441792935 / 1000000000000000000000000 : ℝ) := by
    have hm := add_bounds s9.1 s9.2 t10.1 t10.2
    convert hm using 1 <;> first | ring | norm_num
  have s11 : (-228166178577666126 / 1000000000000000000000000 : ℝ) ≤ ((xyBlkSTM 0 0 * xyBlkSTM 1 1 * xyBlkSTM 2 2 * xyBlkSTM 3 3) + -(xyBlkSTM 0 0 * xyBlkSTM 1 1 * xyBlkSTM 2 3 * xyBlkSTM 3 2) + -(xyBlkSTM 0 0 * xyBlkSTM 1 2 * xyBlkSTM 2 1 * xyBlkSTM 3 3) + (xyBlkSTM 0 0 * xyBlkSTM 1 2 * xyBlkSTM 2 3 * xyBlkSTM 3 1) + (xyBlkSTM 0 0 * xyBlkSTM 1 3 * xyBlkSTM 2 1 * xyBlkSTM 3 2) + -(xyBlkSTM 0 0 * xyBlkSTM 1 3 * xyBlkSTM 2 2 * xyBlkSTM 3 1) + -(xyBlkSTM 0 1 * xyBlkSTM 1 0 * xyBlkSTM 2 2 * xyBlkSTM 3 3) + (xyBlkSTM 0 1 * xyBlkSTM 1 0 * xyBlkSTM 2 3 * xyBlkSTM 3 2) + (xyBlkSTM 0 1 * xyBlkSTM 1 2 * xyBlkSTM 2 0 * xyBlkSTM 3 3) + -(xyBlkSTM 0 1 * xyBlkSTM 1 2 * xyBlkSTM 2 3 * xyBlkSTM 3 0) + -(xyBlkSTM 0 1 * xyBlkSTM 1 3 * xyBlkSTM 2 0 * xyBlkSTM 3 2) + (xyBlkSTM 0 1 * xyBlkSTM 1 3 * xyBlkSTM 2 2 * xyBlkSTM 3 0)) ∧ ((xyBlkSTM 0 0 * xyBlkSTM 1 1 * xyBlkSTM 2 2 * xyBlkSTM 3 3) + -(xyBlkSTM 0 0 * xyBlkSTM 1 1 * xyBlkSTM 2 3 * xyBlkSTM 3 2) + -(xyBlkSTM 0 0 * xyBlkSTM 1 2 * xyBlkSTM 2 1 * xyBlkSTM 3 3) + (xyBlkSTM 0 0 * xyBlkSTM 1 2 * xyBlkSTM 2 3 * xyBlkSTM 3 1) + (xyBlkSTM 0 0 * xyBlkSTM 1 3 * xyBlkSTM 2 1 * xyBlkSTM 3 2) + -(xyBlkSTM 0 0 * xyBlkSTM 1 3 * xyBlkSTM 2 2 * xyBlkSTM 3 1) + -(xyBlkSTM 0 1 * xyBlkSTM 1 0 * xyBlkSTM 2 2 * xyBlkSTM 3 3) + (xyBlkSTM 0 1 * xyBlkSTM 1 0 * xyBlkSTM 2 3 * xyBlkSTM 3 2) + (xyBlkSTM 0 1 * xyBlkSTM 1 2 * xyBlkSTM 2 0 * xyBlkSTM 3 3) + -(xyBlkSTM 0 1 * xyBlkSTM 1 2 * xyBlkSTM 2 3 * xyBlkSTM 3 0) + -(xyBlkSTM 0 1 * xyBlkSTM 1 3 * xyBlkSTM 2 0 * xyBlkSTM 3 2) + (xyBlkSTM 0 1 * xyBlkSTM 1 3 * xyBlkSTM 2 2 * xyBlkSTM 3 0)) ≤ (-211298366099602115 / 1000000000000000000000000 : ℝ) := by
    have hm := add_bounds s10.1 s10.2 t11.1 t11.2
    convert hm using 1 <;> first | ring | norm_num
  have s12 : (-399792101115894606 / 1000000000000000000000000 : ℝ) ≤ ((xyBlkSTM 0 0 * xyBlkSTM 1 1 * xyBlkSTM 2 2 * xyBlkSTM 3 3) + -(xyBlkSTM 0 0 * xyBlkSTM 1 1 * xyBlkSTM 2 3 * xyBlkSTM 3 2) + -(xyBlkSTM 0 0 * xyBlkSTM 1 2 * xyBlkSTM 2 1 * xyBlkSTM 3 3) + (xyBlkSTM 0 0 * xyBlkSTM 1 2 * xyBlkSTM 2 3 * xyBlkSTM 3 1) + (xyBlkSTM 0 0 * xyBlkSTM 1 3 * xyBlkSTM 2 1 * xyBlkSTM 3 2) + -(xyBlkSTM 0 0 * xyBlkSTM 1 3 * xyBlkSTM 2 2 * xyBlkSTM 3 1) + -(xyBlkSTM 0 1 * xyBlkSTM 1 0 * xyBlkSTM 2 2 * xyBlkSTM 3 3) + (xyBlkSTM 0 1 * xyBlkSTM 1 0 * xyBlkSTM 2 3 * xyBlkSTM 3 2) + (xyBlkSTM 0 1 * xyBlkSTM 1 2 * xyBlkSTM 2 0 * xyBlkSTM 3 3) + -(xyBlkSTM 0 1 * xyBlkSTM 1 2 * xyBlkSTM 2 3 * xyBlkSTM 3 0) + -(xyBlkSTM 0 1 * xyBlkSTM 1 3 * xyBlkSTM 2 0 * xyBlkSTM 3 2) + (xyBlkSTM 0 1 * xyBlkSTM 1 3 * xyBlkSTM 2 2 * xyBlkSTM 3 0) + (xyBlkSTM 0 2 * xyBlkSTM 1 0 * xyBlkSTM 2 1 * xyBlkSTM 3 3)) ∧ ((xyBlkSTM 0 0 * xyBlkSTM 1 1 * xyBlkSTM 2 2 * xyBlkSTM 3 3) + -(xyBlkSTM 0 0 * xyBlkSTM 1 1 * xyBlkSTM 2 3 * xyBlkSTM 3 2) + -(xyBlkSTM 0 0 * xyBlkSTM 1 2 * xyBlkSTM 2 1 * xyBlkSTM 3 3) + (xyBlkSTM 0 0 * xyBlkSTM 1 2 * xyBlkSTM 2 3 * xyBlkSTM 3 1) + (xyBlkSTM 0 0 * xyBlkSTM 1 3 * xyBlkSTM 2 1 * xyBlkSTM 3 2) + -(xyBlkSTM 0 0 * xyBlkSTM 1 3 * xyBlkSTM 2 2 * xyBlkSTM 3 1) + -(xyBlkSTM 0 1 * xyBlkSTM 1 0 * xyBlkSTM 2 2 * xyBlkSTM 3 3) + (xyBlkSTM 0 1 * xyBlkSTM 1 0 * xyBlkSTM 2 3 * xyBlkSTM 3 2) + (xyBlkSTM 0 1 * xyBlkSTM 1 2 * xyBlkSTM 2 0 * xyBlkSTM 3 3) + -(xyBlkSTM 0 1 * xyBlkSTM 1 2 * xyBlkSTM 2 3 * xyBlkSTM 3 0) + -(xyBlkSTM 0 1 * xyBlkSTM 1 3 * xyBlkSTM 2 0 * xyBlkSTM 3 2) + (xyBlkSTM 0 1 * xyBlkSTM 1 3 * xyBlkSTM 2 2 * xyBlkSTM 3 0) + (xyBlkSTM 0 2 * xyBlkSTM 1 0 * xyBlkSTM 2 1 * xyBlkSTM 3 3)) ≤ (-377012189285607027 / 1000000000000000000000000 : ℝ) := by
    have hm := add_bounds s11.1 s11.2 t12.1 t12.2
    convert hm using 1 <;> first | ring | norm_num
  have s13 : (-395711838961246212 / 1000000000000000000000000 : ℝ) ≤ ((xyBlkSTM 0 0 * xyBlkSTM 1 1 * xyBlkSTM 2 2 * xyBlkSTM 3 3) + -(xyBlkSTM 0 0 * xyBlkSTM 1 1 * xyBlkSTM 2 3 * xyBlkSTM 3 2) + -(xyBlkSTM 0 0 * xyBlkSTM 1 2 * xyBlkSTM 2 1 * xyBlkSTM 3 3) + (xyBlkSTM 0 0 * xyBlkSTM 1 2 * xyBlkSTM 2 3 * xyBlkSTM 3 1) + (xyBlkSTM 0 0 * xyBlkSTM 1 3 * xyBlkSTM 2 1 * xyBlkSTM 3 2) + -(xyBlkSTM 0 0 * xyBlkSTM 1 3 * xyBlkSTM 2 2 * xyBlkSTM 3 1) + -(xyBlkSTM 0 1 * xyBlkSTM 1 0 * xyBlkSTM 2 2 * xyBlkSTM 3 3) + (xyBlkSTM 0 1 * xyBlkSTM 1 0 * xyBlkSTM 2 3 * xyBlkSTM 3 2) + (xyBlkSTM 0 1 * xyBlkSTM 1 2 * xyBlkSTM 2 0 * xyBlkSTM 3 3) + -(xyBlkSTM 0 1 * xyBlkSTM 1 2 * xyBlkSTM 2 3 * xyBlkSTM 3 0) + -(xyBlkSTM 0 1 * xyBlkSTM 1 3 * xyBlkSTM 2 0 * xyBlkSTM 3 2) + (xyBlkSTM 0 1 * xyBlkSTM 1 3 * xyBlkSTM 2 2 * xyBlkSTM 3 0) + (xyBlkSTM 0 2 * xyBlkSTM 1 0 * xyBlkSTM 2 1 * xyBlkSTM 3 3) + -(xyBlkSTM 0 2 * xyBlkSTM 1 0 * xyBlkSTM 2 3 * xyBlkSTM 3 1)) ∧ ((xyBlkSTM 0 0 * xyBlkSTM 1 1 * xyBlkSTM 2 2 * xyBlkSTM 3 3) + -(xyBlkSTM 0 0 * xyBlkSTM 1 1 * xyBlkSTM 2 3 * xyBlkSTM 3 2) + -(xyBlkSTM 0 0 * xyBlkSTM 1 2 * xyBlkSTM 2 1 * xyBlkSTM 3 3) + (xyBlkSTM 0 0 * xyBlkSTM 1 2 * xyBlkSTM 2 3 * xyBlkSTM 3 1) + (xyBlkSTM 0 0 * xyBlkSTM 1 3 * xyBlkSTM 2 1 * xyBlkSTM 3 2) + -(xyBlkSTM 0 0 * xyBlkSTM 1 3 * xyBlkSTM 2 2 * xyBlkSTM 3 1) + -(xyBlkSTM 0 1 * xyBlkSTM 1 0 * xyBlkSTM 2 2 * xyBlkSTM 3 3) + (xyBlkSTM 0 1 * xyBlkSTM 1 0 * xyBlkSTM 2 3 * xyBlkSTM 3 2) + (xyBlkSTM 0 1 * xyBlkSTM 1 2 * xyBlkSTM 2 0 * xyBlkSTM 3 3) + -(xyBlkSTM 0 1 * xyBlkSTM 1 2 * xyBlkSTM 2 3 * xyBlkSTM 3 0) + -(xyBlkSTM 0 1 * xyBlkSTM 1 3 * xyBlkSTM 2 0 * xyBlkSTM 3 2) + (xyBlkSTM 0 1 * xyBlkSTM 1 3 * xyBlkSTM 2 2 * xyBlkSTM 3 0) + (xyBlkSTM 0 2 * xyBlkSTM 1 0 * xyBlkSTM 2 1 * xyBlkSTM 3 3) + -(xyBlkSTM 0 2 * xyBlkSTM 1 0 * xyBlkSTM 2 3 * xyBlkSTM 3 1)) ≤ (-372648642629671371 / 1000000000000000000000000 : ℝ) := by
    have hm := add_bounds s12.1 s12.2 t13.1 t13.2
    convert hm using 1 <;> first | ring | norm_num
  have s14 : (-368650546031700372 / 1000000000000000000000000 : ℝ) ≤ ((xyBlkSTM 0 0 * xyBlkSTM 1 1 * xyBlkSTM 2 2 * xyBlkSTM 3 3) + -(xyBlkSTM 0 0 * xyBlkSTM 1 1 * xyBlkSTM 2 3 * xyBlkSTM 3 2) + -(xyBlkSTM 0 0 * xyBlkSTM 1 2 * xyBlkSTM 2 1 * xyBlkSTM 3 3) + (xyBlkSTM 0 0 * xyBlkSTM 1 2 * xyBlkSTM 2 3 * xyBlkSTM 3 1) + (xyBlkSTM 0 0 * xyBlkSTM 1 3 * xyBlkSTM 2 1 * xyBlkSTM 3 2) + -(xyBlkSTM 0 0 * xyBlkSTM 1 3 * xyBlkSTM 2 2 * xyBlkSTM 3 1) + -(xyBlkSTM 0 1 * xyBlkSTM 1 0 * xyBlkSTM 2 2 * xyBlkSTM 3 3) + (xyBlkSTM 0 1 * xyBlkSTM 1 0 * xyBlkSTM 2 3 * xyBlkSTM 3 2) + (xyBlkSTM 0 1 * xyBlkSTM 1 2 * xyBlkSTM 2 0 * xyBlkSTM 3 3) + -(xyBlkSTM 0 1 * xyBlkSTM 1 2 * xyBlkSTM 2 3 * xyBlkSTM 3 0) + -(xyBlkSTM 0 1 * xyBlkSTM 1 3 * xyBlkSTM 2 0 * xyBlkSTM 3 2) + (xyBlkSTM 0 1 * xyBlkSTM 1 3 * xyBlkSTM 2 2 * xyBlkSTM 3 0) + (xyBlkSTM 0 2 * xyBlkSTM 1 0 * xyBlkSTM 2 1 * xyBlkSTM 3 3) + -(xyBlkSTM 0 2 * xyBlkSTM 1 0 * xyBlkSTM 2 3 * xyBlkSTM 3 1) + -(xyBlkSTM 0 2 * xyBlkSTM 1 1 * xyBlkSTM 2 0 * xyBlkSTM 3 3)) ∧ ((xyBlkSTM 0 0 * xyBlkSTM 1 1 * xyBlkSTM 2 2 * xyBlkSTM 3 3) + -(xyBlkSTM 0 0 * xyBlkSTM 1 1 * xyBlkSTM 2 3 * xyBlkSTM 3 2) + -(xyBlkSTM 0 0 * xyBlkSTM 1 2 * xyBlkSTM 2 1 * xyBlkSTM 3 3) + (xyBlkSTM 0 0 * xyBlkSTM 1 2 * xyBlkSTM 2 3 * xyBlkSTM 3 1) + (xyBlkSTM 0 0 * xyBlkSTM 1 3 * xyBlkSTM 2 1 * xyBlkSTM 3 2) + -(xyBlkSTM 0 0 * xyBlkSTM 1 3 * xyBlkSTM 2 2 * xyBlkSTM 3 1) + -(xyBlkSTM 0 1 * xyBlkSTM 1 0 * xyBlkSTM 2 2 * xyBlkSTM 3 3) + (xyBlkSTM 0 1 * xyBlkSTM 1 0 * xyBlkSTM 2 3 * xyBlkSTM 3 2) + (xyBlkSTM 0 1 * xyBlkSTM 1 2 * xyBlkSTM 2 0 * xyBlkSTM 3 3) + -(xyBlkSTM 0 1 * xyBlkSTM 1 2 * xyBlkSTM 2 3 * xyBlkSTM 3 0) + -(xyBlkSTM 0 1 * xyBlkSTM 1 3 * xyBlkSTM 2 0 * xyBlkSTM 3 2) + (xyBlkSTM 0 1 * xyBlkSTM 1 3 * xyBlkSTM 2 2 * xyBlkSTM 3 0) + (xyBlkSTM 0 2 * xyBlkSTM 1 0 * xyBlkSTM 2 1 * xyBlkSTM 3 3) + -(xyBlkSTM 0 2 * xyBlkSTM 1 0 * xyBlkSTM 2 3 * xyBlkSTM 3 1) + -(xyBlkSTM 0 2 * xyBlkSTM 1 1 * xyBlkSTM 2 0 * xyBlkSTM 3 3)) ≤ (-343981538900720859 / 1000000000000000000000000 : ℝ) := by
    have hm := add_bounds s13.1 s13.2 t14.1 t14.2
    convert hm using 1 <;> first | ring | norm_num
  have s15 : (-380279290775136654 / 1000000000000000000000000 : ℝ) ≤ ((xyBlkSTM 0 0 * xyBlkSTM 1 1 * xyBlkSTM 2 2 * xyBlkSTM 3 3) + -(xyBlkSTM 0 0 * xyBlkSTM 1 1 * xyBlkSTM 2 3 * xyBlkSTM 3 2) + -(xyBlkSTM 0 0 * xyBlkSTM 1 2 * xyBlkSTM 2 1 * xyBlkSTM 3 3) + (xyBlkSTM 0 0 * xyBlkSTM 1 2 * xyBlkSTM 2 3 * xyBlkSTM 3 1) + (xyBlkSTM 0 0 * xyBlkSTM 1 3 * xyBlkSTM 2 1 * xyBlkSTM 3 2) + -(xyBlkSTM 0 0 * xyBlkSTM 1 3 * xyBlkSTM 2 2 * xyBlkSTM 3 1) + -(xyBlkSTM 0 1 * xyBlkSTM 1 0 * xyBlkSTM 2 2 * xyBlkSTM 3 3) + (xyBlkSTM 0 1 * xyBlkSTM 1 0 * xyBlkSTM 2 3 * xyBlkSTM 3 2) + (xyBlkSTM 0 1 * xyBlkSTM 1 2 * xyBlkSTM 2 0 * xyBlkSTM 3 3) + -(xyBlkSTM 0 1 * xyBlkSTM 1 2 * xyBlkSTM 2 3 * xyBlkSTM 3 0) + -(xyBlkSTM 0 1 * xyBlkSTM 1 3 * xyBlkSTM 2 0 * xyBlkSTM 3 2) + (xyBlkSTM 0 1 * xyBlkSTM 1 3 * xyBlkSTM 2 2 * xyBlkSTM 3 0) + (xyBlkSTM 0 2 * xyBlkSTM 1 0 * xyBlkSTM 2 1 * xyBlkSTM 3 3) + -(xyBlkSTM 0 2 * xyBlkSTM 1 0 * xyBlkSTM 2 3 * xyBlkSTM 3 1) + -(xyBlkSTM 0 2 * xyBlkSTM 1 1 * xyBlkSTM 2 0 * xyBlkSTM 3 3) + (xyBlkSTM 0 2 * xyBlkSTM 1 1 * xyBlkSTM 2 3 * xyBlkSTM 3 0)) ∧ ((xyBlkSTM 0 0 * xyBlkSTM 1 1 * xyBlkSTM 2 2 * xyBlkSTM 3 3) + -(xyBlkSTM 0 0 * xyBlkSTM 1 1 * xyBlkSTM 2 3 * xyBlkSTM 3 2) + -(xyBlkSTM 0 0 * xyBlkSTM 1 2 * xyBlkSTM 2 1 * xyBlkSTM 3 3) + (xyBlkSTM 0 0 * xyBlkSTM 1 2 * xyBlkSTM 2 3 * xyBlkSTM 3 1) + (xyBlkSTM 0 0 * xyBlkSTM 1 3 * xyBlkSTM 2 1 * xyBlkSTM 3 2) + -(xyBlkSTM 0 0 * xyBlkSTM 1 3 * xyBlkSTM 2 2 * xyBlkSTM 3 1) + -(xyBlkSTM 0 1 * xyBlkSTM 1 0 * xyBlkSTM 2 2 * xyBlkSTM 3 3) + (xyBlkSTM 0 1 * xyBlkSTM 1 0 * xyBlkSTM 2 3 * xyBlkSTM 3 2) + (xyBlkSTM 0 1 * xyBlkSTM 1 2 * xyBlkSTM 2 0 * xyBlkSTM 3 3) + -(xyBlkSTM 0 1 * xyBlkSTM 1 2 * xyBlkSTM 2 3 * xyBlkSTM 3 0) + -(xyBlkSTM 0 1 * xyBlkSTM 1 3 * xyBlkSTM 2 0 * xyBlkSTM 3 2) + (xyBlkSTM 0 1 * xyBlkSTM 1 3 * xyBlkSTM 2 2 * xyBlkSTM 3 0) + (xyBlkSTM 0 2 * xyBlkSTM 1 0 * xyBlkSTM 2 1 * xyBlkSTM 3 3) + -(xyBlkSTM 0 2 * xyBlkSTM 1 0 * xyBlkSTM 2 3 * xyBlkSTM 3 1) + -(xyBlkSTM 0 2 * xyBlkSTM 1 1 * xyBlkSTM 2 0 * xyBlkSTM 3 3) + (xyBlkSTM 0 2 * xyBlkSTM 1 1 * xyBlkSTM 2 3 * xyBlkSTM 3 0)) ≤ (-354876039975738639 / 1000000000000000000000000 : ℝ) := by
    have hm := add_bounds s14.1 s14.2 t15.1 t15.2
    convert hm using 1 <;> first | ring | norm_num
  have s16 : (-391015445199638286 / 1000000000000000000000000 : ℝ) ≤ ((xyBlkSTM 0 0 * xyBlkSTM 1 1 * xyBlkSTM 2 2 * xyBlkSTM 3 3) + -(xyBlkSTM 0 0 * xyBlkSTM 1 1 * xyBlkSTM 2 3 * xyBlkSTM 3 2) + -(xyBlkSTM 0 0 * xyBlkSTM 1 2 * xyBlkSTM 2 1 * xyBlkSTM 3 3) + (xyBlkSTM 0 0 * xyBlkSTM 1 2 * xyBlkSTM 2 3 * xyBlkSTM 3 1) + (xyBlkSTM 0 0 * xyBlkSTM 1 3 * xyBlkSTM 2 1 * xyBlkSTM 3 2) + -(xyBlkSTM 0 0 * xyBlkSTM 1 3 * xyBlkSTM 2 2 * xyBlkSTM 3 1) + -(xyBlkSTM 0 1 * xyBlkSTM 1 0 * xyBlkSTM 2 2 * xyBlkSTM 3 3) + (xyBlkSTM 0 1 * xyBlkSTM 1 0 * xyBlkSTM 2 3 * xyBlkSTM 3 2) + (xyBlkSTM 0 1 * xyBlkSTM 1 2 * xyBlkSTM 2 0 * xyBlkSTM 3 3) + -(xyBlkSTM 0 1 * xyBlkSTM 1 2 * xyBlkSTM 2 3 * xyBlkSTM 3 0) + -(xyBlkSTM 0 1 * xyBlkSTM 1 3 * xyBlkSTM 2 0 * xyBlkSTM 3 2) + (xyBlkSTM 0 1 * xyBlkSTM 1 3 * xyBlkSTM 2 2 * xyBlkSTM 3 0) + (xyBlkSTM 0 2 * xyBlkSTM 1 0 * xyBlkSTM 2 1 * xyBlkSTM 3 3) + -(xyBlkSTM 0 2 * xyBlkSTM 1 0 * xyBlkSTM 2 3 * xyBlkSTM 3 1) + -(xyBlkSTM 0 2 * xyBlkSTM 1 1 * xyBlkSTM 2 0 * xyBlkSTM 3 3) + (xyBlkSTM 0 2 * xyBlkSTM 1 1 * xyBlkSTM 2 3 * xyBlkSTM 3 0) + (xyBlkSTM 0 2 * xyBlkSTM 1 3 * xyBlkSTM 2 0 * xyBlkSTM 3 1)) ∧ ((xyBlkSTM 0 0 * xyBlkSTM 1 1 * xyBlkSTM 2 2 * xyBlkSTM 3 3) + -(xyBlkSTM 0 0 * xyBlkSTM 1 1 * xyBlkSTM 2 3 * xyBlkSTM 3 2) + -(xyBlkSTM 0 0 * xyBlkSTM 1 2 * xyBlkSTM 2 1 * xyBlkSTM 3 3) + (xyBlkSTM 0 0 * xyBlkSTM 1 2 * xyBlkSTM 2 3 * xyBlkSTM 3 1) + (xyBlkSTM 0 0 * xyBlkSTM 1 3 * xyBlkSTM 2 1 * xyBlkSTM 3 2) + -(xyBlkSTM 0 0 * xyBlkSTM 1 3 * xyBlkSTM 2 2 * xyBlkSTM 3 1) + -(xyBlkSTM 0 1 * xyBlkSTM 1 0 * xyBlkSTM 2 2 * xyBlkSTM 3 3) + (xyBlkSTM 0 1 * xyBlkSTM 1 0 * xyBlkSTM 2 3 * xyBlkSTM 3 2) + (xyBlkSTM 0 1 * xyBlkSTM 1 2 * xyBlkSTM 2 0 * xyBlkSTM 3 3) + -(xyBlkSTM 0 1 * xyBlkSTM 1 2 * xyBlkSTM 2 3 * xyBlkSTM 3 0) + -(xyBlkSTM 0 1 * xyBlkSTM 1 3 * xyBlkSTM 2 0 * xyBlkSTM 3 2) + (xyBlkSTM 0 1 * xyBlkSTM 1 3 * xyBlkSTM 2 2 * xyBlkSTM 3 0) + (xyBlkSTM 0 2 * xyBlkSTM 1 0 * xyBlkSTM 2 1 * xyBlkSTM 3 3) + -(xyBlkSTM 0 2 * xyBlkSTM 1 0 * xyBlkSTM 2 3 * xyBlkSTM 3 1) + -(xyBlkSTM 0 2 * xyBlkSTM 1 1 * xyBlkSTM 2 0 * xyBlkSTM 3 3) + (xyBlkSTM 0 2 * xyBlkSTM 1 1 * xyBlkSTM 2 3 * xyBlkSTM 3 0) + (xyBlkSTM 0 2 * xyBlkSTM 1 3 * xyBlkSTM 2 0 * xyBlkSTM 3 1)) ≤ (-364979961469609713 / 1000000000000000000000000 : ℝ) := by
    have hm := add_bounds s15.1 s15.2 t16.1 t16.2
    convert hm using 1 <;> first | ring | norm_num
  have s17 : (-225811871916532602 / 1000000000000000000000000 : ℝ) ≤ ((xyBlkSTM 0 0 * xyBlkSTM 1 1 * xyBlkSTM 2 2 * xyBlkSTM 3 3) + -(xyBlkSTM 0 0 * xyBlkSTM 1 1 * xyBlkSTM 2 3 * xyBlkSTM 3 2) + -(xyBlkSTM 0 0 * xyBlkSTM 1 2 * xyBlkSTM 2 1 * xyBlkSTM 3 3) + (xyBlkSTM 0 0 * xyBlkSTM 1 2 * xyBlkSTM 2 3 * xyBlkSTM 3 1) + (xyBlkSTM 0 0 * xyBlkSTM 1 3 * xyBlkSTM 2 1 * xyBlkSTM 3 2) + -(xyBlkSTM 0 0 * xyBlkSTM 1 3 * xyBlkSTM 2 2 * xyBlkSTM 3 1) + -(xyBlkSTM 0 1 * xyBlkSTM 1 0 * xyBlkSTM 2 2 * xyBlkSTM 3 3) + (xyBlkSTM 0 1 * xyBlkSTM 1 0 * xyBlkSTM 2 3 * xyBlkSTM 3 2) + (xyBlkSTM 0 1 * xyBlkSTM 1 2 * xyBlkSTM 2 0 * xyBlkSTM 3 3) + -(xyBlkSTM 0 1 * xyBlkSTM 1 2 * xyBlkSTM 2 3 * xyBlkSTM 3 0) + -(xyBlkSTM 0 1 * xyBlkSTM 1 3 * xyBlkSTM 2 0 * xyBlkSTM 3 2) + (xyBlkSTM 0 1 * xyBlkSTM 1 3 * xyBlkSTM 2 2 * xyBlkSTM 3 0) + (xyBlkSTM 0 2 * xyBlkSTM 1 0 * xyBlkSTM 2 1 * xyBlkSTM 3 3) + -(xyBlkSTM 0 2 * xyBlkSTM 1 0 * xyBlkSTM 2 3 * xyBlkSTM 3 1) + -(xyBlkSTM 0 2 * xyBlkSTM 1 1 * xyBlkSTM 2 0 * xyBlkSTM 3 3) + (xyBlkSTM 0 2 * xyBlkSTM 1 1 * xyBlkSTM 2 3 * xyBlkSTM 3 0) + (xyBlkSTM 0 2 * xyBlkSTM 1 3 * xyBlkSTM 2 0 * xyBlkSTM 3 1) + -(xyBlkSTM 0 2 * xyBlkSTM 1 3 * xyBlkSTM 2 1 * xyBlkSTM 3 0)) ∧ ((xyBlkSTM 0 0 * xyBlkSTM 1 1 * xyBlkSTM 2 2 * xyBlkSTM 3 3) + -(xyBlkSTM 0 0 * xyBlkSTM 1 1 * xyBlkSTM 2 3 * xyBlkSTM 3 2) + -(xyBlkSTM 0 0 * xyBlkSTM 1 2 * xyBlkSTM 2 1 * xyBlkSTM 3 3) + (xyBlkSTM 0 0 * xyBlkSTM 1 2 * xyBlkSTM 2 3 * xyBlkSTM 3 1) + (xyBlkSTM 0 0 * xyBlkSTM 1 3 * xyBlkSTM 2 1 * xyBlkSTM 3 2) + -(xyBlkSTM 0 0 * xyBlkSTM 1 3 * xyBlkSTM 2 2 * xyBlkSTM 3 1) + -(xyBlkSTM 0 1 * xyBlkSTM 1 0 * xyBlkSTM 2 2 * xyBlkSTM 3 3) + (xyBlkSTM 0 1 * xyBlkSTM 1 0 * xyBlkSTM 2 3 * xyBlkSTM 3 2) + (xyBlkSTM 0 1 * xyBlkSTM 1 2 * xyBlkSTM 2 0 * xyBlkSTM 3 3) + -(xyBlkSTM 0 1 * xyBlkSTM 1 2 * xyBlkSTM 2 3 * xyBlkSTM 3 0) + -(xyBlkSTM 0 1 * xyBlkSTM 1 3 * xyBlkSTM 2 0 * xyBlkSTM 3 2) + (xyBlkSTM 0 1 * xyBlkSTM 1 3 * xyBlkSTM 2 2 * xyBlkSTM 3 0) + (xyBlkSTM 0 2 * xyBlkSTM 1 0 * xyBlkSTM 2 1 * xyBlkSTM 3 3) + -(xyBlkSTM 0 2 * xyBlkSTM 1 0 * xyBlkSTM 2 3 * xyBlkSTM 3 1) + -(xyBlkSTM 0 2 * xyBlkSTM 1 1 * xyBlkSTM 2 0 * xyBlkSTM 3 3) + (xyBlkSTM 0 2 * xyBlkSTM 1 1 * xyBlkSTM 2 3 * xyBlkSTM 3 0) + (xyBlkSTM 0 2 * xyBlkSTM 1 3 * xyBlkSTM 2 0 * xyBlkSTM 3 1) + -(xyBlkSTM 0 2 * xyBlkSTM 1 3 * xyBlkSTM 2 1 * xyBlkSTM 3 0)) ≤ (-193686403540109553 / 1000000000000000000000000 : ℝ) := by
    have hm := add_bounds s16.1 s16.2 t17.1 t17.2
    convert hm using 1 <;> first | ring | norm_num
  have s18 : (-222634274223065470 / 1000000000000000000000000 : ℝ) ≤ ((xyBlkSTM 0 0 * xyBlkSTM 1 1 * xyBlkSTM 2 2 * xyBlkSTM 3 3) + -(xyBlkSTM 0 0 * xyBlkSTM 1 1 * xyBlkSTM 2 3 * xyBlkSTM 3 2) + -(xyBlkSTM 0 0 * xyBlkSTM 1 2 * xyBlkSTM 2 1 * xyBlkSTM 3 3) + (xyBlkSTM 0 0 * xyBlkSTM 1 2 * xyBlkSTM 2 3 * xyBlkSTM 3 1) + (xyBlkSTM 0 0 * xyBlkSTM 1 3 * xyBlkSTM 2 1 * xyBlkSTM 3 2) + -(xyBlkSTM 0 0 * xyBlkSTM 1 3 * xyBlkSTM 2 2 * xyBlkSTM 3 1) + -(xyBlkSTM 0 1 * xyBlkSTM 1 0 * xyBlkSTM 2 2 * xyBlkSTM 3 3) + (xyBlkSTM 0 1 * xyBlkSTM 1 0 * xyBlkSTM 2 3 * xyBlkSTM 3 2) + (xyBlkSTM 0 1 * xyBlkSTM 1 2 * xyBlkSTM 2 0 * xyBlkSTM 3 3) + -(xyBlkSTM 0 1 * xyBlkSTM 1 2 * xyBlkSTM 2 3 * xyBlkSTM 3 0) + -(xyBlkSTM 0 1 * xyBlkSTM 1 3 * xyBlkSTM 2 0 * xyBlkSTM 3 2) + (xyBlkSTM 0 1 * xyBlkSTM 1 3 * xyBlkSTM 2 2 * xyBlkSTM 3 0) + (xyBlkSTM 0 2 * xyBlkSTM 1 0 * xyBlkSTM 2 1 * xyBlkSTM 3 3) + -(xyBlkSTM 0 2 * xyBlkSTM 1 0 * xyBlkSTM 2 3 * xyBlkSTM 3 1) + -(xyBlkSTM 0 2 * xyBlkSTM 1 1 * xyBlkSTM 2 0 * xyBlkSTM 3 3) + (xyBlkSTM 0 2 * xyBlkSTM 1 1 * xyBlkSTM 2 3 * xyBlkSTM 3 0) + (xyBlkSTM 0 2 * xyBlkSTM 1 3 * xyBlkSTM 2 0 * xyBlkSTM 3 1) + -(xyBlkSTM 0 2 * xyBlkSTM 1 3 * xyBlkSTM 2 1 * xyBlkSTM 3 0) + -(xyBlkSTM 0 3 * xyBlkSTM 1 0 * xyBlkSTM 2 1 * xyBlkSTM 3 2)) ∧ ((xyBlkSTM 0 0 * xyBlkSTM 1 1 * xyBlkSTM 2 2 * xyBlkSTM 3 3) + -(xyBlkSTM 0 0 * xyBlkSTM 1 1 * xyBlkSTM 2 3 * xyBlkSTM 3 2) + -(xyBlkSTM 0 0 * xyBlkSTM 1 2 * xyBlkSTM 2 1 * xyBlkSTM 3 3) + (xyBlkSTM 0 0 * xyBlkSTM 1 2 * xyBlkSTM 2 3 * xyBlkSTM 3 1) + (xyBlkSTM 0 0 * xyBlkSTM 1 3 * xyBlkSTM 2 1 * xyBlkSTM 3 2) + -(xyBlkSTM 0 0 * xyBlkSTM 1 3 * xyBlkSTM 2 2 * xyBlkSTM 3 1) + -(xyBlkSTM 0 1 * xyBlkSTM 1 0 * xyBlkSTM 2 2 * xyBlkSTM 3 3) + (xyBlkSTM 0 1 * xyBlkSTM 1 0 * xyBlkSTM 2 3 * xyBlkSTM 3 2) + (xyBlkSTM 0 1 * xyBlkSTM 1 2 * xyBlkSTM 2 0 * xyBlkSTM 3 3) + -(xyBlkSTM 0 1 * xyBlkSTM 1 2 * xyBlkSTM 2 3 * xyBlkSTM 3 0) + -(xyBlkSTM 0 1 * xyBlkSTM 1 3 * xyBlkSTM 2 0 * xyBlkSTM 3 2) + (xyBlkSTM 0 1 * xyBlkSTM 1 3 * xyBlkSTM 2 2 * xyBlkSTM 3 0) + (xyBlkSTM 0 2 * xyBlkSTM 1 0 * xyBlkSTM 2 1 * xyBlkSTM 3 3) + -(xyBlkSTM 0 2 * xyBlkSTM 1 0 * xyBlkSTM 2 3 * xyBlkSTM 3 1) + -(xyBlkSTM 0 2 * xyBlkSTM 1 1 * xyBlkSTM 2 0 * xyBlkSTM 3 3) + (xyBlkSTM 0 2 * xyBlkSTM 1 1 * xyBlkSTM 2 3 * xyBlkSTM 3 0) + (xyBlkSTM 0 2 * xyBlkSTM 1 3 * xyBlkSTM 2 0 * xyBlkSTM 3 1) + -(xyBlkSTM 0 2 * xyBlkSTM 1 3 * xyBlkSTM 2 1 * xyBlkSTM 3 0) + -(xyBlkSTM 0 3 * xyBlkSTM 1 0 * xyBlkSTM 2 1 * xyBlkSTM 3 2)) ≤ (-189826173076935153 / 1000000000000000000000000 : ℝ) := by
    have hm := add_bounds s17.1 s17.2 t18.1 t18.2
    convert hm using 1 <;> first | ring | norm_num
  have s19 : (-218046631202679785 / 1000000000000000000000000 : ℝ) ≤ ((xyBlkSTM 0 0 * xyBlkSTM 1 1 * xyBlkSTM 2 2 * xyBlkSTM 3 3) + -(xyBlkSTM 0 0 * xyBlkSTM 1 1 * xyBlkSTM 2 3 * xyBlkSTM 3 2) + -(xyBlkSTM 0 0 * xyBlkSTM 1 2 * xyBlkSTM 2 1 * xyBlkSTM 3 3) + (xyBlkSTM 0 0 * xyBlkSTM 1 2 * xyBlkSTM 2 3 * xyBlkSTM 3 1) + (xyBlkSTM 0 0 * xyBlkSTM 1 3 * xyBlkSTM 2 1 * xyBlkSTM 3 2) + -(xyBlkSTM 0 0 * xyBlkSTM 1 3 * xyBlkSTM 2 2 * xyBlkSTM 3 1) + -(xyBlkSTM 0 1 * xyBlkSTM 1 0 * xyBlkSTM 2 2 * xyBlkSTM 3 3) + (xyBlkSTM 0 1 * xyBlkSTM 1 0 * xyBlkSTM 2 3 * xyBlkSTM 3 2) + (xyBlkSTM 0 1 * xyBlkSTM 1 2 * xyBlkSTM 2 0 * xyBlkSTM 3 3) + -(xyBlkSTM 0 1 * xyBlkSTM 1 2 * xyBlkSTM 2 3 * xyBlkSTM 3 0) + -(xyBlkSTM 0 1 * xyBlkSTM 1 3 * xyBlkSTM 2 0 * xyBlkSTM 3 2) + (xyBlkSTM 0 1 * xyBlkSTM 1 3 * xyBlkSTM 2 2 * xyBlkSTM 3 0) + (xyBlkSTM 0 2 * xyBlkSTM 1 0 * xyBlkSTM 2 1 * xyBlkSTM 3 3) + -(xyBlkSTM 0 2 * xyBlkSTM 1 0 * xyBlkSTM 2 3 * xyBlkSTM 3 1) + -(xyBlkSTM 0 2 * xyBlkSTM 1 1 * xyBlkSTM 2 0 * xyBlkSTM 3 3) + (xyBlkSTM 0 2 * xyBlkSTM 1 1 * xyBlkSTM 2 3 * xyBlkSTM 3 0) + (xyBlkSTM 0 2 * xyBlkSTM 1 3 * xyBlkSTM 2 0 * xyBlkSTM 3 1) + -(xyBlkSTM 0 2 * xyBlkSTM 1 3 * xyBlkSTM 2 1 * xyBlkSTM 3 0) + -(xyBlkSTM 0 3 * xyBlkSTM 1 0 * xyBlkSTM 2 1 * xyBlkSTM 3 2) + (xyBlkSTM 0 3 * xyBlkSTM 1 0 * xyBlkSTM 2 2 * xyBlkSTM 3 1)) ∧ ((xyBlkSTM 0 0 * xyBlkSTM 1 1 * xyBlkSTM 2 2 * xyBlkSTM 3 3) + -(xyBlkSTM 0 0 * xyBlkSTM 1 1 * xyBlkSTM 2 3 * xyBlkSTM 3 2) + -(xyBlkSTM 0 0 * xyBlkSTM 1 2 * xyBlkSTM 2 1 * xyBlkSTM 3 3) + (xyBlkSTM 0 0 * xyBlkSTM 1 2 * xyBlkSTM 2 3 * xyBlkSTM 3 1) + (xyBlkSTM 0 0 * xyBlkSTM 1 3 * xyBlkSTM 2 1 * xyBlkSTM 3 2) + -(xyBlkSTM 0 0 * xyBlkSTM 1 3 * xyBlkSTM 2 2 * xyBlkSTM 3 1) + -(xyBlkSTM 0 1 * xyBlkSTM 1 0 * xyBlkSTM 2 2 * xyBlkSTM 3 3) + (xyBlkSTM 0 1 * xyBlkSTM 1 0 * xyBlkSTM 2 3 * xyBlkSTM 3 2) + (xyBlkSTM 0 1 * xyBlkSTM 1 2 * xyBlkSTM 2 0 * xyBlkSTM 3 3) + -(xyBlkSTM 0 1 * xyBlkSTM 1 2 * xyBlkSTM 2 3 * xyBlkSTM 3 0) + -(xyBlkSTM 0 1 * xyBlkSTM 1 3 * xyBlkSTM 2 0 * xyBlkSTM 3 2) + (xyBlkSTM 0 1 * xyBlkSTM 1 3 * xyBlkSTM 2 2 * xyBlkSTM 3 0) + (xyBlkSTM 0 2 * xyBlkSTM 1 0 * xyBlkSTM 2 1 * xyBlkSTM 3 3) + -(xyBlkSTM 0 2 * xyBlkSTM 1 0 * xyBlkSTM 2 3 * xyBlkSTM 3 1) + -(xyBlkSTM 0 2 * xyBlkSTM 1 1 * xyBlkSTM 2 0 * xyBlkSTM 3 3) + (xyBlkSTM 0 2 * xyBlkSTM 1 1 * xyBlkSTM 2 3 * xyBlkSTM 3 0) + (xyBlkSTM 0 2 * xyBlkSTM 1 3 * xyBlkSTM 2 0 * xyBlkSTM 3 1) + -(xyBlkSTM 0 2 * xyBlkSTM 1 3 * xyBlkSTM 2 1 * xyBlkSTM 3 0) + -(xyBlkSTM 0 3 * xyBlkSTM 1 0 * xyBlkSTM 2 1 * xyBlkSTM 3 2) + (xyBlkSTM 0 3 * xyBlkSTM 1 0 * xyBlkSTM 2 2 * xyBlkSTM 3 1)) ≤ (-184085230474328025 / 1000000000000000000000000 : ℝ) := by
    have hm := add_bounds s18.1 s18.2 t19.1 t19.2
    convert hm using 1 <;> first | ring | norm_num
  have s20 : (-218691415076053145 / 1000000000000000000000000 : ℝ) ≤ ((xyBlkSTM 0 0 * xyBlkSTM 1 1 * xyBlkSTM 2 2 * xyBlkSTM 3 3) + -(xyBlkSTM 0 0 * xyBlkSTM 1 1 * xyBlkSTM 2 3 * xyBlkSTM 3 2) + -(xyBlkSTM 0 0 * xyBlkSTM 1 2 * xyBlkSTM 2 1 * xyBlkSTM 3 3) + (xyBlkSTM 0 0 * xyBlkSTM 1 2 * xyBlkSTM 2 3 * xyBlkSTM 3 1) + (xyBlkSTM 0 0 * xyBlkSTM 1 3 * xyBlkSTM 2 1 * xyBlkSTM 3 2) + -(xyBlkSTM 0 0 * xyBlkSTM 1 3 * xyBlkSTM 2 2 * xyBlkSTM 3 1) + -(xyBlkSTM 0 1 * xyBlkSTM 1 0 * xyBlkSTM 2 2 * xyBlkSTM 3 3) + (xyBlkSTM 0 1 * xyBlkSTM 1 0 * xyBlkSTM 2 3 * xyBlkSTM 3 2) + (xyBlkSTM 0 1 * xyBlkSTM 1 2 * xyBlkSTM 2 0 * xyBlkSTM 3 3) + -(xyBlkSTM 0 1 * xyBlkSTM 1 2 * xyBlkSTM 2 3 * xyBlkSTM 3 0) + -(xyBlkSTM 0 1 * xyBlkSTM 1 3 * xyBlkSTM 2 0 * xyBlkSTM 3 2) + (xyBlkSTM 0 1 * xyBlkSTM 1 3 * xyBlkSTM 2 2 * xyBlkSTM 3 0) + (xyBlkSTM 0 2 * xyBlkSTM 1 0 * xyBlkSTM 2 1 * xyBlkSTM 3 3) + -(xyBlkSTM 0 2 * xyBlkSTM 1 0 * xyBlkSTM 2 3 * xyBlkSTM 3 1) + -(xyBlkSTM 0 2 * xyBlkSTM 1 1 * xyBlkSTM 2 0 * xyBlkSTM 3 3) + (xyBlkSTM 0 2 * xyBlkSTM 1 1 * xyBlkSTM 2 3 * xyBlkSTM 3 0) + (xyBlkSTM 0 2 * xyBlkSTM 1 3 * xyBlkSTM 2 0 * xyBlkSTM 3 1) + -(xyBlkSTM 0 2 * xyBlkSTM 1 3 * xyBlkSTM 2 1 * xyBlkSTM 3 0) + -(xyBlkSTM 0 3 * xyBlkSTM 1 0 * xyBlkSTM 2 1 * xyBlkSTM 3 2) + (xyBlkSTM 0 3 * xyBlkSTM 1 0 * xyBlkSTM 2 2 * xyBlkSTM 3 1) + (xyBlkSTM 0 3 * xyBlkSTM 1 1 * xyBlkSTM 2 0 * xyBlkSTM 3 2)) ∧ ((xyBlkSTM 0 0 * xyBlkSTM 1 1 * xyBlkSTM 2 2 * xyBlkSTM 3 3) + -(xyBlkSTM 0 0 * xyBlkSTM 1 1 * xyBlkSTM 2 3 * xyBlkSTM 3 2) + -(xyBlkSTM 0 0 * xyBlkSTM 1 2 * xyBlkSTM 2 1 * xyBlkSTM 3 3) + (xyBlkSTM 0 0 * xyBlkSTM 1 2 * xyBlkSTM 2 3 * xyBlkSTM 3 1) + (xyBlkSTM 0 0 * xyBlkSTM 1 3 * xyBlkSTM 2 1 * xyBlkSTM 3 2) + -(xyBlkSTM 0 0 * xyBlkSTM 1 3 * xyBlkSTM 2 2 * xyBlkSTM 3 1) + -(xyBlkSTM 0 1 * xyBlkSTM 1 0 * xyBlkSTM 2 2 * xyBlkSTM 3 3) + (xyBlkSTM 0 1 * xyBlkSTM 1 0 * xyBlkSTM 2 3 * xyBlkSTM 3 2) + (xyBlkSTM 0 1 * xyBlkSTM 1 2 * xyBlkSTM 2 0 * xyBlkSTM 3 3) + -(xyBlkSTM 0 1 * xyBlkSTM 1 2 * xyBlkSTM 2 3 * xyBlkSTM 3 0) + -(xyBlkSTM 0 1 * xyBlkSTM 1 3 * xyBlkSTM 2 0 * xyBlkSTM 3 2) + (xyBlkSTM 0 1 * xyBlkSTM 1 3 * xyBlkSTM 2 2 * xyBlkSTM 3 0) + (xyBlkSTM 0 2 * xyBlkSTM 1 0 * xyBlkSTM 2 1 * xyBlkSTM 3 3) + -(xyBlkSTM 0 2 * xyBlkSTM 1 0 * xyBlkSTM 2 3 * xyBlkSTM 3 1) + -(xyBlkSTM 0 2 * xyBlkSTM 1 1 * xyBlkSTM 2 0 * xyBlkSTM 3 3) + (xyBlkSTM 0 2 * xyBlkSTM 1 1 * xyBlkSTM 2 3 * xyBlkSTM 3 0) + (xyBlkSTM 0 2 * xyBlkSTM 1 3 * xyBlkSTM 2 0 * xyBlkSTM 3 1) + -(xyBlkSTM 0 2 * xyBlkSTM 1 3 * xyBlkSTM 2 1 * xyBlkSTM 3 0) + -(xyBlkSTM 0 3 * xyBlkSTM 1 0 * xyBlkSTM 2 1 * xyBlkSTM 3 2) + (xyBlkSTM 0 3 * xyBlkSTM 1 0 * xyBlkSTM 2 2 * xyBlkSTM 3 1) + (xyBlkSTM 0 3 * xyBlkSTM 1 1 * xyBlkSTM 2 0 * xyBlkSTM 3 2)) ≤ (-184604136503661765 / 1000000000000000000000000 : ℝ) := by
    have hm := add_bounds s19.1 s19.2 t20.1 t20.2
    convert hm using 1 <;> first | ring | norm_num
  have s21 : (-233990886211906511 / 1000000000000000000000000 : ℝ) ≤ ((xyBlkSTM 0 0 * xyBlkSTM 1 1 * xyBlkSTM 2 2 * xyBlkSTM 3 3) + -(xyBlkSTM 0 0 * xyBlkSTM 1 1 * xyBlkSTM 2 3 * xyBlkSTM 3 2) + -(xyBlkSTM 0 0 * xyBlkSTM 1 2 * xyBlkSTM 2 1 * xyBlkSTM 3 3) + (xyBlkSTM 0 0 * xyBlkSTM 1 2 * xyBlkSTM 2 3 * xyBlkSTM 3 1) + (xyBlkSTM 0 0 * xyBlkSTM 1 3 * xyBlkSTM 2 1 * xyBlkSTM 3 2) + -(xyBlkSTM 0 0 * xyBlkSTM 1 3 * xyBlkSTM 2 2 * xyBlkSTM 3 1) + -(xyBlkSTM 0 1 * xyBlkSTM 1 0 * xyBlkSTM 2 2 * xyBlkSTM 3 3) + (xyBlkSTM 0 1 * xyBlkSTM 1 0 * xyBlkSTM 2 3 * xyBlkSTM 3 2) + (xyBlkSTM 0 1 * xyBlkSTM 1 2 * xyBlkSTM 2 0 * xyBlkSTM 3 3) + -(xyBlkSTM 0 1 * xyBlkSTM 1 2 * xyBlkSTM 2 3 * xyBlkSTM 3 0) + -(xyBlkSTM 0 1 * xyBlkSTM 1 3 * xyBlkSTM 2 0 * xyBlkSTM 3 2) + (xyBlkSTM 0 1 * xyBlkSTM 1 3 * xyBlkSTM 2 2 * xyBlkSTM 3 0) + (xyBlkSTM 0 2 * xyBlkSTM 1 0 * xyBlkSTM 2 1 * xyBlkSTM 3 3) + -(xyBlkSTM 0 2 * xyBlkSTM 1 0 * xyBlkSTM 2 3 * xyBlkSTM 3 1) + -(xyBlkSTM 0 2 * xyBlkSTM 1 1 * xyBlkSTM 2 0 * xyBlkSTM 3 3) + (xyBlkSTM 0 2 * xyBlkSTM 1 1 * xyBlkSTM 2 3 * xyBlkSTM 3 0) + (xyBlkSTM 0 2 * xyBlkSTM 1 3 * xyBlkSTM 2 0 * xyBlkSTM 3 1) + -(xyBlkSTM 0 2 * xyBlkSTM 1 3 * xyBlkSTM 2 1 * xyBlkSTM 3 0) + -(xyBlkSTM 0 3 * xyBlkSTM 1 0 * xyBlkSTM 2 1 * xyBlkSTM 3 2) + (xyBlkSTM 0 3 * xyBlkSTM 1 0 * xyBlkSTM 2 2 * xyBlkSTM 3 1) + (xyBlkSTM 0 3 * xyBlkSTM 1 1 * xyBlkSTM 2 0 * xyBlkSTM 3 2) + -(xyBlkSTM 0 3 * xyBlkSTM 1 1 * xyBlkSTM 2 2 * xyBlkSTM 3 0)) ∧ ((xyBlkSTM 0 0 * xyBlkSTM 1 1 * xyBlkSTM 2 2 * xyBlkSTM 3 3) + -(xyBlkSTM 0 0 * xyBlkSTM 1 1 * xyBlkSTM 2 3 * xyBlkSTM 3 2) + -(xyBlkSTM 0 0 * xyBlkSTM 1 2 * xyBlkSTM 2 1 * xyBlkSTM 3 3) + (xyBlkSTM 0 0 * xyBlkSTM 1 2 * xyBlkSTM 2 3 * xyBlkSTM 3 1) + (xyBlkSTM 0 0 * xyBlkSTM 1 3 * xyBlkSTM 2 1 * xyBlkSTM 3 2) + -(xyBlkSTM 0 0 * xyBlkSTM 1 3 * xyBlkSTM 2 2 * xyBlkSTM 3 1) + -(xyBlkSTM 0 1 * xyBlkSTM 1 0 * xyBlkSTM 2 2 * xyBlkSTM 3 3) + (xyBlkSTM 0 1 * xyBlkSTM 1 0 * xyBlkSTM 2 3 * xyBlkSTM 3 2) + (xyBlkSTM 0 1 * xyBlkSTM 1 2 * xyBlkSTM 2 0 * xyBlkSTM 3 3) + -(xyBlkSTM 0 1 * xyBlkSTM 1 2 * xyBlkSTM 2 3 * xyBlkSTM 3 0) + -(xyBlkSTM 0 1 * xyBlkSTM 1 3 * xyBlkSTM 2 0 * xyBlkSTM 3 2) + (xyBlkSTM 0 1 * xyBlkSTM 1 3 * xyBlkSTM 2 2 * xyBlkSTM 3 0) + (xyBlkSTM 0 2 * xyBlkSTM 1 0 * xyBlkSTM 2 1 * xyBlkSTM 3 3) + -(xyBlkSTM 0 2 * xyBlkSTM 1 0 * xyBlkSTM 2 3 * xyBlkSTM 3 1) + -(xyBlkSTM 0 2 * xyBlkSTM 1 1 * xyBlkSTM 2 0 * xyBlkSTM 3 3) + (xyBlkSTM 0 2 * xyBlkSTM 1 1 * xyBlkSTM 2 3 * xyBlkSTM 3 0) + (xyBlkSTM 0 2 * xyBlkSTM 1 3 * xyBlkSTM 2 0 * xyBlkSTM 3 1) + -(xyBlkSTM 0 2 * xyBlkSTM 1 3 * xyBlkSTM 2 1 * xyBlkSTM 3 0) + -(xyBlkSTM 0 3 * xyBlkSTM 1 0 * xyBlkSTM 2 1 * xyBlkSTM 3 2) + (xyBlkSTM 0 3 * xyBlkSTM 1 0 * xyBlkSTM 2 2 * xyBlkSTM 3 1) + (xyBlkSTM 0 3 * xyBlkSTM 1 1 * xyBlkSTM 2 0 * xyBlkSTM 3 2) + -(xyBlkSTM 0 3 * xyBlkSTM 1 1 * xyBlkSTM 2 2 * xyBlkSTM 3 0)) ≤ (-196853369499745215 / 1000000000000000000000000 : ℝ) := by
    have hm := add_bounds s20.1 s20.2 t21.1 t21.2
    convert hm using 1 <;> first | ring | norm_num
  have s22 : (-273916798998205547 / 1000000000000000000000000 : ℝ) ≤ ((xyBlkSTM 0 0 * xyBlkSTM 1 1 * xyBlkSTM 2 2 * xyBlkSTM 3 3) + -(xyBlkSTM 0 0 * xyBlkSTM 1 1 * xyBlkSTM 2 3 * xyBlkSTM 3 2) + -(xyBlkSTM 0 0 * xyBlkSTM 1 2 * xyBlkSTM 2 1 * xyBlkSTM 3 3) + (xyBlkSTM 0 0 * xyBlkSTM 1 2 * xyBlkSTM 2 3 * xyBlkSTM 3 1) + (xyBlkSTM 0 0 * xyBlkSTM 1 3 * xyBlkSTM 2 1 * xyBlkSTM 3 2) + -(xyBlkSTM 0 0 * xyBlkSTM 1 3 * xyBlkSTM 2 2 * xyBlkSTM 3 1) + -(xyBlkSTM 0 1 * xyBlkSTM 1 0 * xyBlkSTM 2 2 * xyBlkSTM 3 3) + (xyBlkSTM 0 1 * xyBlkSTM 1 0 * xyBlkSTM 2 3 * xyBlkSTM 3 2) + (xyBlkSTM 0 1 * xyBlkSTM 1 2 * xyBlkSTM 2 0 * xyBlkSTM 3 3) + -(xyBlkSTM 0 1 * xyBlkSTM 1 2 * xyBlkSTM 2 3 * xyBlkSTM 3 0) + -(xyBlkSTM 0 1 * xyBlkSTM 1 3 * xyBlkSTM 2 0 * xyBlkSTM 3 2) + (xyBlkSTM 0 1 * xyBlkSTM 1 3 * xyBlkSTM 2 2 * xyBlkSTM 3 0) + (xyBlkSTM 0 2 * xyBlkSTM 1 0 * xyBlkSTM 2 1 * xyBlkSTM 3 3) + -(xyBlkSTM 0 2 * xyBlkSTM 1 0 * xyBlkSTM 2 3 * xyBlkSTM 3 1) + -(xyBlkSTM 0 2 * xyBlkSTM 1 1 * xyBlkSTM 2 0 * xyBlkSTM 3 3) + (xyBlkSTM 0 2 * xyBlkSTM 1 1 * xyBlkSTM 2 3 * xyBlkSTM 3 0) + (xyBlkSTM 0 2 * xyBlkSTM 1 3 * xyBlkSTM 2 0 * xyBlkSTM 3 1) + -(xyBlkSTM 0 2 * xyBlkSTM 1 3 * xyBlkSTM 2 1 * xyBlkSTM 3 0) + -(xyBlkSTM 0 3 * xyBlkSTM 1 0 * xyBlkSTM 2 1 * xyBlkSTM 3 2) + (xyBlkSTM 0 3 * xyBlkSTM 1 0 * xyBlkSTM 2 2 * xyBlkSTM 3 1) + (xyBlkSTM 0 3 * xyBlkSTM 1 1 * xyBlkSTM 2 0 * xyBlkSTM 3 2) + -(xyBlkSTM 0 3 * xyBlkSTM 1 1 * xyBlkSTM 2 2 * xyBlkSTM 3 0) + -(xyBlkSTM 0 3 * xyBlkSTM 1 2 * xyBlkSTM 2 0 * xyBlkSTM 3 1)) ∧ ((xyBlkSTM 0 0 * xyBlkSTM 1 1 * xyBlkSTM 2 2 * xyBlkSTM 3 3) + -(xyBlkSTM 0 0 * xyBlkSTM 1 1 * xyBlkSTM 2 3 * xyBlkSTM 3 2) + -(xyBlkSTM 0 0 * xyBlkSTM 1 2 * xyBlkSTM 2 1 * xyBlkSTM 3 3) + (xyBlkSTM 0 0 * xyBlkSTM 1 2 * xyBlkSTM 2 3 * xyBlkSTM 3 1) + (xyBlkSTM 0 0 * xyBlkSTM 1 3 * xyBlkSTM 2 1 * xyBlkSTM 3 2) + -(xyBlkSTM 0 0 * xyBlkSTM 1 3 * xyBlkSTM 2 2 * xyBlkSTM 3 1) + -(xyBlkSTM 0 1 * xyBlkSTM 1 0 * xyBlkSTM 2 2 * xyBlkSTM 3 3) + (xyBlkSTM 0 1 * xyBlkSTM 1 0 * xyBlkSTM 2 3 * xyBlkSTM 3 2) + (xyBlkSTM 0 1 * xyBlkSTM 1 2 * xyBlkSTM 2 0 * xyBlkSTM 3 3) + -(xyBlkSTM 0 1 * xyBlkSTM 1 2 * xyBlkSTM 2 3 * xyBlkSTM 3 0) + -(xyBlkSTM 0 1 * xyBlkSTM 1 3 * xyBlkSTM 2 0 * xyBlkSTM 3 2) + (xyBlkSTM 0 1 * xyBlkSTM 1 3 * xyBlkSTM 2 2 * xyBlkSTM 3 0) + (xyBlkSTM 0 2 * xyBlkSTM 1 0 * xyBlkSTM 2 1 * xyBlkSTM 3 3) + -(xyBlkSTM 0 2 * xyBlkSTM 1 0 * xyBlkSTM 2 3 * xyBlkSTM 3 1) + -(xyBlkSTM 0 2 * xyBlkSTM 1 1 * xyBlkSTM 2 0 * xyBlkSTM 3 3) + (xyBlkSTM 0 2 * xyBlkSTM 1 1 * xyBlkSTM 2 3 * xyBlkSTM 3 0) + (xyBlkSTM 0 2 * xyBlkSTM 1 3 * xyBlkSTM 2 0 * xyBlkSTM 3 1) + -(xyBlkSTM 0 2 * xyBlkSTM 1 3 * xyBlkSTM 2 1 * xyBlkSTM 3 0) + -(xyBlkSTM 0 3 * xyBlkSTM 1 0 * xyBlkSTM 2 1 * xyBlkSTM 3 2) + (xyBlkSTM 0 3 * xyBlkSTM 1 0 * xyBlkSTM 2 2 * xyBlkSTM 3 1) + (xyBlkSTM 0 3 * xyBlkSTM 1 1 * xyBlkSTM 2 0 * xyBlkSTM 3 2) + -(xyBlkSTM 0 3 * xyBlkSTM 1 1 * xyBlkSTM 2 2 * xyBlkSTM 3 0) + -(xyBlkSTM 0 3 * xyBlkSTM 1 2 * xyBlkSTM 2 0 * xyBlkSTM 3 1)) ≤ (-235356998779346805 / 1000000000000000000000000 : ℝ) := by
    have hm := add_bounds s21.1 s21.2 t22.1 t22.2
    convert hm using 1 <;> first | ring | norm_num
  have s23 : (355634523744817393 / 1000000000000000000000000 : ℝ) ≤ ((xyBlkSTM 0 0 * xyBlkSTM 1 1 * xyBlkSTM 2 2 * xyBlkSTM 3 3) + -(xyBlkSTM 0 0 * xyBlkSTM 1 1 * xyBlkSTM 2 3 * xyBlkSTM 3 2) + -(xyBlkSTM 0 0 * xyBlkSTM 1 2 * xyBlkSTM 2 1 * xyBlkSTM 3 3) + (xyBlkSTM 0 0 * xyBlkSTM 1 2 * xyBlkSTM 2 3 * xyBlkSTM 3 1) + (xyBlkSTM 0 0 * xyBlkSTM 1 3 * xyBlkSTM 2 1 * xyBlkSTM 3 2) + -(xyBlkSTM 0 0 * xyBlkSTM 1 3 * xyBlkSTM 2 2 * xyBlkSTM 3 1) + -(xyBlkSTM 0 1 * xyBlkSTM 1 0 * xyBlkSTM 2 2 * xyBlkSTM 3 3) + (xyBlkSTM 0 1 * xyBlkSTM 1 0 * xyBlkSTM 2 3 * xyBlkSTM 3 2) + (xyBlkSTM 0 1 * xyBlkSTM 1 2 * xyBlkSTM 2 0 * xyBlkSTM 3 3) + -(xyBlkSTM 0 1 * xyBlkSTM 1 2 * xyBlkSTM 2 3 * xyBlkSTM 3 0) + -(xyBlkSTM 0 1 * xyBlkSTM 1 3 * xyBlkSTM 2 0 * xyBlkSTM 3 2) + (xyBlkSTM 0 1 * xyBlkSTM 1 3 * xyBlkSTM 2 2 * xyBlkSTM 3 0) + (xyBlkSTM 0 2 * xyBlkSTM 1 0 * xyBlkSTM 2 1 * xyBlkSTM 3 3) + -(xyBlkSTM 0 2 * xyBlkSTM 1 0 * xyBlkSTM 2 3 * xyBlkSTM 3 1) + -(xyBlkSTM 0 2 * xyBlkSTM 1 1 * xyBlkSTM 2 0 * xyBlkSTM 3 3) + (xyBlkSTM 0 2 * xyBlkSTM 1 1 * xyBlkSTM 2 3 * xyBlkSTM 3 0) + (xyBlkSTM 0 2 * xyBlkSTM 1 3 * xyBlkSTM 2 0 * xyBlkSTM 3 1) + -(xyBlkSTM 0 2 * xyBlkSTM 1 3 * xyBlkSTM 2 1 * xyBlkSTM 3 0) + -(xyBlkSTM 0 3 * xyBlkSTM 1 0 * xyBlkSTM 2 1 * xyBlkSTM 3 2) + (xyBlkSTM 0 3 * xyBlkSTM 1 0 * xyBlkSTM 2 2 * xyBlkSTM 3 1) + (xyBlkSTM 0 3 * xyBlkSTM 1 1 * xyBlkSTM 2 0 * xyBlkSTM 3 2) + -(xyBlkSTM 0 3 * xyBlkSTM 1 1 * xyBlkSTM 2 2 * xyBlkSTM 3 0) + -(xyBlkSTM 0 3 * xyBlkSTM 1 2 * xyBlkSTM 2 0 * xyBlkSTM 3 1) + (xyBlkSTM 0 3 * xyBlkSTM 1 2 * xyBlkSTM 2 1 * xyBlkSTM 3 0)) ∧ ((xyBlkSTM 0 0 * xyBlkSTM 1 1 * xyBlkSTM 2 2 * xyBlkSTM 3 3) + -(xyBlkSTM 0 0 * xyBlkSTM 1 1 * xyBlkSTM 2 3 * xyBlkSTM 3 2) + -(xyBlkSTM 0 0 * xyBlkSTM 1 2 * xyBlkSTM 2 1 * xyBlkSTM 3 3) + (xyBlkSTM 0 0 * xyBlkSTM 1 2 * xyBlkSTM 2 3 * xyBlkSTM 3 1) + (xyBlkSTM 0 0 * xyBlkSTM 1 3 * xyBlkSTM 2 1 * xyBlkSTM 3 2) + -(xyBlkSTM 0 0 * xyBlkSTM 1 3 * xyBlkSTM 2 2 * xyBlkSTM 3 1) + -(xyBlkSTM 0 1 * xyBlkSTM 1 0 * xyBlkSTM 2 2 * xyBlkSTM 3 3) + (xyBlkSTM 0 1 * xyBlkSTM 1 0 * xyBlkSTM 2 3 * xyBlkSTM 3 2) + (xyBlkSTM 0 1 * xyBlkSTM 1 2 * xyBlkSTM 2 0 * xyBlkSTM 3 3) + -(xyBlkSTM 0 1 * xyBlkSTM 1 2 * xyBlkSTM 2 3 * xyBlkSTM 3 0) + -(xyBlkSTM 0 1 * xyBlkSTM 1 3 * xyBlkSTM 2 0 * xyBlkSTM 3 2) + (xyBlkSTM 0 1 * xyBlkSTM 1 3 * xyBlkSTM 2 2 * xyBlkSTM 3 0) + (xyBlkSTM 0 2 * xyBlkSTM 1 0 * xyBlkSTM 2 1 * xyBlkSTM 3 3) + -(xyBlkSTM 0 2 * xyBlkSTM 1 0 * xyBlkSTM 2 3 * xyBlkSTM 3 1) + -(xyBlkSTM 0 2 * xyBlkSTM 1 1 * xyBlkSTM 2 0 * xyBlkSTM 3 3) + (xyBlkSTM 0 2 * xyBlkSTM 1 1 * xyBlkSTM 2 3 * xyBlkSTM 3 0) + (xyBlkSTM 0 2 * xyBlkSTM 1 3 * xyBlkSTM 2 0 * xyBlkSTM 3 1) + -(xyBlkSTM 0 2 * xyBlkSTM 1 3 * xyBlkSTM 2 1 * xyBlkSTM 3 0) + -(xyBlkSTM 0 3 * xyBlkSTM 1 0 * xyBlkSTM 2 1 * xyBlkSTM 3 2) + (xyBlkSTM 0 3 * xyBlkSTM 1 0 * xyBlkSTM 2 2 * xyBlkSTM 3 1) + (xyBlkSTM 0 3 * xyBlkSTM 1 1 * xyBlkSTM 2 0 * xyBlkSTM 3 2) + -(xyBlkSTM 0 3 * xyBlkSTM 1 1 * xyBlkSTM 2 2 * xyBlkSTM 3 0) + -(xyBlkSTM 0 3 * xyBlkSTM 1 2 * xyBlkSTM 2 0 * xyBlkSTM 3 1) + (xyBlkSTM 0 3 * xyBlkSTM 1 2 * xyBlkSTM 2 1 * xyBlkSTM 3 0)) ≤ (401654298221026875 / 1000000000000000000000000 : ℝ) := by
    have hm := add_bounds s22.1 s22.2 t23.1 t23.2
    convert hm using 1 <;> first | ring | norm_num
  have hlo : (355 / 1000000000 : ℝ) ≤ (355634523744817393 / 1000000000000000000000000 : ℝ) := by norm_num
  have hhi : (401654298221026875 / 1000000000000000000000000 : ℝ) ≤ (402 / 1000000000 : ℝ) := by norm_num
  constructor
  · linarith [hlo, s23.1]
  · linarith [hhi, s23.2]

lemma xyBlkSTM_det_pos : (0 : ℝ) < xyBlkSTM.det := by
  have h := xyBlkSTM_det_bounds
  have : (0 : ℝ) < 355 / 1000000000 := by norm_num
  exact this.trans_le h.1

lemma xyBlkSTM_det_ne : xyBlkSTM.det ≠ 0 := xyBlkSTM_det_pos.ne'

lemma xyBlk_det_ne : xyBlk.det ≠ 0 := by
  rw [xyBlk_eq_xyBlkSTM]; exact xyBlkSTM_det_ne

lemma erOf_ofLp2 (t : ℝ) : (erOf t).ofLp 2 = 0 := by
  simp [erOf, ofLp_ofCoords]

lemma ethOf_ofLp2 (t : ℝ) : (ethOf t).ofLp 2 = 0 := by
  simp [ethOf, ofLp_ofCoords]

lemma stmInertial_ofLp2 (t dx dy dvx dvy : ℝ) :
    (stmInertial t dx dy dvx dvy).ofLp 2 = 0 := by
  simp [stmInertial, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul,
    erOf_ofLp2, ethOf_ofLp2]

lemma stmCol_ofLp2 (j : Fin 4) (t : ℝ) : (stmCol j t).ofLp 2 = 0 := by
  fin_cases j <;> simp [stmCol, stmInertial_ofLp2]

lemma dlosSTM_ofLp2 (t : ℝ) (dr : Vec) (hz : dr.ofLp 2 = 0) :
    (dlosSTM t dr).ofLp 2 = 0 := by
  simp [dlosSTM, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul, uStar_ofLp2, hz]

lemma dlosCol_ofLp2 (j : Fin 4) (t : ℝ) : (dlosCol j t).ofLp 2 = 0 :=
  dlosSTM_ofLp2 t (stmCol j t) (stmCol_ofLp2 j t)

lemma secondDiff_dlosCol_ofLp2 (j : Fin 4) (h : ℝ) :
    (secondDiff (fun t => dlosCol j t) h).ofLp 2 = 0 := by
  simp [secondDiff, PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul,
    dlosCol_ofLp2]

lemma fderiv_sdCart_inPlane_z (j : Fin 4) :
    fderiv ℝ sdCart sStar (Pi.single (inPlane j) 1) 2 = 0 ∧
      fderiv ℝ sdCart sStar (Pi.single (inPlane j) 1) 5 = 0 := by
  rw [fderiv_sdCart_inPlane]
  constructor
  · change (secondDiff (fun t => dlosCol j t) hSD1).ofLp 2 = 0
    exact secondDiff_dlosCol_ofLp2 j hSD1
  · change (secondDiff (fun t => dlosCol j t) hSD2).ofLp 2 = 0
    exact secondDiff_dlosCol_ofLp2 j hSD2

def zOut : Fin 2 → Fin 6 := ![2, 5]

def zIn : Fin 2 → Fin 6 := ![2, 5]

lemma fderiv_sdCart_zIn (j : Fin 2) :
    fderiv ℝ sdCart sStar (Pi.single (zIn j) 1)
      = match j with
        | ⟨0, _⟩ => ![0, 0, deltaPhi phiZ hSD1, 0, 0, deltaPhi phiZ hSD2]
        | ⟨1, _⟩ => ![0, 0, deltaPhi phiVz hSD1, 0, 0, deltaPhi phiVz hSD2] := by
  fin_cases j
  · simpa [zIn] using fderiv_sdCart_ez'
  · simpa [zIn] using fderiv_sdCart_evz'

lemma fderiv_sdCart_ez_xy :
    fderiv ℝ sdCart sStar (Pi.single 2 1) 0 = 0 ∧
      fderiv ℝ sdCart sStar (Pi.single 2 1) 1 = 0 ∧
      fderiv ℝ sdCart sStar (Pi.single 2 1) 3 = 0 ∧
      fderiv ℝ sdCart sStar (Pi.single 2 1) 4 = 0 := by
  simp [fderiv_sdCart_ez']

lemma fderiv_sdCart_evz_xy :
    fderiv ℝ sdCart sStar (Pi.single 5 1) 0 = 0 ∧
      fderiv ℝ sdCart sStar (Pi.single 5 1) 1 = 0 ∧
      fderiv ℝ sdCart sStar (Pi.single 5 1) 3 = 0 ∧
      fderiv ℝ sdCart sStar (Pi.single 5 1) 4 = 0 := by
  simp [fderiv_sdCart_evz']

lemma fderiv_sdCart_z_xy (j : Fin 2) :
    fderiv ℝ sdCart sStar (Pi.single (zIn j) 1) 0 = 0 ∧
      fderiv ℝ sdCart sStar (Pi.single (zIn j) 1) 1 = 0 ∧
      fderiv ℝ sdCart sStar (Pi.single (zIn j) 1) 3 = 0 ∧
      fderiv ℝ sdCart sStar (Pi.single (zIn j) 1) 4 = 0 := by
  rcases j with ⟨n, hn⟩
  interval_cases n
  · simpa [zIn] using fderiv_sdCart_ez_xy
  · simpa [zIn] using fderiv_sdCart_evz_xy

lemma fderiv_sdCart_apply_eq_sum (v : Fin 6 → ℝ) :
    fderiv ℝ sdCart sStar v =
      v 0 • fderiv ℝ sdCart sStar (Pi.single 0 1)
        + v 1 • fderiv ℝ sdCart sStar (Pi.single 1 1)
        + v 2 • fderiv ℝ sdCart sStar (Pi.single 2 1)
        + v 3 • fderiv ℝ sdCart sStar (Pi.single 3 1)
        + v 4 • fderiv ℝ sdCart sStar (Pi.single 4 1)
        + v 5 • fderiv ℝ sdCart sStar (Pi.single 5 1) := by
  conv_lhs => rw [eq_sum_single v]
  simp only [map_sum, map_smul]
  simp [Fin.sum_univ_six]

lemma fderiv_sdCart_ez_inPlaneOut (i : Fin 4) :
    fderiv ℝ sdCart sStar (Pi.single 2 1) (inPlaneOut i) = 0 := by
  rcases i with ⟨n, hn⟩
  interval_cases n <;> simp [inPlaneOut, fderiv_sdCart_ez_xy]

lemma fderiv_sdCart_evz_inPlaneOut (i : Fin 4) :
    fderiv ℝ sdCart sStar (Pi.single 5 1) (inPlaneOut i) = 0 := by
  rcases i with ⟨n, hn⟩
  interval_cases n <;> simp [inPlaneOut, fderiv_sdCart_evz_xy]

lemma fderiv_sdCart_inPlaneOut_eq_xy (v : Fin 6 → ℝ) (i : Fin 4) :
    fderiv ℝ sdCart sStar v (inPlaneOut i)
      = (xyBlk *ᵥ ![v 0, v 1, v 3, v 4]) i := by
  have hz0' := fderiv_sdCart_ez_inPlaneOut i
  have hz1' := fderiv_sdCart_evz_inPlaneOut i
  rw [fderiv_sdCart_apply_eq_sum]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hz0', hz1',
    mul_zero, add_zero, zero_add]
  rcases i with ⟨n, hn⟩
  interval_cases n <;>
    simp [xyBlk, Matrix.mulVec, dotProduct, Fin.sum_univ_four, inPlane, inPlaneOut,
      Matrix.of_apply] <;> ring

lemma fderiv_sdCart_inPlane_zOut (j : Fin 4) (i : Fin 2) :
    fderiv ℝ sdCart sStar (Pi.single (inPlane j) 1) (zOut i) = 0 := by
  have hp := fderiv_sdCart_inPlane_z j
  rcases i with ⟨n, hn⟩
  interval_cases n <;> simp [zOut, hp]

lemma zBlk_mulVec (v2 v5 : ℝ) :
    zBlk *ᵥ ![v2, v5] =
      ![v2 * deltaPhi phiZ hSD1 + v5 * deltaPhi phiVz hSD1,
        v2 * deltaPhi phiZ hSD2 + v5 * deltaPhi phiVz hSD2] := by
  ext i
  rcases i with ⟨n, hn⟩
  interval_cases n <;>
    (simp [zBlk, Matrix.mulVec, dotProduct, Fin.sum_univ_two]; ring)

lemma fderiv_sdCart_coord2 (v : Fin 6 → ℝ) :
    fderiv ℝ sdCart sStar v 2 =
      v 2 * deltaPhi phiZ hSD1 + v 5 * deltaPhi phiVz hSD1 := by
  have e0 : fderiv ℝ sdCart sStar (Pi.single 0 1) 2 = 0 :=
    (fderiv_sdCart_inPlane_z 0).1
  have e1 : fderiv ℝ sdCart sStar (Pi.single 1 1) 2 = 0 :=
    (fderiv_sdCart_inPlane_z 1).1
  have e2 : fderiv ℝ sdCart sStar (Pi.single 3 1) 2 = 0 :=
    (fderiv_sdCart_inPlane_z 2).1
  have e3 : fderiv ℝ sdCart sStar (Pi.single 4 1) 2 = 0 :=
    (fderiv_sdCart_inPlane_z 3).1
  have ez : fderiv ℝ sdCart sStar (Pi.single 2 1) 2 = deltaPhi phiZ hSD1 := by
    simp [fderiv_sdCart_ez']
  have evz : fderiv ℝ sdCart sStar (Pi.single 5 1) 2 = deltaPhi phiVz hSD1 := by
    simp [fderiv_sdCart_evz']
  rw [fderiv_sdCart_apply_eq_sum]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, e0, e1, e2, e3, ez, evz]
  ring

lemma fderiv_sdCart_coord5 (v : Fin 6 → ℝ) :
    fderiv ℝ sdCart sStar v 5 =
      v 2 * deltaPhi phiZ hSD2 + v 5 * deltaPhi phiVz hSD2 := by
  have e0 : fderiv ℝ sdCart sStar (Pi.single 0 1) 5 = 0 :=
    (fderiv_sdCart_inPlane_z 0).2
  have e1 : fderiv ℝ sdCart sStar (Pi.single 1 1) 5 = 0 :=
    (fderiv_sdCart_inPlane_z 1).2
  have e2 : fderiv ℝ sdCart sStar (Pi.single 3 1) 5 = 0 :=
    (fderiv_sdCart_inPlane_z 2).2
  have e3 : fderiv ℝ sdCart sStar (Pi.single 4 1) 5 = 0 :=
    (fderiv_sdCart_inPlane_z 3).2
  have ez : fderiv ℝ sdCart sStar (Pi.single 2 1) 5 = deltaPhi phiZ hSD2 := by
    simp [fderiv_sdCart_ez']
  have evz : fderiv ℝ sdCart sStar (Pi.single 5 1) 5 = deltaPhi phiVz hSD2 := by
    simp [fderiv_sdCart_evz']
  rw [fderiv_sdCart_apply_eq_sum]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, e0, e1, e2, e3, ez, evz]
  ring

lemma fderiv_sdCart_zOut_eq_z (v : Fin 6 → ℝ) (i : Fin 2) :
    fderiv ℝ sdCart sStar v (zOut i)
      = (zBlk *ᵥ ![v 2, v 5]) i := by
  rw [zBlk_mulVec]
  rcases i with ⟨n, hn⟩
  interval_cases n
  · simpa [zOut] using fderiv_sdCart_coord2 v
  · simpa [zOut] using fderiv_sdCart_coord5 v

lemma xyBlk_mulVec_eq_zero {v : Fin 4 → ℝ} (h : xyBlk *ᵥ v = 0) : v = 0 :=
  Matrix.eq_zero_of_mulVec_eq_zero xyBlk_det_ne h

lemma zBlk_mulVec_eq_zero {v : Fin 2 → ℝ} (h : zBlk *ᵥ v = 0) : v = 0 :=
  Matrix.eq_zero_of_mulVec_eq_zero zBlk_det_ne h

lemma fderiv_sdCart_injective :
    Function.Injective (fderiv ℝ sdCart sStar) := by
  intro v w hvw
  have hdiff : fderiv ℝ sdCart sStar (v - w) = 0 := by
    simpa [map_sub] using sub_eq_zero.mpr hvw
  have hxy : xyBlk *ᵥ ![(v - w) 0, (v - w) 1, (v - w) 3, (v - w) 4] = 0 := by
    ext i
    have hi := fderiv_sdCart_inPlaneOut_eq_xy (v - w) i
    have hz : fderiv ℝ sdCart sStar (v - w) (inPlaneOut i) = 0 := by
      simp [hdiff]
    exact hi.symm.trans hz
  have hz : zBlk *ᵥ ![(v - w) 2, (v - w) 5] = 0 := by
    ext i
    have hi := fderiv_sdCart_zOut_eq_z (v - w) i
    have h0 : fderiv ℝ sdCart sStar (v - w) (zOut i) = 0 := by
      simp [hdiff]
    exact hi.symm.trans h0
  have hxy0 := xyBlk_mulVec_eq_zero hxy
  have hz0 := zBlk_mulVec_eq_zero hz
  have hvw' : v - w = 0 := by
    ext i
    fin_cases i
    · simpa using congrArg (fun f : Fin 4 → ℝ => f 0) hxy0
    · simpa using congrArg (fun f : Fin 4 → ℝ => f 1) hxy0
    · simpa using congrArg (fun f : Fin 2 → ℝ => f 0) hz0
    · simpa using congrArg (fun f : Fin 4 → ℝ => f 2) hxy0
    · simpa using congrArg (fun f : Fin 4 → ℝ => f 3) hxy0
    · simpa using congrArg (fun f : Fin 2 → ℝ => f 1) hz0
  exact sub_eq_zero.mp hvw'

lemma exists_sigma_sdCart :
    ∃ σ : ℝ, 0 < σ ∧ ∀ v : Fin 6 → ℝ, σ * ‖v‖ ≤ ‖fderiv ℝ sdCart sStar v‖ := by
  classical
  let S : Set (Fin 6 → ℝ) := Metric.sphere 0 1
  have hK : IsCompact S := isCompact_sphere (0 : Fin 6 → ℝ) 1
  have hne : (Metric.sphere (0 : Fin 6 → ℝ) 1).Nonempty :=
    NormedSpace.sphere_nonempty.mpr (by norm_num : (0 : ℝ) ≤ 1)
  have hcont : Continuous fun v : Fin 6 → ℝ => ‖fderiv ℝ sdCart sStar v‖ := by
    fun_prop
  obtain ⟨v0, hv0S, hmin⟩ := hK.exists_isMinOn hne hcont.continuousOn
  have hv01 : ‖v0‖ = 1 := mem_sphere_zero_iff_norm.mp hv0S
  have hσpos : 0 < ‖fderiv ℝ sdCart sStar v0‖ := by
    refine norm_pos_iff.mpr ?_
    intro hz
    have : v0 = 0 := fderiv_sdCart_injective (by simpa using hz)
    have : (0 : ℝ) = 1 := by rw [← hv01, this, norm_zero]
    exact (by norm_num : (0 : ℝ) ≠ 1) this
  refine ⟨‖fderiv ℝ sdCart sStar v0‖, hσpos, ?_⟩
  intro v
  rcases eq_or_ne v 0 with hv | hv
  · simp [hv]
  · have hun : ‖(‖v‖)⁻¹ • v‖ = 1 := by
      rw [norm_smul, norm_inv, norm_norm]
      field_simp [norm_ne_zero_iff.mpr hv]
    have huS : (‖v‖)⁻¹ • v ∈ S := mem_sphere_zero_iff_norm.mpr hun
    have hmin' : ‖fderiv ℝ sdCart sStar v0‖
        ≤ ‖fderiv ℝ sdCart sStar ((‖v‖)⁻¹ • v)‖ := hmin huS
    have hsc : fderiv ℝ sdCart sStar ((‖v‖)⁻¹ • v)
        = (‖v‖)⁻¹ • fderiv ℝ sdCart sStar v := by
      simp
    rw [hsc, norm_smul, norm_inv, norm_norm] at hmin'
    have hvpos : 0 < ‖v‖ := norm_pos_iff.mpr hv
    have : ‖fderiv ℝ sdCart sStar v0‖ * ‖v‖ ≤ ‖fderiv ℝ sdCart sStar v‖ := by
      have := mul_le_mul_of_nonneg_right hmin' hvpos.le
      field_simp [hvpos.ne'] at this
      exact this
    simpa [mul_comm] using this

lemma contDiffAt_fderiv_sdCart :
    ContDiffAt ℝ 1 (fderiv ℝ sdCart) sStar :=
  contDiffAt_sdCart.fderiv_right (by decide)

lemma exists_lipschitz_fderiv_sdCart :
    ∃ K : NNReal, ∃ t ∈ 𝓝 sStar, LipschitzOnWith K (fderiv ℝ sdCart) t :=
  contDiffAt_fderiv_sdCart.exists_lipschitzOnWith

lemma exists_sdCart_remainder :
    ∃ σ K r : ℝ, 0 < σ ∧ 0 < r ∧
      ∀ x y : Fin 6 → ℝ, ‖x - sStar‖ < r → ‖y - sStar‖ < r →
        σ * ‖y - x‖ - K * ‖y - x‖ ^ 2 ≤ ‖sdCart y - sdCart x‖ := by
  obtain ⟨σ0, hσ0, hσ⟩ := exists_sigma_sdCart
  obtain ⟨K0, t, ht, hLip⟩ := exists_lipschitz_fderiv_sdCart
  have hC2 : ∀ᶠ z in 𝓝 sStar, ContDiffAt ℝ 2 sdCart z :=
    contDiffAt_sdCart.eventually (by simp)
  have hDfclose : ∀ᶠ z in 𝓝 sStar,
      ‖fderiv ℝ sdCart z - fderiv ℝ sdCart sStar‖ < σ0 / 2 := by
    have hc := contDiffAt_fderiv_sdCart.continuousAt
    simpa [dist_eq_norm] using (Metric.tendsto_nhds.mp hc.tendsto _ (half_pos hσ0))
  have hnhds : ∀ᶠ z in 𝓝 sStar,
      z ∈ t ∧ ContDiffAt ℝ 2 sdCart z ∧
        ‖fderiv ℝ sdCart z - fderiv ℝ sdCart sStar‖ < σ0 / 2 :=
    ((eventually_of_mem ht fun _ hz => hz).and hC2).and hDfclose |>.mono
      fun z hz => ⟨hz.1.1, hz.1.2, hz.2⟩
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hnhds
  have hσhalf : 0 < σ0 / 2 := half_pos hσ0
  refine ⟨σ0 / 2, (K0 : ℝ), r, hσhalf, hr, ?_⟩
  intro x y hx hy
  have hxB : x ∈ Metric.ball sStar r := Metric.mem_ball.2 (by rwa [dist_eq_norm])
  have hyB : y ∈ Metric.ball sStar r := Metric.mem_ball.2 (by rwa [dist_eq_norm])
  have hx' := hball hxB
  have hy' := hball hyB
  have hsegB : segment ℝ x y ⊆ Metric.ball sStar r :=
    (convex_ball (sStar : Fin 6 → ℝ) r).segment_subset hxB hyB
  have hσx : ∀ v, (σ0 / 2) * ‖v‖ ≤ ‖fderiv ℝ sdCart x v‖ := by
    intro v
    have hA : σ0 * ‖v‖ ≤ ‖fderiv ℝ sdCart sStar v‖ := hσ v
    have hop : ‖(fderiv ℝ sdCart x - fderiv ℝ sdCart sStar) v‖
        ≤ ‖fderiv ℝ sdCart x - fderiv ℝ sdCart sStar‖ * ‖v‖ :=
      ContinuousLinearMap.le_opNorm _ _
    have htri : ‖fderiv ℝ sdCart sStar v‖
        ≤ ‖fderiv ℝ sdCart x v‖
          + ‖(fderiv ℝ sdCart x - fderiv ℝ sdCart sStar) v‖ := by
      have : fderiv ℝ sdCart sStar v
          = fderiv ℝ sdCart x v
            - (fderiv ℝ sdCart x - fderiv ℝ sdCart sStar) v := by simp
      rw [this]; exact norm_sub_le _ _
    have hop' : ‖(fderiv ℝ sdCart x - fderiv ℝ sdCart sStar) v‖
        ≤ (σ0 / 2) * ‖v‖ :=
      hop.trans (mul_le_mul_of_nonneg_right hx'.2.2.le (norm_nonneg _))
    linarith [hA, hop', htri]
  have hdiff : ∀ z ∈ segment ℝ x y,
      HasFDerivWithinAt
        (fun w => sdCart w - fderiv ℝ sdCart x (w - x))
        (fderiv ℝ sdCart z - fderiv ℝ sdCart x) (segment ℝ x y) z := by
    intro z hz
    have hzB := hsegB hz
    have hz' := hball hzB
    have hF : HasFDerivAt sdCart (fderiv ℝ sdCart z) z :=
      (hz'.2.1.differentiableAt (by decide)).hasFDerivAt
    have hA : HasFDerivAt (fun w : Fin 6 → ℝ => fderiv ℝ sdCart x (w - x))
        (fderiv ℝ sdCart x) z := by
      have hsub : HasFDerivAt (fun w : Fin 6 → ℝ => w - x)
          (ContinuousLinearMap.id ℝ (Fin 6 → ℝ)) z :=
        (hasFDerivAt_id z).sub_const x
      exact (fderiv ℝ sdCart x).hasFDerivAt.comp z hsub
    exact (hF.sub hA).hasFDerivWithinAt
  have hC : ∀ z ∈ segment ℝ x y,
      ‖(fderiv ℝ sdCart z - fderiv ℝ sdCart x : (Fin 6 → ℝ) →L[ℝ] (Fin 6 → ℝ))‖
        ≤ (K0 : ℝ) * ‖y - x‖ := by
    intro z hz
    have hzB := hsegB hz
    have hz' := hball hzB
    have h1 : ‖fderiv ℝ sdCart z - fderiv ℝ sdCart x‖ ≤ K0 * ‖z - x‖ :=
      hLip.norm_sub_le hz'.1 hx'.1
    have h2 : ‖z - x‖ ≤ ‖y - x‖ := by
      have hs : z ∈ Metric.closedBall x ‖y - x‖ := by
        -- segment ⊆ Metric.closedBall x ‖y-x‖
        exact (convex_closedBall x ‖y - x‖).segment_subset
          (Metric.mem_closedBall_self (norm_nonneg _))
          (by rw [Metric.mem_closedBall, dist_eq_norm]) hz
      simpa [Metric.mem_closedBall, dist_eq_norm] using hs
    exact h1.trans (mul_le_mul_of_nonneg_left h2 K0.coe_nonneg)
  have hmvt :=
    (convex_segment x y).norm_image_sub_le_of_norm_hasFDerivWithin_le
      (f := fun w => sdCart w - fderiv ℝ sdCart x (w - x))
      (f' := fun z => fderiv ℝ sdCart z - fderiv ℝ sdCart x)
      hdiff hC (left_mem_segment ℝ x y) (right_mem_segment ℝ x y)
  have hrem : ‖sdCart y - sdCart x - fderiv ℝ sdCart x (y - x)‖
      ≤ (K0 : ℝ) * ‖y - x‖ ^ 2 := by
    have hgyx :
        (fun w => sdCart w - fderiv ℝ sdCart x (w - x)) y
          - (fun w => sdCart w - fderiv ℝ sdCart x (w - x)) x
          = sdCart y - sdCart x - fderiv ℝ sdCart x (y - x) := by
      simp only [map_sub]
      abel
    rw [← hgyx]
    have hpow : (K0 : ℝ) * ‖y - x‖ ^ 2 = (K0 : ℝ) * ‖y - x‖ * ‖y - x‖ := by
      ring
    rw [hpow]
    exact hmvt
  exact remainder_lower_bound hσx hrem

lemma isTarget_keplerIC_sStar (T : ℝ) :
    IsTarget (1 : ℝ) 2 3 T (keplerIC sStar) := by
  convert isTarget_circular_fiveHalves T
  funext t
  exact keplerIC_sStar t

lemma sdPairCoord_sub (a b c d : Vec) :
    sdPairCoord a b - sdPairCoord c d = sdPairCoord (a - c) (b - d) := by
  funext i
  fin_cases i <;> simp [sdPairCoord, Pi.sub_apply, PiLp.sub_apply]

lemma sdCart_sub (x y : Fin 6 → ℝ) :
    sdCart y - sdCart x =
      sdPairCoord
        (secondDiff (fun t => los obs (keplerIC y) t - los obs (keplerIC x) t) hSD1)
        (secondDiff (fun t => los obs (keplerIC y) t - los obs (keplerIC x) t) hSD2) := by
  simp only [sdCart, sdPairCoord_sub, secondDiff_sub]

lemma secondDiff_los_large_of_sdCart {x y : Fin 6 → ℝ} {ε : ℝ}
    (hε : 0 ≤ ε) (h : 8 * ε < ‖sdCart y - sdCart x‖) :
    8 * ε < ‖secondDiff (fun t => los obs (keplerIC y) t - los obs (keplerIC x) t) hSD1‖ ∨
      8 * ε < ‖secondDiff (fun t => los obs (keplerIC y) t - los obs (keplerIC x) t) hSD2‖ := by
  rw [sdCart_sub] at h
  set w1 := secondDiff (fun t => los obs (keplerIC y) t - los obs (keplerIC x) t) hSD1
  set w2 := secondDiff (fun t => los obs (keplerIC y) t - los obs (keplerIC x) t) hSD2
  have hmax : ∃ i, 8 * ε < |sdPairCoord w1 w2 i| := by
    by_contra hnone
    push_neg at hnone
    have : ‖sdPairCoord w1 w2‖ ≤ 8 * ε :=
      (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => by
        simpa [Real.norm_eq_abs] using hnone i
    exact (h.trans_le this).false
  obtain ⟨i, hi⟩ := hmax
  fin_cases i
  · left; exact hi.trans_le (coord_le_euclidean w1 0)
  · left; exact hi.trans_le (coord_le_euclidean w1 1)
  · left; exact hi.trans_le (coord_le_euclidean w1 2)
  · right; exact hi.trans_le (coord_le_euclidean w2 0)
  · right; exact hi.trans_le (coord_le_euclidean w2 1)
  · right; exact hi.trans_le (coord_le_euclidean w2 2)

lemma not_both_recovered_sdCart {ε : ℝ} {ξ : ℝ → Vec} {x y : Fin 6 → ℝ}
    (hε : 0 ≤ ε) (hsep : 8 * ε < ‖sdCart y - sdCart x‖)
    (hx : RecoveredBy obs ε 1 ξ (keplerIC x))
    (hy : RecoveredBy obs ε 1 ξ (keplerIC y)) : False := by
  rcases secondDiff_los_large_of_sdCart hε hsep with h1 | h2
  · exact not_both_recovered hSD1_window h1 hy hx
  · exact not_both_recovered hSD2_window h2 hy hx

lemma exists_sdCart_linear :
    ∃ σ r : ℝ, 0 < σ ∧ 0 < r ∧
      ∀ x y : Fin 6 → ℝ, ‖x - sStar‖ < r → ‖y - sStar‖ < r →
        σ * ‖y - x‖ ≤ ‖sdCart y - sdCart x‖ := by
  obtain ⟨σ, K, r0, hσ, hr0, hrem⟩ := exists_sdCart_remainder
  let r : ℝ := min r0 (σ / (4 * (|K| + 1)))
  have hr : 0 < r :=
    lt_min hr0 (div_pos hσ (by positivity))
  refine ⟨σ / 2, r, half_pos hσ, hr, ?_⟩
  intro x y hx hy
  have hx0 : ‖x - sStar‖ < r0 := hx.trans_le (min_le_left _ _)
  have hy0 : ‖y - sStar‖ < r0 := hy.trans_le (min_le_left _ _)
  have hlow := hrem x y hx0 hy0
  have hΔ : ‖y - x‖ < 2 * r := by
    have htri : ‖(y - sStar) + (sStar - x)‖ ≤ ‖y - sStar‖ + ‖sStar - x‖ :=
      norm_add_le _ _
    have hyx : y - x = (y - sStar) + (sStar - x) := by abel
    rw [hyx]
    have hrev : ‖sStar - x‖ = ‖x - sStar‖ := norm_sub_rev _ _
    have hsum : ‖y - sStar‖ + ‖x - sStar‖ < r + r := add_lt_add hy hx
    have hrr : r + r = 2 * r := by ring
    exact (htri.trans_eq (by rw [hrev])).trans_lt (hsum.trans_eq hrr)
  have hK : K * ‖y - x‖ ^ 2 ≤ |K| * ‖y - x‖ * (2 * r) := by
    have h1 : K * ‖y - x‖ ^ 2 ≤ |K| * ‖y - x‖ ^ 2 :=
      mul_le_mul_of_nonneg_right (le_abs_self K) (sq_nonneg _)
    have h2 : |K| * ‖y - x‖ ^ 2 = (|K| * ‖y - x‖) * ‖y - x‖ := by ring
    have h3 : (|K| * ‖y - x‖) * ‖y - x‖ ≤ (|K| * ‖y - x‖) * (2 * r) :=
      mul_le_mul_of_nonneg_left hΔ.le (mul_nonneg (abs_nonneg _) (norm_nonneg _))
    linarith
  have hKσ : |K| * (2 * r) ≤ σ / 2 := by
    have hrle : r ≤ σ / (4 * (|K| + 1)) := min_le_right _ _
    have hstep : |K| * (2 * r) ≤ |K| * (2 * (σ / (4 * (|K| + 1)))) :=
      mul_le_mul_of_nonneg_left (by nlinarith) (abs_nonneg _)
    have hfrac : |K| * (2 * (σ / (4 * (|K| + 1)))) ≤ σ / 2 := by
      have hden : (0 : ℝ) < 4 * (|K| + 1) := by positivity
      field_simp
      nlinarith [abs_nonneg K, hσ]
    exact hstep.trans hfrac
  have hK2 : |K| * ‖y - x‖ * (2 * r) ≤ (σ / 2) * ‖y - x‖ := by
    calc
      |K| * ‖y - x‖ * (2 * r) = |K| * (2 * r) * ‖y - x‖ := by ring
      _ ≤ (σ / 2) * ‖y - x‖ :=
        mul_le_mul_of_nonneg_right hKσ (norm_nonneg _)
  have hlin : (σ / 2) * ‖y - x‖ ≤ σ * ‖y - x‖ - K * ‖y - x‖ ^ 2 := by linarith
  exact hlin.trans hlow

def cartPt (n : ℕ) (δ : ℝ) (u : Fin 6 → Fin n) : Fin 6 → ℝ :=
  fun i => sStar i + δ * (((u i : ℕ) : ℝ) - ((n : ℝ) - 1) / 2)

lemma cartPt_injective {n : ℕ} {δ : ℝ} (hδ : 0 < δ) {u v : Fin 6 → Fin n}
    (h : cartPt n δ u = cartPt n δ v) : u = v := by
  funext i
  have hcongr := congrArg (fun f : Fin 6 → ℝ => f i) h
  simp only [cartPt] at hcongr
  have : ((u i : ℕ) : ℝ) = ((v i : ℕ) : ℝ) := by
    apply_fun (fun z => z - sStar i) at hcongr
    simp only [add_sub_cancel_left] at hcongr
    have : ((u i : ℕ) : ℝ) - ((n : ℝ) - 1) / 2 =
        ((v i : ℕ) : ℝ) - ((n : ℝ) - 1) / 2 :=
      mul_left_cancel₀ hδ.ne' hcongr
    linarith
  exact Fin.ext (Nat.cast_injective this)

lemma cartPt_coord_abs {n : ℕ} {δ : ℝ} (hn : 0 < n) (hδ : 0 ≤ δ)
    (u : Fin 6 → Fin n) (i : Fin 6) :
    |cartPt n δ u i - sStar i| ≤ δ * ((n : ℝ) - 1) / 2 := by
  simp only [cartPt, add_sub_cancel_left, abs_mul, abs_of_nonneg hδ]
  have hidx : |((u i : ℕ) : ℝ) - ((n : ℝ) - 1) / 2| ≤ ((n : ℝ) - 1) / 2 := by
    have hu : (u i : ℕ) < n := (u i).isLt
    have hun : ((u i : ℕ) : ℝ) ≤ (n : ℝ) - 1 := by
      have : (u i : ℕ) ≤ n - 1 := Nat.le_pred_of_lt hu
      cases n with
      | zero => exact (lt_irrefl _ hn).elim
      | succ n => exact (Nat.cast_le.mpr this).trans_eq (by simp [Nat.cast_succ])
    have hhalf : 0 ≤ ((n : ℝ) - 1) / 2 := by
      have : (1 : ℝ) ≤ n := Nat.one_le_cast.mpr (Nat.succ_le_of_lt hn)
      linarith
    have hu0 : (0 : ℝ) ≤ (u i : ℕ) := Nat.cast_nonneg _
    exact abs_sub_le_iff.2 ⟨by linarith, by linarith⟩
  have : δ * |((u i : ℕ) : ℝ) - ((n : ℝ) - 1) / 2| ≤ δ * (((n : ℝ) - 1) / 2) := by
    gcongr
  linarith

lemma cartPt_mem_ball {n : ℕ} {δ r : ℝ} (hn : 0 < n) (hδ : 0 ≤ δ)
    (hbd : δ * ((n : ℝ) - 1) / 2 < r) (u : Fin 6 → Fin n) :
    ‖cartPt n δ u - sStar‖ < r := by
  have hn1 : (1 : ℝ) ≤ n := Nat.one_le_cast.mpr (Nat.succ_le_of_lt hn)
  have hnn : 0 ≤ δ * ((n : ℝ) - 1) / 2 := by
    have : 0 ≤ (n : ℝ) - 1 := by linarith
    positivity
  have hle : ‖cartPt n δ u - sStar‖ ≤ δ * ((n : ℝ) - 1) / 2 :=
    (pi_norm_le_iff_of_nonneg hnn).2 fun i => by
      simpa [Real.norm_eq_abs, Pi.sub_apply] using cartPt_coord_abs hn hδ u i
  exact hle.trans_lt hbd

lemma cartPt_sep {n : ℕ} {δ : ℝ} (hδ : 0 < δ) {u v : Fin 6 → Fin n}
    (hne : u ≠ v) : δ ≤ ‖cartPt n δ u - cartPt n δ v‖ := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hne
  have hun : (u i : ℕ) ≠ (v i : ℕ) := mt (fun h => Fin.ext h) hi
  have hcoord :
      |cartPt n δ u i - cartPt n δ v i| ≤ ‖cartPt n δ u - cartPt n δ v‖ := by
    simpa [Real.norm_eq_abs, Pi.sub_apply] using
      norm_le_pi_norm (cartPt n δ u - cartPt n δ v) i
  have hdiff : cartPt n δ u i - cartPt n δ v i =
      δ * (((u i : ℕ) : ℝ) - ((v i : ℕ) : ℝ)) := by
    simp [cartPt]; ring
  have habs : |cartPt n δ u i - cartPt n δ v i| =
      δ * |((u i : ℕ) : ℝ) - ((v i : ℕ) : ℝ)| := by
    rw [hdiff, abs_mul, abs_of_pos hδ]
  have h1 : (1 : ℝ) ≤ |((u i : ℕ) : ℝ) - ((v i : ℕ) : ℝ)| := by
    have : (1 : ℤ) ≤ |((u i : ℕ) : ℤ) - ((v i : ℕ) : ℤ)| :=
      Int.one_le_abs (sub_ne_zero.mpr (by exact_mod_cast hun))
    exact_mod_cast this
  calc
    δ = δ * 1 := by ring
    _ ≤ δ * |((u i : ℕ) : ℝ) - ((v i : ℕ) : ℝ)| :=
      mul_le_mul_of_nonneg_left h1 hδ.le
    _ = |cartPt n δ u i - cartPt n δ v i| := habs.symm
    _ ≤ ‖cartPt n δ u - cartPt n δ v‖ := hcoord

lemma exhaustive_ncard_ge_sdCart
    {ε : ℝ} {P : Set (Fin 6 → ℝ)} {S : Set (ℝ → Vec)}
    (hε : 0 ≤ ε) (hSfin : S.Finite)
    (hP : ∀ s ∈ P, IsTarget (1 : ℝ) 2 3 1 (keplerIC s))
    (hsep : ∀ x ∈ P, ∀ y ∈ P, x ≠ y → 8 * ε < ‖sdCart y - sdCart x‖)
    (hcov : IsExhaustiveCover (1 : ℝ) 2 3 1 ε obs S) :
    P.ncard ≤ S.ncard := by
  classical
  obtain ⟨_, hrec⟩ := hcov
  let f : (Fin 6 → ℝ) → (ℝ → Vec) := fun s =>
    if hs : s ∈ P then Classical.choose (hrec (keplerIC s) (hP s hs)) else obs
  have hfmem : ∀ s ∈ P, f s ∈ S := by
    intro s hs
    simpa [f, dif_pos hs] using (Classical.choose_spec (hrec (keplerIC s) (hP s hs))).1
  have hfrec : ∀ s ∈ P, RecoveredBy obs ε 1 (f s) (keplerIC s) := by
    intro s hs
    simpa [f, dif_pos hs] using (Classical.choose_spec (hrec (keplerIC s) (hP s hs))).2
  refine Set.ncard_le_ncard_of_injOn f hfmem ?_ hSfin
  intro x hx y hy hxy
  by_contra hne
  exact not_both_recovered_sdCart hε (hsep x hx y hy hne)
    (hfrec x hx) (hxy ▸ hfrec y hy)

lemma circular_norm_fiveHalves (t : ℝ) :
    ‖keplerIC sStar t‖ = (5 / 2 : ℝ) := by
  rw [keplerIC_sStar, circular_norm _ _ _ _ (by norm_num)]

lemma cartPt_sdCart_sep {n : ℕ} {δ σ r : ℝ}
    (hσ : 0 < σ) (hδ : 0 < δ) (hr : 0 < r) (hn : 0 < n)
    (hlin : ∀ x y : Fin 6 → ℝ, ‖x - sStar‖ < r → ‖y - sStar‖ < r →
      σ * ‖y - x‖ ≤ ‖sdCart y - sdCart x‖)
    (hbd : δ * ((n : ℝ) - 1) / 2 < r)
    {u v : Fin 6 → Fin n} (hne : u ≠ v) :
    σ * δ ≤ ‖sdCart (cartPt n δ v) - sdCart (cartPt n δ u)‖ := by
  have hu := cartPt_mem_ball hn hδ.le hbd u
  have hv := cartPt_mem_ball hn hδ.le hbd v
  have hsep := cartPt_sep hδ hne
  have hlin' := hlin (cartPt n δ u) (cartPt n δ v) hu hv
  have hrev : ‖cartPt n δ v - cartPt n δ u‖ = ‖cartPt n δ u - cartPt n δ v‖ :=
    norm_sub_rev _ _
  exact (mul_le_mul_of_nonneg_left hsep hσ.le).trans (hrev ▸ hlin')


/-! Joint-in-time Kepler anomaly `chiProd` (level-set inverse of `univF`). -/

lemma hasStrictFDerivAt_uncurry_univF (chi0 : ℝ) :
    HasStrictFDerivAt (Function.uncurry univF)
      (fderiv ℝ (Function.uncurry univF) (sStar, chi0)) (sStar, chi0) :=
  (contDiffAt_uncurry_univF chi0).hasStrictFDerivAt (by decide)

lemma univF_partial_chi_invertible_chi (chi0 : ℝ) :
    (fderiv ℝ (Function.uncurry univF) (sStar, chi0) ∘L
        ContinuousLinearMap.inr ℝ (Fin 6 → ℝ) ℝ).IsInvertible := by
  rw [fderiv_univF_comp_inr]
  exact ContinuousLinearMap.IsInvertible.of_inverse
    (g := ContinuousLinearMap.toSpanSingleton ℝ (2 / 5))
    (by ext; simp) (by ext; simp)

noncomputable def chiData (t0 : ℝ) :
    ImplicitFunctionData ℝ ((Fin 6 → ℝ) × ℝ) ℝ (Fin 6 → ℝ) :=
  (hasStrictFDerivAt_uncurry_univF (2 * t0 / 5)).implicitFunctionDataOfProdDomain
    (univF_partial_chi_invertible_chi (2 * t0 / 5))

noncomputable def chiProd (t0 : ℝ) (t : ℝ) (s : Fin 6 → ℝ) : ℝ :=
  (chiData t0 |>.implicitFunction t s).2

/-! Algebraic elliptic f,g identities used by the two-body ODE. -/

lemma fg_f_ell_id {s : Fin 6 → ℝ} {χ : ℝ} (hα : 0 < alphaOf s) :
    fg_f s χ = 1 - (1 - Real.cos (Real.sqrt (alphaOf s) * χ)) /
      (alphaOf s * rnorm s) :=
  fg_f_ell hα

lemma fg_g_of_kepler {s : Fin 6 → ℝ} {t χ : ℝ}
    (hα : 0 < alphaOf s) (ht : univF s χ = t) :
    fg_g s t χ =
      sigmaOf s * (1 - Real.cos (Real.sqrt (alphaOf s) * χ)) / alphaOf s
        + rnorm s * Real.sin (Real.sqrt (alphaOf s) * χ)
          / Real.sqrt (alphaOf s) := by
  have hg := fg_g_ell (s := s) (t := t) (chi := χ) hα
  have hu := univF_eq_ell (s := s) (χ := χ) hα
  rw [hg]
  have hα0 : alphaOf s ≠ 0 := hα.ne'
  have hω0 : Real.sqrt (alphaOf s) ≠ 0 := Real.sqrt_ne_zero'.2 hα
  have ht' : t = univF_ell (alphaOf s) (sigmaOf s) (rnorm s) χ := by
    rw [← hu, ht]
  rw [ht']
  simp [univF_ell]
  field_simp [hα0, hω0]
  ring


lemma chiData_pt (t0 : ℝ) : (chiData t0).pt = (sStar, 2 * t0 / 5) := rfl

lemma chiData_leftFun (t0 : ℝ) :
    (chiData t0).leftFun = Function.uncurry univF := rfl

lemma chiData_rightFun (t0 : ℝ) :
    (chiData t0).rightFun = Prod.fst := rfl

lemma chiData_prodFun_pt (t0 : ℝ) :
    (chiData t0).prodFun (chiData t0).pt = (t0, sStar) := by
  change (Function.uncurry univF (sStar, 2 * t0 / 5), sStar) = (t0, sStar)
  simp [Function.uncurry, univF_sStar]

lemma eventually_prodFun_chiProd (t0 : ℝ) :
    ∀ᶠ p : ℝ × (Fin 6 → ℝ) in 𝓝 (t0, sStar),
      (chiData t0).prodFun ((chiData t0).implicitFunction p.1 p.2) = p := by
  have h := (chiData t0).prodFun_implicitFunction
  rwa [chiData_prodFun_pt t0] at h

lemma eventually_univF_chiProd (t0 : ℝ) :
    ∀ᶠ p : ℝ × (Fin 6 → ℝ) in 𝓝 (t0, sStar),
      univF p.2 (chiProd t0 p.1 p.2) = p.1 := by
  filter_upwards [eventually_prodFun_chiProd t0] with p hp
  have hF : Function.uncurry univF ((chiData t0).implicitFunction p.1 p.2) = p.1 := by
    simpa [ImplicitFunctionData.prodFun, chiData_leftFun] using congrArg Prod.fst hp
  have hs : ((chiData t0).implicitFunction p.1 p.2).1 = p.2 := by
    simpa [ImplicitFunctionData.prodFun, chiData_rightFun] using congrArg Prod.snd hp
  have : Function.uncurry univF ((chiData t0).implicitFunction p.1 p.2) =
      univF p.2 (chiProd t0 p.1 p.2) := by
    simp [Function.uncurry, chiProd, hs]
  exact this.symm.trans hF

lemma eventually_univF_chiProd_sStar (t0 : ℝ) :
    ∀ᶠ t in 𝓝 t0, univF sStar (chiProd t0 t sStar) = t := by
  have hpath : Tendsto (fun t : ℝ => (t, sStar)) (𝓝 t0) (𝓝 (t0, sStar)) :=
    tendsto_id.prodMk_nhds tendsto_const_nhds
  exact hpath.eventually (eventually_univF_chiProd t0)

lemma chiProd_center (t0 : ℝ) : chiProd t0 t0 sStar = 2 * t0 / 5 := by
  have h := (chiData t0).implicitFunction_apply_image.self_of_nhds
  have hpt : (chiData t0).implicitFunction t0 sStar = (sStar, 2 * t0 / 5) := by
    simpa [chiData_pt, chiData_leftFun, chiData_rightFun, Function.uncurry, univF_sStar] using h
  simpa [chiProd] using congrArg Prod.snd hpt

lemma eventually_chiProd_sStar (t0 : ℝ) :
    ∀ᶠ t in 𝓝 t0, chiProd t0 t sStar = 2 * t / 5 := by
  filter_upwards [eventually_univF_chiProd_sStar t0] with t ht
  have : (5 / 2) * chiProd t0 t sStar = t := by
    rw [← univF_sStar, ht]
  linarith

lemma chiData_target_mem (t0 : ℝ) :
    (t0, sStar) ∈ (chiData t0).toOpenPartialHomeomorph.target := by
  have h := (chiData t0).map_pt_mem_toOpenPartialHomeomorph_target
  -- `map_pt` is `(leftFun pt, rightFun pt) = prodFun pt`
  change (chiData t0).prodFun (chiData t0).pt ∈ _ at h
  rwa [chiData_prodFun_pt t0] at h

lemma continuousAt_chiProd (t0 : ℝ) :
    ContinuousAt (fun p : ℝ × (Fin 6 → ℝ) => chiProd t0 p.1 p.2) (t0, sStar) := by
  have hsym := (chiData t0).toOpenPartialHomeomorph.continuousAt_symm (chiData_target_mem t0)
  exact continuousAt_snd.comp hsym

lemma continuousAt_chiProd_sStar (t0 : ℝ) :
    ContinuousAt (fun t : ℝ => chiProd t0 t sStar) t0 := by
  have hp : ContinuousAt (fun t : ℝ => (t, sStar)) t0 :=
    continuousAt_id.prodMk continuousAt_const
  change ContinuousAt
      ((fun p : ℝ × (Fin 6 → ℝ) => chiProd t0 p.1 p.2) ∘ fun t : ℝ => (t, sStar)) t0
  exact ContinuousAt.comp (continuousAt_chiProd t0) hp

lemma hasDerivAt_chiProd_sStar (t0 : ℝ) :
    HasDerivAt (fun t => chiProd t0 t sStar) (2 / 5) t0 := by
  have hf : HasDerivAt (univF sStar) (5 / 2) (chiProd t0 t0 sStar) := by
    simpa [chiProd_center t0] using hasDerivAt_univF_sStar (2 * t0 / 5)
  have hinv := HasDerivAt.of_local_left_inverse (continuousAt_chiProd_sStar t0) hf
    (by norm_num : (5 / 2 : ℝ) ≠ 0)
    (eventually_univF_chiProd_sStar t0)
  exact hinv.congr_deriv (by norm_num)

lemma hasDerivAt_fg_f_ell_chi {s : Fin 6 → ℝ} {χ : ℝ} (hα : 0 < alphaOf s)
    (hr : rnorm s ≠ 0) :
    HasDerivAt (fg_f s)
      (-Real.sin (Real.sqrt (alphaOf s) * χ) /
        (Real.sqrt (alphaOf s) * rnorm s)) χ := by
  have hα0 : alphaOf s ≠ 0 := hα.ne'
  have hω0 : Real.sqrt (alphaOf s) ≠ 0 := Real.sqrt_ne_zero'.2 hα
  have hωu : HasDerivAt (fun u => Real.sqrt (alphaOf s) * u)
      (Real.sqrt (alphaOf s)) χ := by
    simpa using (hasDerivAt_id χ).const_mul (Real.sqrt (alphaOf s))
  have h1 : HasDerivAt (fun u => 1 - Real.cos (Real.sqrt (alphaOf s) * u))
      (Real.sin (Real.sqrt (alphaOf s) * χ) * Real.sqrt (alphaOf s)) χ := by
    refine ((hasDerivAt_const χ (1 : ℝ)).sub hωu.cos).congr_deriv ?_
    ring
  have hdiv : HasDerivAt
      (fun u => (1 - Real.cos (Real.sqrt (alphaOf s) * u)) / (alphaOf s * rnorm s))
      (Real.sin (Real.sqrt (alphaOf s) * χ) * Real.sqrt (alphaOf s) /
        (alphaOf s * rnorm s)) χ :=
    h1.div_const (alphaOf s * rnorm s)
  have hell : HasDerivAt
      (fun u => 1 - (1 - Real.cos (Real.sqrt (alphaOf s) * u)) / (alphaOf s * rnorm s))
      (-(Real.sin (Real.sqrt (alphaOf s) * χ) * Real.sqrt (alphaOf s)) /
        (alphaOf s * rnorm s)) χ :=
    ((hasDerivAt_const χ (1 : ℝ)).sub hdiv).congr_deriv (by ring)
  have hfun : fg_f s = fun u =>
      1 - (1 - Real.cos (Real.sqrt (alphaOf s) * u)) / (alphaOf s * rnorm s) :=
    funext fun u => fg_f_ell (s := s) (chi := u) hα
  rw [hfun]
  refine hell.congr_deriv ?_
  have hsq : Real.sqrt (alphaOf s) * Real.sqrt (alphaOf s) = alphaOf s :=
    Real.mul_self_sqrt hα.le
  field_simp [hα0, hω0, hr]
  simp [pow_two, hsq]
  ring

lemma hasDerivAt_fg_g_ell_chi {s : Fin 6 → ℝ} {t χ : ℝ} (hα : 0 < alphaOf s) :
    HasDerivAt (fun ξ => fg_g s t ξ)
      ((Real.cos (Real.sqrt (alphaOf s) * χ) - 1) / alphaOf s) χ := by
  have hα0 : alphaOf s ≠ 0 := hα.ne'
  have hω0 : Real.sqrt (alphaOf s) ≠ 0 := Real.sqrt_ne_zero'.2 hα
  have hωu : HasDerivAt (fun u => Real.sqrt (alphaOf s) * u)
      (Real.sqrt (alphaOf s)) χ := by
    simpa using (hasDerivAt_id χ).const_mul (Real.sqrt (alphaOf s))
  have hidα : HasDerivAt (fun u => u / alphaOf s) (1 / alphaOf s) χ :=
    (hasDerivAt_id χ).div_const (alphaOf s)
  have hsin : HasDerivAt (fun u => Real.sin (Real.sqrt (alphaOf s) * u))
      (Real.cos (Real.sqrt (alphaOf s) * χ) * Real.sqrt (alphaOf s)) χ :=
    hωu.sin
  have hsinα : HasDerivAt
      (fun u => Real.sin (Real.sqrt (alphaOf s) * u) /
        (alphaOf s * Real.sqrt (alphaOf s)))
      (Real.cos (Real.sqrt (alphaOf s) * χ) / alphaOf s) χ := by
    refine (hsin.div_const (alphaOf s * Real.sqrt (alphaOf s))).congr_deriv ?_
    field_simp [hα0, hω0]
  have hinner := hidα.sub hsinα
  have hell : HasDerivAt
      (fun u => t - (u / alphaOf s -
        Real.sin (Real.sqrt (alphaOf s) * u) / (alphaOf s * Real.sqrt (alphaOf s))))
      (-(1 / alphaOf s - Real.cos (Real.sqrt (alphaOf s) * χ) / alphaOf s)) χ :=
    ((hasDerivAt_const χ t).sub hinner).congr_deriv (by ring)
  have hfun : (fun ξ => fg_g s t ξ) = fun u =>
      t - (u / alphaOf s -
        Real.sin (Real.sqrt (alphaOf s) * u) / (alphaOf s * Real.sqrt (alphaOf s))) :=
    funext fun u => fg_g_ell (s := s) (t := t) (chi := u) hα
  rw [hfun]
  refine hell.congr_deriv ?_
  field_simp [hα0]
  ring

lemma hasDerivAt_fg_f_ell_chi2 {s : Fin 6 → ℝ} {χ : ℝ} (hα : 0 < alphaOf s)
    (hr : rnorm s ≠ 0) :
    HasDerivAt (fun u =>
        -Real.sin (Real.sqrt (alphaOf s) * u) /
          (Real.sqrt (alphaOf s) * rnorm s))
      (-Real.cos (Real.sqrt (alphaOf s) * χ) / rnorm s) χ := by
  have hω0 : Real.sqrt (alphaOf s) ≠ 0 := Real.sqrt_ne_zero'.2 hα
  have hωu : HasDerivAt (fun u => Real.sqrt (alphaOf s) * u)
      (Real.sqrt (alphaOf s)) χ := by
    simpa using (hasDerivAt_id χ).const_mul (Real.sqrt (alphaOf s))
  have hsin : HasDerivAt (fun u => Real.sin (Real.sqrt (alphaOf s) * u))
      (Real.cos (Real.sqrt (alphaOf s) * χ) * Real.sqrt (alphaOf s)) χ :=
    hωu.sin
  have hdiv := hsin.div_const (Real.sqrt (alphaOf s) * rnorm s)
  have hneg := hdiv.neg
  have hfun : (fun u => -Real.sin (Real.sqrt (alphaOf s) * u) /
        (Real.sqrt (alphaOf s) * rnorm s)) =
      fun u => -(Real.sin (Real.sqrt (alphaOf s) * u) /
        (Real.sqrt (alphaOf s) * rnorm s)) := by
    funext u; ring
  rw [hfun]
  refine hneg.congr_deriv ?_
  field_simp [hω0, hr]

lemma hasDerivAt_fg_g_ell_chi2 {s : Fin 6 → ℝ} {χ : ℝ} (hα : 0 < alphaOf s) :
    HasDerivAt (fun u =>
        (Real.cos (Real.sqrt (alphaOf s) * u) - 1) / alphaOf s)
      (-Real.sin (Real.sqrt (alphaOf s) * χ) / Real.sqrt (alphaOf s)) χ := by
  have hα0 : alphaOf s ≠ 0 := hα.ne'
  have hω0 : Real.sqrt (alphaOf s) ≠ 0 := Real.sqrt_ne_zero'.2 hα
  have hωu : HasDerivAt (fun u => Real.sqrt (alphaOf s) * u)
      (Real.sqrt (alphaOf s)) χ := by
    simpa using (hasDerivAt_id χ).const_mul (Real.sqrt (alphaOf s))
  have hnum : HasDerivAt (fun u => Real.cos (Real.sqrt (alphaOf s) * u) - 1)
      (-Real.sin (Real.sqrt (alphaOf s) * χ) * Real.sqrt (alphaOf s)) χ := by
    refine (hωu.cos.sub_const (1 : ℝ)).congr_deriv ?_
    ring
  refine (hnum.div_const (alphaOf s)).congr_deriv ?_
  have hsq : Real.sqrt (alphaOf s) * Real.sqrt (alphaOf s) = alphaOf s :=
    Real.mul_self_sqrt hα.le
  field_simp [hα0, hω0]
  simp [pow_two, hsq]
  ring

lemma rho_ell_eq (s : Fin 6 → ℝ) (χ : ℝ) (hα : 0 < alphaOf s) :
    univF_dchi s χ =
      rnorm s * Real.cos (Real.sqrt (alphaOf s) * χ)
        + sigmaOf s * Real.sin (Real.sqrt (alphaOf s) * χ) / Real.sqrt (alphaOf s)
        + (1 - Real.cos (Real.sqrt (alphaOf s) * χ)) / alphaOf s := by
  rw [univF_dchi_eq_ell hα]
  have hα0 : alphaOf s ≠ 0 := hα.ne'
  field_simp [hα0]
  ring

lemma rnorm_ne_of_alpha_pos {s : Fin 6 → ℝ} (hα : 0 < alphaOf s) : rnorm s ≠ 0 := by
  intro hr
  have hαeq : alphaOf s = -‖stateVel s‖ ^ 2 := by
    unfold alphaOf
    rw [hr, div_zero]
    ring
  have : alphaOf s ≤ 0 := by
    rw [hαeq]; nlinarith [sq_nonneg (‖stateVel s‖)]
  exact (not_le_of_gt hα) this

lemma eventually_rnorm_pos :
    ∀ᶠ s in 𝓝 sStar, 0 < rnorm s := by
  have : Tendsto rnorm (𝓝 sStar) (𝓝 (rnorm sStar)) :=
    (contDiffAt_rnorm rnorm_sStar_ne).continuousAt.tendsto
  exact this.eventually (Ioi_mem_nhds rnorm_sStar_pos)

lemma hasDerivAt_chiOf_time_sStar (t : ℝ) :
    HasDerivAt (fun τ => chiOf sStar τ) (2 / 5) t :=
  (hasDerivAt_chiOf_sStar t).congr_deriv (by field_simp)

lemma ncard_cartPt {n : ℕ} {δ : ℝ} (hδ : 0 < δ) :
    (Set.range (cartPt n δ)).ncard = n ^ 6 := by
  have hinj : Function.Injective (cartPt n δ) :=
    fun _ _ h => cartPt_injective hδ h
  rw [Set.ncard_range_of_injective hinj, ← ncard_grid, Set.ncard_univ]

lemma packing_cartPt_ncard {n : ℕ} {δ : ℝ} (hδ : 0 < δ) :
    ((Set.range (cartPt n δ)).ncard : ℝ) = (n : ℝ) ^ 6 := by
  rw [ncard_cartPt hδ]
  norm_cast

/-! χ' = 1/ρ off `sStar`, f''/g'' = -f/g / ρ³, Kepler/InShell for `keplerIC`. -/

lemma chiData_open_target (t0 : ℝ) :
    IsOpen (chiData t0).toOpenPartialHomeomorph.target :=
  (chiData t0).toOpenPartialHomeomorph.open_target

lemma chiData_right_inv (t0 t : ℝ) (s : Fin 6 → ℝ)
    (h : (t, s) ∈ (chiData t0).toOpenPartialHomeomorph.target) :
    univF s (chiProd t0 t s) = t ∧
      ((chiData t0).implicitFunction t s).1 = s := by
  have himp : (chiData t0).implicitFunction t s =
      (chiData t0).toOpenPartialHomeomorph.symm (t, s) := rfl
  have hr := (chiData t0).toOpenPartialHomeomorph.right_inv h
  have hprod : (chiData t0).prodFun ((chiData t0).implicitFunction t s) = (t, s) := by
    simpa [himp, ImplicitFunctionData.prodFun] using hr
  have hF : Function.uncurry univF ((chiData t0).implicitFunction t s) = t :=
    congrArg Prod.fst hprod
  have hs : ((chiData t0).implicitFunction t s).1 = s := by
    simpa [ImplicitFunctionData.prodFun, chiData_rightFun] using congrArg Prod.snd hprod
  refine ⟨?_, hs⟩
  simpa [Function.uncurry, chiProd, hs] using hF

lemma continuousAt_chiProd_slice (t0 t : ℝ) (s : Fin 6 → ℝ)
    (h : (t, s) ∈ (chiData t0).toOpenPartialHomeomorph.target) :
    ContinuousAt (fun τ => chiProd t0 τ s) t := by
  have hsym := (chiData t0).toOpenPartialHomeomorph.continuousAt_symm h
  have hp : ContinuousAt (fun τ : ℝ => (τ, s)) t :=
    continuousAt_id.prodMk continuousAt_const
  change ContinuousAt
      ((fun p : ℝ × (Fin 6 → ℝ) => chiProd t0 p.1 p.2) ∘ fun τ : ℝ => (τ, s)) t
  exact ContinuousAt.comp (continuousAt_snd.comp hsym) hp

lemma eventually_univF_chiProd_slice (t0 t : ℝ) (s : Fin 6 → ℝ)
    (h : (t, s) ∈ (chiData t0).toOpenPartialHomeomorph.target) :
    ∀ᶠ τ in 𝓝 t, univF s (chiProd t0 τ s) = τ := by
  have hnhds := (chiData_open_target t0).mem_nhds h
  have hslice : {τ : ℝ | (τ, s) ∈ (chiData t0).toOpenPartialHomeomorph.target} ∈ 𝓝 t :=
    (continuous_id.prodMk continuous_const).continuousAt.preimage_mem_nhds hnhds
  refine Filter.eventually_of_mem hslice ?_
  intro τ hτ
  exact (chiData_right_inv t0 τ s hτ).1

lemma eventually_univF_dchi_pos (chi0 : ℝ) :
    ∀ᶠ v : (Fin 6 → ℝ) × ℝ in 𝓝 (sStar, chi0), 0 < univF_dchi v.1 v.2 := by
  have hpos : 0 < univF_dchi sStar chi0 := by
    rw [univF_dchi_sStar]; norm_num
  exact (continuousAt_univF_dchi chi0).preimage_mem_nhds (Ioi_mem_nhds hpos)

lemma eventually_chiProd_dchi_pos (t0 : ℝ) :
    ∀ᶠ p : ℝ × (Fin 6 → ℝ) in 𝓝 (t0, sStar),
      0 < univF_dchi p.2 (chiProd t0 p.1 p.2) := by
  have hρ := eventually_univF_dchi_pos (2 * t0 / 5)
  have hcont : Tendsto (fun p : ℝ × (Fin 6 → ℝ) =>
      (p.2, chiProd t0 p.1 p.2)) (𝓝 (t0, sStar))
      (𝓝 (sStar, 2 * t0 / 5)) := by
    have hs : Tendsto (fun p : ℝ × (Fin 6 → ℝ) => p.2) (𝓝 (t0, sStar)) (𝓝 sStar) :=
      continuous_snd.continuousAt
    have hχ : Tendsto (fun p : ℝ × (Fin 6 → ℝ) => chiProd t0 p.1 p.2)
        (𝓝 (t0, sStar)) (𝓝 (2 * t0 / 5)) := by
      simpa [chiProd_center t0] using (continuousAt_chiProd t0).tendsto
    exact hs.prodMk_nhds hχ
  exact hcont.eventually hρ

lemma eventually_hasDerivAt_chiProd (t0 : ℝ) :
    ∀ᶠ p : ℝ × (Fin 6 → ℝ) in 𝓝 (t0, sStar),
      0 < alphaOf p.2 ∧
        0 < univF_dchi p.2 (chiProd t0 p.1 p.2) ∧
          HasDerivAt (fun τ => chiProd t0 τ p.2)
            (univF_dchi p.2 (chiProd t0 p.1 p.2))⁻¹ p.1 := by
  have hα : ∀ᶠ p : ℝ × (Fin 6 → ℝ) in 𝓝 (t0, sStar), 0 < alphaOf p.2 := by
    have : Tendsto (fun p : ℝ × (Fin 6 → ℝ) => alphaOf p.2)
        (𝓝 (t0, sStar)) (𝓝 (alphaOf sStar)) :=
      continuousAt_alphaOf_sStar.tendsto.comp continuous_snd.continuousAt.tendsto
    have hpos : 0 < alphaOf sStar := by rw [alphaOf_sStar]; norm_num
    exact this.eventually (Ioi_mem_nhds hpos)
  have htarget : (chiData t0).toOpenPartialHomeomorph.target ∈ 𝓝 (t0, sStar) :=
    (chiData_open_target t0).mem_nhds (chiData_target_mem t0)
  filter_upwards [hα, eventually_chiProd_dchi_pos t0,
    Filter.eventually_of_mem htarget fun _ h => h] with p hαp hρp hmem
  refine ⟨hαp, hρp, ?_⟩
  have hf : HasDerivAt (univF p.2)
      (univF_dchi p.2 (chiProd t0 p.1 p.2)) (chiProd t0 p.1 p.2) :=
    hasDerivAt_univF_of_alpha_pos hαp
  exact (HasDerivAt.of_local_left_inverse
    (continuousAt_chiProd_slice t0 p.1 p.2 hmem) hf hρp.ne'
    (eventually_univF_chiProd_slice t0 p.1 p.2 hmem)).congr_deriv
    (by field_simp [hρp.ne'])

lemma hasDerivAt_univF_dchi {s : Fin 6 → ℝ} {χ : ℝ} (hα : 0 < alphaOf s) :
    HasDerivAt (univF_dchi s)
      (-rnorm s * Real.sqrt (alphaOf s) * Real.sin (Real.sqrt (alphaOf s) * χ)
        + sigmaOf s * Real.cos (Real.sqrt (alphaOf s) * χ)
        + Real.sin (Real.sqrt (alphaOf s) * χ) / Real.sqrt (alphaOf s)) χ := by
  have hα0 : alphaOf s ≠ 0 := hα.ne'
  have hω0 : Real.sqrt (alphaOf s) ≠ 0 := Real.sqrt_ne_zero'.2 hα
  have hωu : HasDerivAt (fun u => Real.sqrt (alphaOf s) * u)
      (Real.sqrt (alphaOf s)) χ := by
    simpa using (hasDerivAt_id χ).const_mul (Real.sqrt (alphaOf s))
  have h1 : HasDerivAt
      (fun u => rnorm s * Real.cos (Real.sqrt (alphaOf s) * u))
      (-rnorm s * Real.sin (Real.sqrt (alphaOf s) * χ) * Real.sqrt (alphaOf s)) χ := by
    refine ((hasDerivAt_const χ (rnorm s)).mul hωu.cos).congr_deriv ?_
    ring
  have h2 : HasDerivAt
      (fun u => sigmaOf s * Real.sin (Real.sqrt (alphaOf s) * u)
        / Real.sqrt (alphaOf s))
      (sigmaOf s * Real.cos (Real.sqrt (alphaOf s) * χ)) χ := by
    refine (((hasDerivAt_const χ (sigmaOf s)).mul hωu.sin).div_const
      (Real.sqrt (alphaOf s))).congr_deriv ?_
    field_simp [hω0]
    ring
  have h3 : HasDerivAt
      (fun u => (1 - Real.cos (Real.sqrt (alphaOf s) * u)) / alphaOf s)
      (Real.sin (Real.sqrt (alphaOf s) * χ) / Real.sqrt (alphaOf s)) χ := by
    have hnum : HasDerivAt (fun u => 1 - Real.cos (Real.sqrt (alphaOf s) * u))
        (Real.sin (Real.sqrt (alphaOf s) * χ) * Real.sqrt (alphaOf s)) χ := by
      refine ((hasDerivAt_const χ (1 : ℝ)).sub hωu.cos).congr_deriv ?_
      ring
    refine (hnum.div_const (alphaOf s)).congr_deriv ?_
    have hsq : Real.sqrt (alphaOf s) * Real.sqrt (alphaOf s) = alphaOf s :=
      Real.mul_self_sqrt hα.le
    field_simp [hα0, hω0]
    simp [pow_two, hsq]
    ring
  have hell := (h1.add h2).add h3
  have hfun : univF_dchi s = fun u =>
      rnorm s * Real.cos (Real.sqrt (alphaOf s) * u)
        + sigmaOf s * Real.sin (Real.sqrt (alphaOf s) * u) / Real.sqrt (alphaOf s)
        + (1 - Real.cos (Real.sqrt (alphaOf s) * u)) / alphaOf s :=
    funext fun u => rho_ell_eq s u hα
  rw [hfun]
  refine hell.congr_deriv ?_
  ring


/-! Time derivatives of f,g along `chiProd`, then Kepler for the local propagator. -/

lemma fg_f_chi_deriv (s : Fin 6 → ℝ) (χ : ℝ) (hα : 0 < alphaOf s)
    (hr : rnorm s ≠ 0) :
    deriv (fg_f s) χ =
      -Real.sin (Real.sqrt (alphaOf s) * χ) /
        (Real.sqrt (alphaOf s) * rnorm s) :=
  (hasDerivAt_fg_f_ell_chi hα hr).deriv

lemma fg_g_chi_deriv (s : Fin 6 → ℝ) (t χ : ℝ) (hα : 0 < alphaOf s) :
    deriv (fun ξ => fg_g s t ξ) χ =
      (Real.cos (Real.sqrt (alphaOf s) * χ) - 1) / alphaOf s :=
  (hasDerivAt_fg_g_ell_chi (s := s) (t := t) (χ := χ) hα).deriv

lemma univF_dchi_chi_deriv (s : Fin 6 → ℝ) (χ : ℝ) (hα : 0 < alphaOf s) :
    deriv (univF_dchi s) χ =
      -rnorm s * Real.sqrt (alphaOf s) * Real.sin (Real.sqrt (alphaOf s) * χ)
        + sigmaOf s * Real.cos (Real.sqrt (alphaOf s) * χ)
        + Real.sin (Real.sqrt (alphaOf s) * χ) / Real.sqrt (alphaOf s) :=
  (hasDerivAt_univF_dchi hα).deriv

lemma eventually_hasDerivAt_fg_f_chiProd (t0 : ℝ) :
    ∀ᶠ p : ℝ × (Fin 6 → ℝ) in 𝓝 (t0, sStar),
      HasDerivAt (fun τ => fg_f p.2 (chiProd t0 τ p.2))
        (deriv (fg_f p.2) (chiProd t0 p.1 p.2) *
          (univF_dchi p.2 (chiProd t0 p.1 p.2))⁻¹) p.1 := by
  have hr := eventually_rnorm_pos
  have hpath : Tendsto (fun p : ℝ × (Fin 6 → ℝ) => p.2) (𝓝 (t0, sStar)) (𝓝 sStar) :=
    continuous_snd.continuousAt
  filter_upwards [eventually_hasDerivAt_chiProd t0, hpath.eventually hr] with p hp hr0
  have hχ := hp.2.2
  have hf : HasDerivAt (fg_f p.2)
      (-Real.sin (Real.sqrt (alphaOf p.2) * chiProd t0 p.1 p.2) /
        (Real.sqrt (alphaOf p.2) * rnorm p.2))
      (chiProd t0 p.1 p.2) :=
    hasDerivAt_fg_f_ell_chi (s := p.2) (χ := chiProd t0 p.1 p.2) hp.1 hr0.ne'
  exact (hf.comp p.1 hχ).congr_deriv (by rw [← hf.deriv])

def psiOf (s : Fin 6 → ℝ) (ξ : ℝ) : ℝ :=
  ξ / alphaOf s
    - Real.sin (Real.sqrt (alphaOf s) * ξ) / (alphaOf s * Real.sqrt (alphaOf s))

lemma fg_g_ell_psi {s : Fin 6 → ℝ} {t ξ : ℝ} (hα : 0 < alphaOf s) :
    fg_g s t ξ = t - psiOf s ξ := by
  simpa [psiOf] using fg_g_ell (s := s) (t := t) (chi := ξ) hα

lemma hasDerivAt_psiOf {s : Fin 6 → ℝ} {t ξ : ℝ} (hα : 0 < alphaOf s) :
    HasDerivAt (psiOf s)
      (-deriv (fun u => fg_g s t u) ξ) ξ := by
  have hfg := hasDerivAt_fg_g_ell_chi (s := s) (t := t) (χ := ξ) hα
  have hfun : psiOf s = fun u => t - fg_g s t u := by
    funext u
    simp [psiOf, fg_g_ell_psi hα]
  rw [hfun]
  exact ((hasDerivAt_const ξ t).sub hfg).congr_deriv (by rw [hfg.deriv]; ring)

lemma eventually_hasDerivAt_fg_g_chiProd (t0 : ℝ) :
    ∀ᶠ p : ℝ × (Fin 6 → ℝ) in 𝓝 (t0, sStar),
      HasDerivAt (fun τ => fg_g p.2 τ (chiProd t0 τ p.2))
        (1 + deriv (fun ξ => fg_g p.2 p.1 ξ) (chiProd t0 p.1 p.2) *
          (univF_dchi p.2 (chiProd t0 p.1 p.2))⁻¹) p.1 := by
  filter_upwards [eventually_hasDerivAt_chiProd t0] with p hp
  have hχ := hp.2.2
  have hfun :
      (fun τ => fg_g p.2 τ (chiProd t0 τ p.2)) =
        fun τ => τ - psiOf p.2 (chiProd t0 τ p.2) := by
    funext τ
    exact fg_g_ell_psi (s := p.2) (t := τ) (ξ := chiProd t0 τ p.2) hp.1
  have hψ0 : HasDerivAt (psiOf p.2)
      (-deriv (fun ξ => fg_g p.2 p.1 ξ) (chiProd t0 p.1 p.2))
      (chiProd t0 p.1 p.2) :=
    hasDerivAt_psiOf (s := p.2) (t := p.1) (ξ := chiProd t0 p.1 p.2) hp.1
  have hψ : HasDerivAt (psiOf p.2 ∘ fun τ => chiProd t0 τ p.2)
      (-deriv (fun ξ => fg_g p.2 p.1 ξ) (chiProd t0 p.1 p.2) *
        (univF_dchi p.2 (chiProd t0 p.1 p.2))⁻¹) p.1 :=
    hψ0.comp p.1 hχ
  have hsum : HasDerivAt (fun τ => τ - psiOf p.2 (chiProd t0 τ p.2))
      (1 + deriv (fun ξ => fg_g p.2 p.1 ξ) (chiProd t0 p.1 p.2) *
        (univF_dchi p.2 (chiProd t0 p.1 p.2))⁻¹) p.1 :=
    ((hasDerivAt_id p.1).sub hψ).congr_deriv (by ring)
  exact hfun ▸ hsum

noncomputable def fChi (s : Fin 6 → ℝ) (χ : ℝ) : ℝ :=
  -Real.sin (Real.sqrt (alphaOf s) * χ) / (Real.sqrt (alphaOf s) * rnorm s)

noncomputable def gChi (s : Fin 6 → ℝ) (χ : ℝ) : ℝ :=
  (Real.cos (Real.sqrt (alphaOf s) * χ) - 1) / alphaOf s

noncomputable def rhoChi (s : Fin 6 → ℝ) (χ : ℝ) : ℝ :=
  -rnorm s * Real.sqrt (alphaOf s) * Real.sin (Real.sqrt (alphaOf s) * χ)
    + sigmaOf s * Real.cos (Real.sqrt (alphaOf s) * χ)
    + Real.sin (Real.sqrt (alphaOf s) * χ) / Real.sqrt (alphaOf s)

lemma fChi_eq {s : Fin 6 → ℝ} {χ : ℝ} (hα : 0 < alphaOf s) (hr : rnorm s ≠ 0) :
    fChi s χ = deriv (fg_f s) χ :=
  (fg_f_chi_deriv s χ hα hr).symm ▸ rfl

lemma gChi_eq {s : Fin 6 → ℝ} {t χ : ℝ} (hα : 0 < alphaOf s) :
    gChi s χ = deriv (fun ξ => fg_g s t ξ) χ :=
  (fg_g_chi_deriv s t χ hα).symm ▸ rfl

lemma rhoChi_eq {s : Fin 6 → ℝ} {χ : ℝ} (hα : 0 < alphaOf s) :
    rhoChi s χ = deriv (univF_dchi s) χ :=
  (univF_dchi_chi_deriv s χ hα).symm ▸ rfl

lemma battin_f_alg (α r0 σ ω c sn : ℝ)
    (hα : α ≠ 0) (hr : r0 ≠ 0) (hω : ω ≠ 0) (hw : ω ^ 2 = α)
    (hcs : c * c + sn * sn = 1) :
    (-c / r0) * (r0 * c + σ * sn / ω + (1 - c) / α)
      - (-sn / (ω * r0)) * (-r0 * ω * sn + σ * c + sn / ω)
      = -(1 - (1 - c) / (α * r0)) := by
  subst hw
  field_simp [hr, hω]
  grind

lemma battin_g_alg (α r0 σ ω c sn : ℝ)
    (hα : α ≠ 0) (hr : r0 ≠ 0) (hω : ω ≠ 0) (hw : ω ^ 2 = α)
    (hcs : c * c + sn * sn = 1) :
    (-sn / ω) * (r0 * c + σ * sn / ω + (1 - c) / α)
      - ((c - 1) / α) * (-r0 * ω * sn + σ * c + sn / ω)
      = -(σ * (1 - c) / α + r0 * sn / ω) := by
  subst hw
  field_simp [hr, hω]
  grind

lemma battin_f {s : Fin 6 → ℝ} {χ : ℝ} (hα : 0 < alphaOf s) :
    (-Real.cos (Real.sqrt (alphaOf s) * χ) / rnorm s) * univF_dchi s χ
      - fChi s χ * rhoChi s χ = -fg_f s χ := by
  have hr : rnorm s ≠ 0 := rnorm_ne_of_alpha_pos hα
  have hα0 : alphaOf s ≠ 0 := hα.ne'
  have hω : Real.sqrt (alphaOf s) ≠ 0 := Real.sqrt_ne_zero'.2 hα
  have hsq : Real.sqrt (alphaOf s) ^ 2 = alphaOf s := Real.sq_sqrt hα.le
  have hcs : Real.cos (Real.sqrt (alphaOf s) * χ)
        * Real.cos (Real.sqrt (alphaOf s) * χ)
      + Real.sin (Real.sqrt (alphaOf s) * χ)
        * Real.sin (Real.sqrt (alphaOf s) * χ) = 1 := by
    simpa [pow_two] using Real.cos_sq_add_sin_sq (Real.sqrt (alphaOf s) * χ)
  have hρ := rho_ell_eq s χ hα
  have hf := fg_f_ell (s := s) (chi := χ) hα
  simp only [fChi, rhoChi, hρ, hf]
  exact battin_f_alg (alphaOf s) (rnorm s) (sigmaOf s)
    (Real.sqrt (alphaOf s)) (Real.cos (Real.sqrt (alphaOf s) * χ))
    (Real.sin (Real.sqrt (alphaOf s) * χ)) hα0 hr hω hsq hcs

lemma battin_g {s : Fin 6 → ℝ} {t χ : ℝ} (hα : 0 < alphaOf s)
    (ht : univF s χ = t) :
    (-Real.sin (Real.sqrt (alphaOf s) * χ) / Real.sqrt (alphaOf s))
        * univF_dchi s χ
      - gChi s χ * rhoChi s χ = -fg_g s t χ := by
  have hr : rnorm s ≠ 0 := rnorm_ne_of_alpha_pos hα
  have hα0 : alphaOf s ≠ 0 := hα.ne'
  have hω : Real.sqrt (alphaOf s) ≠ 0 := Real.sqrt_ne_zero'.2 hα
  have hsq : Real.sqrt (alphaOf s) ^ 2 = alphaOf s := Real.sq_sqrt hα.le
  have hcs : Real.cos (Real.sqrt (alphaOf s) * χ)
        * Real.cos (Real.sqrt (alphaOf s) * χ)
      + Real.sin (Real.sqrt (alphaOf s) * χ)
        * Real.sin (Real.sqrt (alphaOf s) * χ) = 1 := by
    simpa [pow_two] using Real.cos_sq_add_sin_sq (Real.sqrt (alphaOf s) * χ)
  have hρ := rho_ell_eq s χ hα
  have hg := fg_g_of_kepler (s := s) (t := t) (χ := χ) hα ht
  simp only [gChi, rhoChi, hρ, hg]
  exact battin_g_alg (alphaOf s) (rnorm s) (sigmaOf s)
    (Real.sqrt (alphaOf s)) (Real.cos (Real.sqrt (alphaOf s) * χ))
    (Real.sin (Real.sqrt (alphaOf s) * χ)) hα0 hr hω hsq hcs

lemma vel_norm_sq {s : Fin 6 → ℝ} (hr : rnorm s ≠ 0) :
    ‖stateVel s‖ ^ 2 = 2 / rnorm s - alphaOf s := by
  simp [alphaOf]

lemma eventually_hasDerivAt_rho_chiProd (t0 : ℝ) :
    ∀ᶠ p : ℝ × (Fin 6 → ℝ) in 𝓝 (t0, sStar),
      HasDerivAt (fun τ => univF_dchi p.2 (chiProd t0 τ p.2))
        (rhoChi p.2 (chiProd t0 p.1 p.2) *
          (univF_dchi p.2 (chiProd t0 p.1 p.2))⁻¹) p.1 := by
  filter_upwards [eventually_hasDerivAt_chiProd t0] with p hp
  have hρ := hasDerivAt_univF_dchi (s := p.2) (χ := chiProd t0 p.1 p.2) hp.1
  refine (hρ.comp p.1 hp.2.2).congr_deriv ?_
  simp [rhoChi]

lemma eventually_hasDerivAt_chiProd2 (t0 : ℝ) :
    ∀ᶠ p : ℝ × (Fin 6 → ℝ) in 𝓝 (t0, sStar),
      HasDerivAt (fun τ => (univF_dchi p.2 (chiProd t0 τ p.2))⁻¹)
        (-rhoChi p.2 (chiProd t0 p.1 p.2) /
          (univF_dchi p.2 (chiProd t0 p.1 p.2)) ^ 3) p.1 := by
  filter_upwards [eventually_hasDerivAt_chiProd t0,
    eventually_hasDerivAt_rho_chiProd t0] with p hp hρt
  have hρ0 := hp.2.1
  have hinv := hρt.inv (ne_of_gt hρ0)
  refine hinv.congr_deriv ?_
  field_simp [hρ0.ne']

lemma eventually_hasDerivAt_fChi_chiProd (t0 : ℝ) :
    ∀ᶠ p : ℝ × (Fin 6 → ℝ) in 𝓝 (t0, sStar),
      HasDerivAt (fun τ => fChi p.2 (chiProd t0 τ p.2))
        ((-Real.cos (Real.sqrt (alphaOf p.2) * chiProd t0 p.1 p.2) / rnorm p.2) *
          (univF_dchi p.2 (chiProd t0 p.1 p.2))⁻¹) p.1 := by
  have hr := eventually_rnorm_pos
  have hpath : Tendsto (fun p : ℝ × (Fin 6 → ℝ) => p.2) (𝓝 (t0, sStar)) (𝓝 sStar) :=
    continuous_snd.continuousAt
  filter_upwards [eventually_hasDerivAt_chiProd t0, hpath.eventually hr] with p hp hr0
  have hf := hasDerivAt_fg_f_ell_chi2 (s := p.2) (χ := chiProd t0 p.1 p.2) hp.1 hr0.ne'
  unfold fChi
  exact hf.comp p.1 hp.2.2

lemma eventually_hasDerivAt_gChi_chiProd (t0 : ℝ) :
    ∀ᶠ p : ℝ × (Fin 6 → ℝ) in 𝓝 (t0, sStar),
      HasDerivAt (fun τ => gChi p.2 (chiProd t0 τ p.2))
        ((-Real.sin (Real.sqrt (alphaOf p.2) * chiProd t0 p.1 p.2)
            / Real.sqrt (alphaOf p.2)) *
          (univF_dchi p.2 (chiProd t0 p.1 p.2))⁻¹) p.1 := by
  filter_upwards [eventually_hasDerivAt_chiProd t0] with p hp
  have hg := hasDerivAt_fg_g_ell_chi2 (s := p.2) (χ := chiProd t0 p.1 p.2) hp.1
  unfold gChi
  exact hg.comp p.1 hp.2.2

lemma f_ddot_alg (a b c ρ f : ℝ) (hρ : ρ ≠ 0)
    (hb : a * ρ - b * c = -f) :
    a * ρ⁻¹ * ρ⁻¹ + b * (-c / ρ ^ 3) = -f / ρ ^ 3 := by
  field_simp [hρ] at hb ⊢
  linear_combination hb

lemma eventually_hasDerivAt_f_ddot (t0 : ℝ) :
    ∀ᶠ p : ℝ × (Fin 6 → ℝ) in 𝓝 (t0, sStar),
      HasDerivAt
        (fun τ => fChi p.2 (chiProd t0 τ p.2) *
          (univF_dchi p.2 (chiProd t0 τ p.2))⁻¹)
        (-fg_f p.2 (chiProd t0 p.1 p.2) /
          univF_dchi p.2 (chiProd t0 p.1 p.2) ^ 3) p.1 := by
  filter_upwards [eventually_hasDerivAt_fChi_chiProd t0,
    eventually_hasDerivAt_chiProd2 t0,
    eventually_hasDerivAt_chiProd t0] with p hf hinv hp
  have hα := hp.1
  have hρpos := hp.2.1
  have hρne : univF_dchi p.2 (chiProd t0 p.1 p.2) ≠ 0 := hρpos.ne'
  have hmul := hf.mul hinv
  refine hmul.congr_deriv ?_
  have hb := battin_f (s := p.2) (χ := chiProd t0 p.1 p.2) hα
  exact f_ddot_alg _ _ _ _ _ hρne hb

lemma eventually_hasDerivAt_g_ddot (t0 : ℝ) :
    ∀ᶠ p : ℝ × (Fin 6 → ℝ) in 𝓝 (t0, sStar),
      HasDerivAt
        (fun τ => 1 + gChi p.2 (chiProd t0 τ p.2) *
          (univF_dchi p.2 (chiProd t0 τ p.2))⁻¹)
        (-fg_g p.2 p.1 (chiProd t0 p.1 p.2) /
          univF_dchi p.2 (chiProd t0 p.1 p.2) ^ 3) p.1 := by
  filter_upwards [eventually_hasDerivAt_gChi_chiProd t0,
    eventually_hasDerivAt_chiProd2 t0,
    eventually_hasDerivAt_chiProd t0,
    eventually_univF_chiProd t0] with p hg hinv hp ht
  have hα := hp.1
  have hρpos := hp.2.1
  have hρne : univF_dchi p.2 (chiProd t0 p.1 p.2) ≠ 0 := hρpos.ne'
  have hmul := hg.mul hinv
  have hone : HasDerivAt (fun _ : ℝ => (1 : ℝ)) 0 p.1 := hasDerivAt_const _ _
  have hsum := hone.add hmul
  refine hsum.congr_deriv ?_
  have hb := battin_g (s := p.2) (t := p.1) (χ := chiProd t0 p.1 p.2) hα ht
  have halg := f_ddot_alg _ _ _ _ _ hρne hb
  simpa using halg

lemma radius_sq_alg (α r0 σ ω c sn : ℝ)
    (hα : α ≠ 0) (hr : r0 ≠ 0) (hω : ω ≠ 0) (hw : ω ^ 2 = α)
    (hcs : c * c + sn * sn = 1) :
    (1 - (1 - c) / (α * r0)) ^ 2 * r0 ^ 2
      + 2 * (1 - (1 - c) / (α * r0)) *
        (σ * (1 - c) / α + r0 * sn / ω) * σ
      + (σ * (1 - c) / α + r0 * sn / ω) ^ 2 * (2 / r0 - α)
      = (r0 * c + σ * sn / ω + (1 - c) / α) ^ 2 := by
  subst hw
  field_simp [hr, hω]
  grind

lemma kepler_fg_norm_sq {s : Fin 6 → ℝ} {t χ : ℝ}
    (hα : 0 < alphaOf s) (ht : univF s χ = t) :
    ‖fg_f s χ • statePos s + fg_g s t χ • stateVel s‖ ^ 2
      = univF_dchi s χ ^ 2 := by
  have hr : rnorm s ≠ 0 := rnorm_ne_of_alpha_pos hα
  have hα0 : alphaOf s ≠ 0 := hα.ne'
  have hω : Real.sqrt (alphaOf s) ≠ 0 := Real.sqrt_ne_zero'.2 hα
  have hsq : Real.sqrt (alphaOf s) ^ 2 = alphaOf s := Real.sq_sqrt hα.le
  have hcs : Real.cos (Real.sqrt (alphaOf s) * χ)
        * Real.cos (Real.sqrt (alphaOf s) * χ)
      + Real.sin (Real.sqrt (alphaOf s) * χ)
        * Real.sin (Real.sqrt (alphaOf s) * χ) = 1 := by
    simpa [pow_two] using Real.cos_sq_add_sin_sq (Real.sqrt (alphaOf s) * χ)
  have hf := fg_f_ell (s := s) (chi := χ) hα
  have hg := fg_g_of_kepler (s := s) (t := t) (χ := χ) hα ht
  have hρ := rho_ell_eq s χ hα
  have hv := vel_norm_sq (s := s) hr
  have hx : ‖fg_f s χ • statePos s‖ ^ 2 = fg_f s χ ^ 2 * rnorm s ^ 2 := by
    rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, rnorm]
  have hy : ‖fg_g s t χ • stateVel s‖ ^ 2
      = fg_g s t χ ^ 2 * ‖stateVel s‖ ^ 2 := by
    rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  have hin : ⟪fg_f s χ • statePos s, fg_g s t χ • stateVel s⟫
      = fg_f s χ * fg_g s t χ * sigmaOf s := by
    rw [real_inner_smul_left, real_inner_smul_right, ← vecDot_eq_inner, sigmaOf]
    ring
  rw [norm_add_sq_real, hx, hy, hin, hf, hg, hρ, hv]
  convert radius_sq_alg (alphaOf s) (rnorm s) (sigmaOf s)
    (Real.sqrt (alphaOf s)) (Real.cos (Real.sqrt (alphaOf s) * χ))
    (Real.sin (Real.sqrt (alphaOf s) * χ)) hα0 hr hω hsq hcs using 1
  ring

lemma kepler_fg_norm {s : Fin 6 → ℝ} {t χ : ℝ}
    (hα : 0 < alphaOf s) (ht : univF s χ = t)
    (hρ : 0 < univF_dchi s χ) :
    ‖fg_f s χ • statePos s + fg_g s t χ • stateVel s‖
      = univF_dchi s χ := by
  have hsq := kepler_fg_norm_sq hα ht
  have hnn : 0 ≤ univF_dchi s χ := hρ.le
  exact (sq_eq_sq₀ (norm_nonneg _) hnn).mp hsq

noncomputable def fDot (s : Fin 6 → ℝ) (χ : ℝ) : ℝ :=
  fChi s χ * (univF_dchi s χ)⁻¹

noncomputable def gDot (s : Fin 6 → ℝ) (χ : ℝ) : ℝ :=
  1 + gChi s χ * (univF_dchi s χ)⁻¹

noncomputable def propagator (t0 : ℝ) (s : Fin 6 → ℝ) (t : ℝ) : Vec :=
  fg_f s (chiProd t0 t s) • statePos s + fg_g s t (chiProd t0 t s) • stateVel s

noncomputable def propagatorVel (t0 : ℝ) (s : Fin 6 → ℝ) (t : ℝ) : Vec :=
  fDot s (chiProd t0 t s) • statePos s + gDot s (chiProd t0 t s) • stateVel s

lemma eventually_hasDerivAt_propagator (t0 : ℝ) :
    ∀ᶠ p : ℝ × (Fin 6 → ℝ) in 𝓝 (t0, sStar),
      HasDerivAt (propagator t0 p.2) (propagatorVel t0 p.2 p.1) p.1 := by
  filter_upwards [eventually_hasDerivAt_fg_f_chiProd t0,
    eventually_hasDerivAt_fg_g_chiProd t0,
    eventually_hasDerivAt_chiProd t0] with p hf hg hp
  have hr : rnorm p.2 ≠ 0 := rnorm_ne_of_alpha_pos hp.1
  have hf' : HasDerivAt (fun τ => fg_f p.2 (chiProd t0 τ p.2))
      (fDot p.2 (chiProd t0 p.1 p.2)) p.1 :=
    hf.congr_deriv (by simp [fDot, fChi_eq hp.1 hr])
  have hg' : HasDerivAt (fun τ => fg_g p.2 τ (chiProd t0 τ p.2))
      (gDot p.2 (chiProd t0 p.1 p.2)) p.1 :=
    hg.congr_deriv (by rw [gDot, ← gChi_eq (s := p.2) (t := p.1) hp.1])
  have h1 := hf'.smul_const (statePos p.2)
  have h2 := hg'.smul_const (stateVel p.2)
  have hsum := h1.add h2
  have hfun : propagator t0 p.2 =
      (fun y => fg_f p.2 (chiProd t0 y p.2) • statePos p.2)
        + fun y => fg_g p.2 y (chiProd t0 y p.2) • stateVel p.2 := by
    funext y; simp [propagator, Pi.add_apply]
  simpa [hfun, propagatorVel] using hsum

lemma eventually_hasDerivAt_propagator_vel (t0 : ℝ) :
    ∀ᶠ p : ℝ × (Fin 6 → ℝ) in 𝓝 (t0, sStar),
      HasDerivAt (propagatorVel t0 p.2)
        (-(1 / univF_dchi p.2 (chiProd t0 p.1 p.2) ^ 3) •
          propagator t0 p.2 p.1) p.1 := by
  filter_upwards [eventually_hasDerivAt_f_ddot t0,
    eventually_hasDerivAt_g_ddot t0] with p hf hg
  have hf' : HasDerivAt (fun τ => fDot p.2 (chiProd t0 τ p.2))
      (-fg_f p.2 (chiProd t0 p.1 p.2) /
        univF_dchi p.2 (chiProd t0 p.1 p.2) ^ 3) p.1 := by
    simpa [fDot] using hf
  have hg' : HasDerivAt (fun τ => gDot p.2 (chiProd t0 τ p.2))
      (-fg_g p.2 p.1 (chiProd t0 p.1 p.2) /
        univF_dchi p.2 (chiProd t0 p.1 p.2) ^ 3) p.1 := by
    simpa [gDot] using hg
  have h1 := hf'.smul_const (statePos p.2)
  have h2 := hg'.smul_const (stateVel p.2)
  have hsum := h1.add h2
  have hfun : propagatorVel t0 p.2 =
      (fun y => fDot p.2 (chiProd t0 y p.2) • statePos p.2)
        + fun y => gDot p.2 (chiProd t0 y p.2) • stateVel p.2 := by
    funext y; simp [propagatorVel, Pi.add_apply]
  rw [hfun]
  refine hsum.congr_deriv ?_
  simp [propagator, smul_add, smul_smul, div_eq_mul_inv, mul_comm]

lemma eventually_propagator_kepler (t0 : ℝ) :
    ∀ᶠ p : ℝ × (Fin 6 → ℝ) in 𝓝 (t0, sStar),
      propagator t0 p.2 p.1 ≠ 0 ∧
        HasDerivAt (propagator t0 p.2) (propagatorVel t0 p.2 p.1) p.1 ∧
        HasDerivAt (propagatorVel t0 p.2)
          (-(1 / ‖propagator t0 p.2 p.1‖ ^ 3) • propagator t0 p.2 p.1) p.1 := by
  filter_upwards [eventually_hasDerivAt_propagator t0,
    eventually_hasDerivAt_propagator_vel t0,
    eventually_hasDerivAt_chiProd t0,
    eventually_univF_chiProd t0] with p hpos hvel hp ht
  have hρ := hp.2.1
  have hnorm := kepler_fg_norm (s := p.2) (t := p.1)
    (χ := chiProd t0 p.1 p.2) hp.1 ht hρ
  have hne : propagator t0 p.2 p.1 ≠ 0 := by
    intro h0
    have : ‖propagator t0 p.2 p.1‖ = univF_dchi p.2 (chiProd t0 p.1 p.2) := by
      simpa [propagator] using hnorm
    rw [h0, norm_zero] at this
    exact hρ.ne' this.symm
  refine ⟨hne, hpos, ?_⟩
  refine hvel.congr_deriv ?_
  have : ‖propagator t0 p.2 p.1‖ = univF_dchi p.2 (chiProd t0 p.1 p.2) := by
    simpa [propagator] using hnorm
  rw [this]

lemma eventually_chiOf_eq_chiProd_diag (t : ℝ) :
    ∀ᶠ s in 𝓝 sStar, chiOf s t = chiProd t t s := by
  have hiff := eventually_apply_eq_iff_implicitFunctionOfBivariate
    (eventually_hasFDerivAt_univF_s (2 * t / 5))
    (eventually_hasFDerivAt_univF_chi (2 * t / 5))
    (continuousAt_univF_f1 (2 * t / 5))
    (continuousAt_univF_f2 (2 * t / 5))
    (univF_f2_invertible t)
  have hslice : ∀ᶠ s in 𝓝 sStar, univF s (chiProd t t s) = t := by
    have hpath : Tendsto (fun s : Fin 6 → ℝ => (t, s)) (𝓝 sStar) (𝓝 (t, sStar)) :=
      tendsto_const_nhds.prodMk_nhds tendsto_id
    exact hpath.eventually (eventually_univF_chiProd t)
  have hχ : Tendsto (fun s : Fin 6 → ℝ => chiProd t t s) (𝓝 sStar) (𝓝 (2 * t / 5)) := by
    have hc := (continuousAt_chiProd t).comp
      (continuousAt_const.prodMk (continuousAt_id : ContinuousAt (fun s : Fin 6 → ℝ => s) sStar))
    have hfun : (fun s : Fin 6 → ℝ => chiProd t t s) =
        (fun p : ℝ × (Fin 6 → ℝ) => chiProd t p.1 p.2) ∘ Prod.mk t := rfl
    rw [hfun]
    simpa [chiProd_center t] using hc.tendsto
  have htend : Tendsto (fun s : Fin 6 → ℝ => (s, chiProd t t s)) (𝓝 sStar)
      (𝓝 (sStar, 2 * t / 5)) :=
    tendsto_id.prodMk_nhds hχ
  have hiff' : ∀ᶠ s in 𝓝 sStar,
      univF s (chiProd t t s) = t ↔ chiOf s t = chiProd t t s := by
    have : ∀ᶠ v : (Fin 6 → ℝ) × ℝ in 𝓝 (sStar, 2 * t / 5),
        univF v.1 v.2 = t ↔ chiOf v.1 t = v.2 := by
      refine hiff.mono ?_
      intro v hv
      simpa [univF_sStar, chiOf] using hv
    exact htend.eventually this
  filter_upwards [hiff', hslice] with s hiffs hs
  exact hiffs.mp hs

lemma eventually_keplerIC_eq_propagator_diag (t : ℝ) :
    ∀ᶠ s in 𝓝 sStar, keplerIC s t = propagator t s t := by
  filter_upwards [eventually_chiOf_eq_chiProd_diag t] with s hs
  simp [keplerIC, propagator, hs]

lemma chiData_mem_source (t0 : ℝ) :
    (sStar, 2 * t0 / 5) ∈ (chiData t0).toOpenPartialHomeomorph.source :=
  (chiData t0).pt_mem_toOpenPartialHomeomorph_source

lemma chiData_left_inv {t0 : ℝ} {s : Fin 6 → ℝ} {χ : ℝ}
    (h : (s, χ) ∈ (chiData t0).toOpenPartialHomeomorph.source) :
    (chiData t0).implicitFunction (univF s χ) s = (s, χ) := by
  have hmap : (chiData t0).toOpenPartialHomeomorph (s, χ) = (univF s χ, s) := by
    rw [ImplicitFunctionData.toOpenPartialHomeomorph_coe, ImplicitFunctionData.prodFun_apply]
    simp [chiData_leftFun, chiData_rightFun, Function.uncurry]
  have hleft := (chiData t0).toOpenPartialHomeomorph.left_inv h
  simpa [ImplicitFunctionData.implicitFunction, Function.curry, hmap] using hleft

lemma chiProd_unique_of_mem_source {t0 : ℝ} {s : Fin 6 → ℝ} {χ : ℝ}
    (h : (s, χ) ∈ (chiData t0).toOpenPartialHomeomorph.source) :
    chiProd t0 (univF s χ) s = χ :=
  congrArg Prod.snd (chiData_left_inv h)

lemma continuousAt_chiProd_mem {t0 t : ℝ} {s : Fin 6 → ℝ}
    (h : (t, s) ∈ (chiData t0).toOpenPartialHomeomorph.target) :
    ContinuousAt (fun p : ℝ × (Fin 6 → ℝ) => chiProd t0 p.1 p.2) (t, s) :=
  continuousAt_snd.comp ((chiData t0).toOpenPartialHomeomorph.continuousAt_symm h)

lemma eventually_chiProd_sStar_eq (t0 : ℝ) :
    ∀ᶠ t in 𝓝 t0, chiProd t0 t sStar = 2 * t / 5 ∧
      (t, sStar) ∈ (chiData t0).toOpenPartialHomeomorph.target := by
  have hT := (chiData_open_target t0).mem_nhds (chiData_target_mem t0)
  have hpath : Tendsto (fun t : ℝ => (t, sStar)) (𝓝 t0) (𝓝 (t0, sStar)) :=
    tendsto_id.prodMk_nhds tendsto_const_nhds
  filter_upwards [eventually_chiProd_sStar t0,
    hpath.eventually (Filter.eventually_of_mem hT fun _ h => h)] with t hχ ht
  exact ⟨hχ, ht⟩

lemma eventually_chiOf_eq_chiProd_slice_near (t0 t1 : ℝ)
    (hχ : chiProd t0 t1 sStar = 2 * t1 / 5)
    (ht : (t1, sStar) ∈ (chiData t0).toOpenPartialHomeomorph.target) :
    ∀ᶠ s in 𝓝 sStar, chiOf s t1 = chiProd t0 t1 s := by
  have hiff := eventually_apply_eq_iff_implicitFunctionOfBivariate
    (eventually_hasFDerivAt_univF_s (2 * t1 / 5))
    (eventually_hasFDerivAt_univF_chi (2 * t1 / 5))
    (continuousAt_univF_f1 (2 * t1 / 5))
    (continuousAt_univF_f2 (2 * t1 / 5))
    (univF_f2_invertible t1)
  have hcont := continuousAt_chiProd_mem (t0 := t0) (t := t1) (s := sStar) ht
  have htend : Tendsto (fun s : Fin 6 → ℝ => (s, chiProd t0 t1 s)) (𝓝 sStar)
      (𝓝 (sStar, 2 * t1 / 5)) := by
    have hs : Tendsto (fun s : Fin 6 → ℝ => s) (𝓝 sStar) (𝓝 sStar) := tendsto_id
    have hχt : Tendsto (fun s : Fin 6 → ℝ => chiProd t0 t1 s) (𝓝 sStar)
        (𝓝 (2 * t1 / 5)) := by
      have hp : ContinuousAt (fun s : Fin 6 → ℝ => (t1, s)) sStar :=
        continuousAt_const.prodMk continuousAt_id
      have : Tendsto (fun s : Fin 6 → ℝ => chiProd t0 t1 s) (𝓝 sStar)
          (𝓝 (chiProd t0 t1 sStar)) :=
        (hcont.comp hp).tendsto
      simpa [hχ] using this
    exact hs.prodMk_nhds hχt
  have hF : ∀ᶠ s in 𝓝 sStar, univF s (chiProd t0 t1 s) = t1 := by
    have hpath : Tendsto (fun s : Fin 6 → ℝ => (t1, s)) (𝓝 sStar) (𝓝 (t1, sStar)) :=
      tendsto_const_nhds.prodMk_nhds tendsto_id
    have hnhds := (chiData_open_target t0).mem_nhds ht
    have hmem : ∀ᶠ s in 𝓝 sStar,
        (t1, s) ∈ (chiData t0).toOpenPartialHomeomorph.target :=
      hpath.eventually (Filter.eventually_of_mem hnhds fun _ h => h)
    filter_upwards [hmem] with s hs
    exact (chiData_right_inv t0 t1 s hs).1
  have hiff' : ∀ᶠ s in 𝓝 sStar,
      univF s (chiProd t0 t1 s) = t1 ↔ chiOf s t1 = chiProd t0 t1 s := by
    have : ∀ᶠ v : (Fin 6 → ℝ) × ℝ in 𝓝 (sStar, 2 * t1 / 5),
        univF v.1 v.2 = t1 ↔ chiOf v.1 t1 = v.2 := by
      refine hiff.mono ?_
      intro v hv
      simpa [univF_sStar, chiOf] using hv
    exact htend.eventually this
  filter_upwards [hiff', hF] with s hiffs hs
  exact hiffs.mp hs

lemma eventually_chiOf_eq_chiProd_near_times (t0 : ℝ) :
    ∀ᶠ t in 𝓝 t0, ∀ᶠ s in 𝓝 sStar, chiOf s t = chiProd t0 t s := by
  filter_upwards [eventually_chiProd_sStar_eq t0] with t ht
  exact eventually_chiOf_eq_chiProd_slice_near t0 t ht.1 ht.2

lemma chiData_open_source (t0 : ℝ) :
    IsOpen (chiData t0).toOpenPartialHomeomorph.source :=
  (chiData t0).toOpenPartialHomeomorph.open_source

lemma exists_ball_subset_chiData_source (t0 : ℝ) :
    ∃ r > (0 : ℝ), Metric.ball (sStar, 2 * t0 / 5) r ⊆
      (chiData t0).toOpenPartialHomeomorph.source :=
  Metric.mem_nhds_iff.mp
    ((chiData_open_source t0).mem_nhds (chiData_mem_source t0))

lemma chiOf_eq_chiProd_of_univF_mem_source {t0 t : ℝ} {s : Fin 6 → ℝ}
    (hF : univF s (chiOf s t) = t)
    (hsrc : (s, chiOf s t) ∈ (chiData t0).toOpenPartialHomeomorph.source) :
    chiOf s t = chiProd t0 t s :=
  (chiProd_unique_of_mem_source hsrc).symm.trans (by rw [hF])

lemma tendsto_chiProd_center_line (t0 : ℝ) :
    Tendsto (fun p : ℝ × (Fin 6 → ℝ) => (p.2, chiProd t0 p.1 p.2))
      (𝓝 (t0, sStar)) (𝓝 (sStar, 2 * t0 / 5)) := by
  have hs : Tendsto (fun p : ℝ × (Fin 6 → ℝ) => p.2) (𝓝 (t0, sStar)) (𝓝 sStar) :=
    continuous_snd.continuousAt
  have hχ : Tendsto (fun p : ℝ × (Fin 6 → ℝ) => chiProd t0 p.1 p.2)
      (𝓝 (t0, sStar)) (𝓝 (2 * t0 / 5)) := by
    simpa [chiProd_center t0] using (continuousAt_chiProd t0).tendsto
  exact hs.prodMk_nhds hχ

lemma tendsto_chiProd_sub_two_fifths (t0 : ℝ) :
    Tendsto (fun p : ℝ × (Fin 6 → ℝ) =>
        (p.2, chiProd t0 p.1 p.2) - (sStar, 2 * p.1 / 5))
      (𝓝 (t0, sStar)) (𝓝 0) := by
  have hγ := tendsto_chiProd_center_line t0
  have hc : Tendsto (fun p : ℝ × (Fin 6 → ℝ) => (sStar, 2 * p.1 / 5))
      (𝓝 (t0, sStar)) (𝓝 (sStar, 2 * t0 / 5)) := by
    have h1 : Tendsto (fun _ : ℝ × (Fin 6 → ℝ) => sStar) (𝓝 (t0, sStar)) (𝓝 sStar) :=
      tendsto_const_nhds
    have h2 : Tendsto (fun p : ℝ × (Fin 6 → ℝ) => 2 * p.1 / 5)
        (𝓝 (t0, sStar)) (𝓝 (2 * t0 / 5)) := by
      have : Tendsto (fun p : ℝ × (Fin 6 → ℝ) => p.1) (𝓝 (t0, sStar)) (𝓝 t0) :=
        continuous_fst.continuousAt
      simpa using this.const_mul 2 |>.div_const 5
    exact h1.prodMk_nhds h2
  simpa [sub_eq_add_neg] using hγ.sub hc

lemma chiProd_mem_source {t0 t : ℝ} {s : Fin 6 → ℝ}
    (h : (t, s) ∈ (chiData t0).toOpenPartialHomeomorph.target) :
    (s, chiProd t0 t s) ∈ (chiData t0).toOpenPartialHomeomorph.source := by
  have hs := (chiData t0).toOpenPartialHomeomorph.map_target h
  have h1 : ((chiData t0).implicitFunction t s).1 = s := (chiData_right_inv t0 t s h).2
  change (chiData t0).implicitFunction t s ∈
      (chiData t0).toOpenPartialHomeomorph.source at hs
  have : (chiData t0).implicitFunction t s = (s, chiProd t0 t s) := by
    ext <;> simp [chiProd, h1]
  rwa [this] at hs

lemma eventually_chiProd_mem_source (t0 : ℝ) :
    ∀ᶠ p : ℝ × (Fin 6 → ℝ) in 𝓝 (t0, sStar),
      (p.2, chiProd t0 p.1 p.2) ∈ (chiData t0).toOpenPartialHomeomorph.source := by
  have hT : (chiData t0).toOpenPartialHomeomorph.target ∈ 𝓝 (t0, sStar) :=
    (chiData_open_target t0).mem_nhds (chiData_target_mem t0)
  filter_upwards [Filter.eventually_of_mem hT fun _ h => h] with p hp
  exact chiProd_mem_source hp

lemma eventually_dist_chiProd_center_line (t0 : ℝ) {r : ℝ} (hr : 0 < r) :
    ∀ᶠ p : ℝ × (Fin 6 → ℝ) in 𝓝 (t0, sStar),
      dist (p.2, chiProd t0 p.1 p.2) (sStar, 2 * p.1 / 5) < r := by
  have h0 := tendsto_chiProd_sub_two_fifths t0
  have hb : {q : (Fin 6 → ℝ) × ℝ | ‖q‖ < r} ∈ 𝓝 (0 : (Fin 6 → ℝ) × ℝ) := by
    simpa [Metric.ball, dist_eq_norm] using
      Metric.ball_mem_nhds (0 : (Fin 6 → ℝ) × ℝ) hr
  filter_upwards [h0.eventually hb] with p hp
  simpa [dist_eq_norm] using hp

lemma tendsto_chiOf (t : ℝ) :
    Tendsto (fun s : Fin 6 → ℝ => chiOf s t) (𝓝 sStar) (𝓝 (2 * t / 5)) := by
  have h := tendsto_implicitFunctionOfBivariate
    (eventually_hasFDerivAt_univF_s (2 * t / 5))
    (eventually_hasFDerivAt_univF_chi (2 * t / 5))
    (continuousAt_univF_f1 (2 * t / 5))
    (continuousAt_univF_f2 (2 * t / 5))
    (univF_f2_invertible t)
  simpa [chiOf] using h

lemma tendsto_pair_chiOf (t : ℝ) :
    Tendsto (fun s : Fin 6 → ℝ => (s, chiOf s t)) (𝓝 sStar)
      (𝓝 (sStar, 2 * t / 5)) :=
  tendsto_id.prodMk_nhds (tendsto_chiOf t)

lemma eventually_pair_chiOf_mem_ball (t : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ s in 𝓝 sStar, dist (s, chiOf s t) (sStar, 2 * t / 5) < ε := by
  exact (tendsto_pair_chiOf t).eventually (Metric.ball_mem_nhds _ hε)

lemma dist_center_two_fifths (t0 t : ℝ) :
    dist (sStar, 2 * t / 5) (sStar, 2 * t0 / 5) = |2 * t / 5 - 2 * t0 / 5| := by
  rw [dist_prod_same_left, Real.dist_eq]

lemma exists_delta_center_in_half_ball (t0 : ℝ) {r : ℝ} (hr : 0 < r) :
    ∃ δ > (0 : ℝ), ∀ t ∈ Set.Icc (t0 - δ) (t0 + δ),
      dist (sStar, 2 * t / 5) (sStar, 2 * t0 / 5) < r / 2 := by
  refine ⟨r, hr, ?_⟩
  intro t ht
  have habs : |t - t0| ≤ r := abs_le.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩
  rw [dist_center_two_fifths,
    show 2 * t / 5 - 2 * t0 / 5 = (2 / 5) * (t - t0) by ring, abs_mul,
    abs_of_pos (by norm_num : (0 : ℝ) < 2 / 5)]
  nlinarith

lemma eventually_chiOf_mem_source_of_center (t0 t : ℝ) {r : ℝ}
    (hr : 0 < r)
    (hsub : Metric.ball (sStar, 2 * t0 / 5) r ⊆
      (chiData t0).toOpenPartialHomeomorph.source)
    (hctr : dist (sStar, 2 * t / 5) (sStar, 2 * t0 / 5) < r / 2) :
    ∀ᶠ s in 𝓝 sStar,
      (s, chiOf s t) ∈ (chiData t0).toOpenPartialHomeomorph.source := by
  have hε : 0 < r / 2 := half_pos hr
  filter_upwards [eventually_pair_chiOf_mem_ball t hε] with s hs
  have hsum : dist (s, chiOf s t) (sStar, 2 * t / 5)
      + dist (sStar, 2 * t / 5) (sStar, 2 * t0 / 5) < r := by
    have : r / 2 + r / 2 = r := by ring
    linarith
  exact hsub ((dist_triangle _ (sStar, 2 * t / 5) _).trans_lt hsum)

lemma eventually_chiOf_eq_chiProd_of_source (t0 t : ℝ)
    (hmem : ∀ᶠ s in 𝓝 sStar,
      (s, chiOf s t) ∈ (chiData t0).toOpenPartialHomeomorph.source) :
    ∀ᶠ s in 𝓝 sStar, chiOf s t = chiProd t0 t s := by
  filter_upwards [eventually_univF_chiOf t, hmem] with s hF hsrc
  exact chiOf_eq_chiProd_of_univF_mem_source hF hsrc

lemma exists_Icc_chiOf_eq_chiProd_slice (t0 : ℝ) :
    ∃ δ > (0 : ℝ), ∀ t ∈ Set.Icc (t0 - δ) (t0 + δ),
      ∀ᶠ s in 𝓝 sStar, chiOf s t = chiProd t0 t s := by
  obtain ⟨r, hr, hsub⟩ := exists_ball_subset_chiData_source t0
  obtain ⟨δ, hδ, hctr⟩ := exists_delta_center_in_half_ball t0 hr
  refine ⟨δ, hδ, ?_⟩
  intro t ht
  exact eventually_chiOf_eq_chiProd_of_source t0 t
    (eventually_chiOf_mem_source_of_center t0 t hr hsub (hctr t ht))

lemma exists_Icc_keplerIC_eq_propagator_slice (t0 : ℝ) :
    ∃ δ > (0 : ℝ), ∀ t ∈ Set.Icc (t0 - δ) (t0 + δ),
      ∀ᶠ s in 𝓝 sStar, keplerIC s t = propagator t0 s t := by
  obtain ⟨δ, hδ, h⟩ := exists_Icc_chiOf_eq_chiProd_slice t0
  refine ⟨δ, hδ, ?_⟩
  intro t ht
  filter_upwards [h t ht] with s hs
  simp [keplerIC, propagator, hs]

lemma chiProd_sStar_of_mem_target {t0 t : ℝ}
    (ht : (t, sStar) ∈ (chiData t0).toOpenPartialHomeomorph.target) :
    chiProd t0 t sStar = 2 * t / 5 := by
  have hF := (chiData_right_inv t0 t sStar ht).1
  have : (5 / 2) * chiProd t0 t sStar = t := by
    rw [← univF_sStar, hF]
  linarith

lemma eventually_propagator_kepler_ball (t0 : ℝ) :
    ∃ r > (0 : ℝ), ∀ p : ℝ × (Fin 6 → ℝ),
      dist p (t0, sStar) < r →
        propagator t0 p.2 p.1 ≠ 0 ∧
          HasDerivAt (propagator t0 p.2) (propagatorVel t0 p.2 p.1) p.1 ∧
          HasDerivAt (propagatorVel t0 p.2)
            (-(1 / ‖propagator t0 p.2 p.1‖ ^ 3) • propagator t0 p.2 p.1) p.1 := by
  have h := eventually_propagator_kepler t0
  rcases Metric.mem_nhds_iff.mp h with ⟨r, hr, hsub⟩
  refine ⟨r, hr, ?_⟩
  intro p hp
  exact hsub hp

lemma eventually_propagator_kepler_prod (t0 t : ℝ) {r : ℝ}
    (hr : 0 < r)
    (hball : ∀ p : ℝ × (Fin 6 → ℝ), dist p (t0, sStar) < r →
      propagator t0 p.2 p.1 ≠ 0 ∧
        HasDerivAt (propagator t0 p.2) (propagatorVel t0 p.2 p.1) p.1 ∧
        HasDerivAt (propagatorVel t0 p.2)
          (-(1 / ‖propagator t0 p.2 p.1‖ ^ 3) • propagator t0 p.2 p.1) p.1)
    (ht : dist (t, sStar) (t0, sStar) < r) :
    ∀ᶠ z : (Fin 6 → ℝ) × ℝ in 𝓝 (sStar, t),
      propagator t0 z.1 z.2 ≠ 0 ∧
        HasDerivAt (propagator t0 z.1) (propagatorVel t0 z.1 z.2) z.2 ∧
        HasDerivAt (propagatorVel t0 z.1)
          (-(1 / ‖propagator t0 z.1 z.2‖ ^ 3) • propagator t0 z.1 z.2) z.2 := by
  have hpos : 0 < r - dist (t, sStar) (t0, sStar) := sub_pos.mpr ht
  have hb : Metric.ball (t, sStar) (r - dist (t, sStar) (t0, sStar)) ∈ 𝓝 (t, sStar) :=
    Metric.ball_mem_nhds _ hpos
  have hφ : Tendsto (fun z : (Fin 6 → ℝ) × ℝ => (z.2, z.1))
      (𝓝 (sStar, t)) (𝓝 (t, sStar)) :=
    continuous_snd.continuousAt.prodMk_nhds continuous_fst.continuousAt
  filter_upwards [hφ.eventually (Filter.eventually_of_mem hb fun _ hp => hp)] with z hz
  have hlt : dist (z.2, z.1) (t, sStar) < r - dist (t, sStar) (t0, sStar) :=
    Metric.mem_ball.mp hz
  have hsum : dist (z.2, z.1) (t0, sStar) < r := by
    have := dist_triangle (z.2, z.1) (t, sStar) (t0, sStar)
    linarith
  exact hball (z.2, z.1) hsum

lemma exists_Icc_propagator_kepler (t0 : ℝ) :
    ∃ δ > (0 : ℝ), ∀ᶠ s in 𝓝 sStar, ∀ t ∈ Set.Icc (t0 - δ) (t0 + δ),
      propagator t0 s t ≠ 0 ∧
        HasDerivAt (propagator t0 s) (propagatorVel t0 s t) t ∧
        HasDerivAt (propagatorVel t0 s)
          (-(1 / ‖propagator t0 s t‖ ^ 3) • propagator t0 s t) t := by
  obtain ⟨r, hr, hball⟩ := eventually_propagator_kepler_ball t0
  let δ : ℝ := r / 2
  have hδ : 0 < δ := half_pos hr
  refine ⟨δ, hδ, ?_⟩
  have hK : IsCompact (Set.Icc (t0 - δ) (t0 + δ)) := isCompact_Icc
  refine hK.eventually_forall_of_forall_eventually (x₀ := sStar) ?_
  intro t ht
  have htball : dist (t, sStar) (t0, sStar) < r := by
    have habs : |t - t0| ≤ δ := abs_le.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have hdist : dist (t, sStar) (t0, sStar) = |t - t0| := by
      simpa [Real.dist_eq] using dist_prod_same_right t t0 sStar
    have hδr : δ = r / 2 := rfl
    have hr2 : r / 2 < r := half_lt_self hr
    rw [hdist]
    linarith [habs, hδr, hr2]
  exact eventually_propagator_kepler_prod t0 t hr hball htball

lemma mem_chiData_target_of_center {t0 t : ℝ} {r : ℝ}
    (hsub : Metric.ball (sStar, 2 * t0 / 5) r ⊆
      (chiData t0).toOpenPartialHomeomorph.source)
    (hctr : dist (sStar, 2 * t / 5) (sStar, 2 * t0 / 5) < r) :
    (t, sStar) ∈ (chiData t0).toOpenPartialHomeomorph.target := by
  have hsrc : (sStar, 2 * t / 5) ∈ (chiData t0).toOpenPartialHomeomorph.source :=
    hsub hctr
  have hmap := (chiData t0).toOpenPartialHomeomorph.map_source hsrc
  have hleft : (chiData t0).toOpenPartialHomeomorph (sStar, 2 * t / 5)
      = (t, sStar) := by
    rw [ImplicitFunctionData.toOpenPartialHomeomorph_coe,
      ImplicitFunctionData.prodFun_apply]
    simp [chiData_leftFun, chiData_rightFun, Function.uncurry, univF_sStar]
  rwa [hleft] at hmap

lemma eventually_chiProd_eq_two_fifths_prod (t0 t : ℝ)
    (ht : (t, sStar) ∈ (chiData t0).toOpenPartialHomeomorph.target) :
    ∀ᶠ z : (Fin 6 → ℝ) × ℝ in 𝓝 (sStar, t),
      univF z.1 (chiProd t0 z.2 z.1) = z.2 ∧
        (z.2, z.1) ∈ (chiData t0).toOpenPartialHomeomorph.target := by
  have htarget : (chiData t0).toOpenPartialHomeomorph.target ∈ 𝓝 (t, sStar) :=
    (chiData_open_target t0).mem_nhds ht
  have hφ : Tendsto (fun z : (Fin 6 → ℝ) × ℝ => (z.2, z.1))
      (𝓝 (sStar, t)) (𝓝 (t, sStar)) :=
    continuous_snd.continuousAt.prodMk_nhds continuous_fst.continuousAt
  filter_upwards [hφ.eventually (Filter.eventually_of_mem htarget fun _ h => h)]
    with z hz
  exact ⟨(chiData_right_inv t0 z.2 z.1 hz).1, hz⟩

noncomputable def keplerICVel (s : Fin 6 → ℝ) (t : ℝ) : Vec :=
  fDot s (chiOf s t) • statePos s + gDot s (chiOf s t) • stateVel s

def univFsub (p : (Fin 6 → ℝ) × ℝ) (χ : ℝ) : ℝ := univF p.1 χ - p.2

lemma univFsub_center (t : ℝ) : univFsub (sStar, t) (2 * t / 5) = 0 := by
  simp [univFsub, univF_sStar]

lemma tendsto_univFsub_stχ (t : ℝ) :
    Tendsto (fun v : ((Fin 6 → ℝ) × ℝ) × ℝ => (v.1.1, v.2))
      (𝓝 ((sStar, t), 2 * t / 5)) (𝓝 (sStar, 2 * t / 5)) :=
  (continuous_fst.continuousAt (x := ((sStar, t), 2 * t / 5))).fst.prodMk_nhds
    continuous_snd.continuousAt

lemma eventually_hasFDerivAt_univFsub_chi (t : ℝ) :
    ∀ᶠ v : ((Fin 6 → ℝ) × ℝ) × ℝ in 𝓝 ((sStar, t), 2 * t / 5),
      HasFDerivAt (fun χ => univFsub v.1 χ) (univF_f2 v.1.1 v.2) v.2 := by
  filter_upwards [tendsto_univFsub_stχ t |>.eventually
    (eventually_hasFDerivAt_univF_chi (2 * t / 5))] with v hv
  simpa [univFsub] using hv.sub_const v.1.2

lemma eventually_hasFDerivAt_univFsub_st (t : ℝ) :
    ∀ᶠ v : ((Fin 6 → ℝ) × ℝ) × ℝ in 𝓝 ((sStar, t), 2 * t / 5),
      HasFDerivAt (fun p : (Fin 6 → ℝ) × ℝ => univFsub p v.2)
        ((univF_f1 v.1.1 v.2).comp (ContinuousLinearMap.fst ℝ (Fin 6 → ℝ) ℝ) -
          ContinuousLinearMap.snd ℝ (Fin 6 → ℝ) ℝ) v.1 := by
  have hcd : ContDiffAt ℝ 2 (Function.uncurry univF) (sStar, 2 * t / 5) :=
    (contDiffAt_uncurry_univF (2 * t / 5)).of_le (by exact le_top)
  have hopen : ∀ᶠ w : (Fin 6 → ℝ) × ℝ in 𝓝 (sStar, 2 * t / 5),
      ContDiffAt ℝ 2 (Function.uncurry univF) w :=
    hcd.eventually (by decide)
  filter_upwards [tendsto_univFsub_stχ t |>.eventually hopen] with v hvopen
  have hunc : HasFDerivAt (Function.uncurry univF)
      (fderiv ℝ (Function.uncurry univF) (v.1.1, v.2)) (v.1.1, v.2) :=
    (hvopen.differentiableAt (by decide)).hasFDerivAt
  have hpair : HasFDerivAt (fun p : (Fin 6 → ℝ) × ℝ => (p.1, v.2))
      ((ContinuousLinearMap.fst ℝ (Fin 6 → ℝ) ℝ).prod 0) v.1 :=
    hasFDerivAt_fst.prodMk (hasFDerivAt_const _ _)
  have hF : HasFDerivAt (fun p : (Fin 6 → ℝ) × ℝ => univF p.1 v.2)
      ((univF_f1 v.1.1 v.2).comp (ContinuousLinearMap.fst ℝ (Fin 6 → ℝ) ℝ)) v.1 := by
    have hcomp := hunc.comp v.1 hpair
    refine hcomp.congr_fderiv ?_
    apply ContinuousLinearMap.ext
    intro dp
    simp [univF_f1, ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
      ContinuousLinearMap.inl]
  have ht : HasFDerivAt (fun p : (Fin 6 → ℝ) × ℝ => p.2)
      (ContinuousLinearMap.snd ℝ (Fin 6 → ℝ) ℝ) v.1 := hasFDerivAt_snd
  have hsub := hF.sub ht
  have hfun :
      (fun p : (Fin 6 → ℝ) × ℝ => univFsub p v.2) =
        (fun p => univF p.1 v.2) - fun p => p.2 := by
    funext p; rfl
  exact hfun ▸ hsub

lemma continuousAt_univFsub_f1 (t : ℝ) :
    ContinuousAt (Function.uncurry fun p χ =>
      (univF_f1 p.1 χ).comp (ContinuousLinearMap.fst ℝ (Fin 6 → ℝ) ℝ) -
        ContinuousLinearMap.snd ℝ (Fin 6 → ℝ) ℝ)
      ((sStar, t), 2 * t / 5) := by
  have hf1 := continuousAt_univF_f1 (2 * t / 5)
  have hπ : ContinuousAt (fun v : ((Fin 6 → ℝ) × ℝ) × ℝ => (v.1.1, v.2))
      ((sStar, t), 2 * t / 5) :=
    (continuous_fst.continuousAt (x := ((sStar, t), 2 * t / 5))).fst.prodMk
      continuous_snd.continuousAt
  have hcomp : ContinuousAt
      ((Function.uncurry univF_f1) ∘
        fun q : ((Fin 6 → ℝ) × ℝ) × ℝ => (q.1.1, q.2))
      ((sStar, t), 2 * t / 5) :=
    ContinuousAt.comp (f := fun q : ((Fin 6 → ℝ) × ℝ) × ℝ => (q.1.1, q.2)) hf1 hπ
  have hL : Continuous
      (fun L : (Fin 6 → ℝ) →L[ℝ] ℝ =>
        L.comp (ContinuousLinearMap.fst ℝ (Fin 6 → ℝ) ℝ) -
          ContinuousLinearMap.snd ℝ (Fin 6 → ℝ) ℝ) :=
    (continuous_id.clm_comp continuous_const).sub continuous_const
  exact hL.continuousAt.comp hcomp

lemma continuousAt_univFsub_f2 (t : ℝ) :
    ContinuousAt (fun q : ((Fin 6 → ℝ) × ℝ) × ℝ => univF_f2 q.1.1 q.2)
      ((sStar, t), 2 * t / 5) := by
  have hf2 := continuousAt_univF_f2 (2 * t / 5)
  have hπ : ContinuousAt (fun v : ((Fin 6 → ℝ) × ℝ) × ℝ => (v.1.1, v.2))
      ((sStar, t), 2 * t / 5) :=
    (continuous_fst.continuousAt (x := ((sStar, t), 2 * t / 5))).fst.prodMk
      continuous_snd.continuousAt
  have : ContinuousAt
      ((Function.uncurry univF_f2) ∘
        fun q : ((Fin 6 → ℝ) × ℝ) × ℝ => (q.1.1, q.2))
      ((sStar, t), 2 * t / 5) :=
    ContinuousAt.comp (f := fun q : ((Fin 6 → ℝ) × ℝ) × ℝ => (q.1.1, q.2)) hf2 hπ
  simpa [Function.comp_def, Function.uncurry] using this

lemma univFsub_f2_invertible (t : ℝ) :
    (univF_f2 sStar (2 * t / 5)).IsInvertible :=
  univF_f2_invertible t

noncomputable def chiOfParam (t : ℝ) : (Fin 6 → ℝ) × ℝ → ℝ :=
  implicitFunctionOfBivariate
    (f := univFsub)
    (f₁ := fun p χ =>
      (univF_f1 p.1 χ).comp (ContinuousLinearMap.fst ℝ (Fin 6 → ℝ) ℝ) -
        ContinuousLinearMap.snd ℝ (Fin 6 → ℝ) ℝ)
    (f₂ := fun p χ => univF_f2 p.1 χ)
    (eventually_hasFDerivAt_univFsub_st t)
    (eventually_hasFDerivAt_univFsub_chi t)
    (continuousAt_univFsub_f1 t)
    (continuousAt_univFsub_f2 t)
    (univFsub_f2_invertible t)

lemma eventually_univF_chiOfParam (t : ℝ) :
    ∀ᶠ z : (Fin 6 → ℝ) × ℝ in 𝓝 (sStar, t),
      univF z.1 (chiOfParam t z) = z.2 := by
  have happly := eventually_apply_implicitFunctionOfBivariate
    (f := univFsub)
    (f₁ := fun p χ =>
      (univF_f1 p.1 χ).comp (ContinuousLinearMap.fst ℝ (Fin 6 → ℝ) ℝ) -
        ContinuousLinearMap.snd ℝ (Fin 6 → ℝ) ℝ)
    (f₂ := fun p χ => univF_f2 p.1 χ)
    (eventually_hasFDerivAt_univFsub_st t)
    (eventually_hasFDerivAt_univFsub_chi t)
    (continuousAt_univFsub_f1 t)
    (continuousAt_univFsub_f2 t)
    (univFsub_f2_invertible t)
  filter_upwards [happly] with z hz
  have : univFsub z (chiOfParam t z) = univFsub (sStar, t) (2 * t / 5) := by
    simpa [chiOfParam] using hz
  have h0 : univFsub z (chiOfParam t z) = 0 := this.trans (univFsub_center t)
  exact sub_eq_zero.mp h0

lemma tendsto_chiOfParam (t : ℝ) :
    Tendsto (chiOfParam t) (𝓝 (sStar, t)) (𝓝 (2 * t / 5)) := by
  have h := tendsto_implicitFunctionOfBivariate
    (f := univFsub)
    (f₁ := fun p χ =>
      (univF_f1 p.1 χ).comp (ContinuousLinearMap.fst ℝ (Fin 6 → ℝ) ℝ) -
        ContinuousLinearMap.snd ℝ (Fin 6 → ℝ) ℝ)
    (f₂ := fun p χ => univF_f2 p.1 χ)
    (eventually_hasFDerivAt_univFsub_st t)
    (eventually_hasFDerivAt_univFsub_chi t)
    (continuousAt_univFsub_f1 t)
    (continuousAt_univFsub_f2 t)
    (univFsub_f2_invertible t)
  simpa [chiOfParam] using h

lemma tendsto_pair_chiOfParam (t : ℝ) :
    Tendsto (fun z : (Fin 6 → ℝ) × ℝ => (z.1, chiOfParam t z))
      (𝓝 (sStar, t)) (𝓝 (sStar, 2 * t / 5)) :=
  continuous_fst.continuousAt.prodMk_nhds (tendsto_chiOfParam t)

lemma eventually_chiOfParam_mem_source (t0 : ℝ) :
    ∀ᶠ z : (Fin 6 → ℝ) × ℝ in 𝓝 (sStar, t0),
      (z.1, chiOfParam t0 z) ∈ (chiData t0).toOpenPartialHomeomorph.source := by
  have hsrc : (chiData t0).toOpenPartialHomeomorph.source ∈ 𝓝 (sStar, 2 * t0 / 5) :=
    (chiData_open_source t0).mem_nhds (chiData_mem_source t0)
  exact (tendsto_pair_chiOfParam t0).eventually
    (Filter.eventually_of_mem hsrc fun _ h => h)

lemma eventually_chiOfParam_eq_chiProd (t0 : ℝ) :
    ∀ᶠ z : (Fin 6 → ℝ) × ℝ in 𝓝 (sStar, t0),
      chiOfParam t0 z = chiProd t0 z.2 z.1 := by
  filter_upwards [eventually_univF_chiOfParam t0,
    eventually_chiOfParam_mem_source t0] with z hF hsrc
  exact (chiProd_unique_of_mem_source hsrc).symm.trans (by rw [hF])

lemma eventually_chiOf_eq_chiOfParam_slice (t : ℝ) :
    ∀ᶠ s in 𝓝 sStar, chiOf s t = chiOfParam t (s, t) := by
  have hiff := eventually_apply_eq_iff_implicitFunctionOfBivariate
    (eventually_hasFDerivAt_univF_s (2 * t / 5))
    (eventually_hasFDerivAt_univF_chi (2 * t / 5))
    (continuousAt_univF_f1 (2 * t / 5))
    (continuousAt_univF_f2 (2 * t / 5))
    (univF_f2_invertible t)
  have hpath : Tendsto (fun s : Fin 6 → ℝ => (s, t)) (𝓝 sStar) (𝓝 (sStar, t)) :=
    tendsto_id.prodMk_nhds tendsto_const_nhds
  have hχ : Tendsto (fun s : Fin 6 → ℝ => (s, chiOfParam t (s, t))) (𝓝 sStar)
      (𝓝 (sStar, 2 * t / 5)) :=
    (tendsto_pair_chiOfParam t).comp hpath
  have hiff' : ∀ᶠ s in 𝓝 sStar,
      univF s (chiOfParam t (s, t)) = t ↔ chiOf s t = chiOfParam t (s, t) := by
    have : ∀ᶠ v : (Fin 6 → ℝ) × ℝ in 𝓝 (sStar, 2 * t / 5),
        univF v.1 v.2 = t ↔ chiOf v.1 t = v.2 := by
      refine hiff.mono ?_
      intro v hv
      simpa [univF_sStar, chiOf] using hv
    exact hχ.eventually this
  filter_upwards [hiff', hpath.eventually (eventually_univF_chiOfParam t)] with s hiffs hF
  exact hiffs.mp hF

lemma eventually_iff_chiOfParam (t : ℝ) :
    ∀ᶠ q : ((Fin 6 → ℝ) × ℝ) × ℝ in 𝓝 ((sStar, t), 2 * t / 5),
      univF q.1.1 q.2 = q.1.2 ↔ chiOfParam t q.1 = q.2 := by
  have h := eventually_apply_eq_iff_implicitFunctionOfBivariate
    (f := univFsub)
    (f₁ := fun p χ =>
      (univF_f1 p.1 χ).comp (ContinuousLinearMap.fst ℝ (Fin 6 → ℝ) ℝ) -
        ContinuousLinearMap.snd ℝ (Fin 6 → ℝ) ℝ)
    (f₂ := fun p χ => univF_f2 p.1 χ)
    (eventually_hasFDerivAt_univFsub_st t)
    (eventually_hasFDerivAt_univFsub_chi t)
    (continuousAt_univFsub_f1 t)
    (continuousAt_univFsub_f2 t)
    (univFsub_f2_invertible t)
  refine h.mono ?_
  intro q hq
  have hq' :
      univFsub q.1 q.2 = univFsub (sStar, t) (2 * t / 5) ↔
        chiOfParam t q.1 = q.2 := by
    simpa [chiOfParam] using hq
  have h0 : univF sStar (2 * t / 5) - t = 0 := univFsub_center t
  simpa [univFsub, h0, sub_eq_zero] using hq'

/-- Joint `univF s (chiOf s t) = t` by IFT left-inverse of `chiOfParam`,
composed with the continuous pairing `(s, t)` along `chiOfParam`
(which agrees with `chiOf` on the diagonal slice). The remaining
product identification `chiOf = chiProd` uses uniqueness on source. -/
lemma eventually_univF_chiOfParam_prod (t : ℝ) :
    ∀ᶠ z : (Fin 6 → ℝ) × ℝ in 𝓝 (sStar, t),
      univF z.1 (chiOfParam t z) = z.2 :=
  eventually_univF_chiOfParam t

lemma eventually_chiOfParam_eq_chiProd_prod (t0 t : ℝ) {r : ℝ}
    (hr : 0 < r)
    (hball : ∀ p : ℝ × (Fin 6 → ℝ), dist p (t0, sStar) < r →
      chiOfParam t0 (p.2, p.1) = chiProd t0 p.1 p.2)
    (ht : dist (t, sStar) (t0, sStar) < r) :
    ∀ᶠ z : (Fin 6 → ℝ) × ℝ in 𝓝 (sStar, t),
      chiOfParam t0 z = chiProd t0 z.2 z.1 := by
  have hpos : 0 < r - dist (t, sStar) (t0, sStar) := sub_pos.mpr ht
  have hb : Metric.ball (t, sStar) (r - dist (t, sStar) (t0, sStar)) ∈ 𝓝 (t, sStar) :=
    Metric.ball_mem_nhds _ hpos
  have hφ : Tendsto (fun z : (Fin 6 → ℝ) × ℝ => (z.2, z.1))
      (𝓝 (sStar, t)) (𝓝 (t, sStar)) :=
    continuous_snd.continuousAt.prodMk_nhds continuous_fst.continuousAt
  filter_upwards [hφ.eventually (Filter.eventually_of_mem hb fun _ hp => hp)] with z hz
  have hlt : dist (z.2, z.1) (t, sStar) < r - dist (t, sStar) (t0, sStar) :=
    Metric.mem_ball.mp hz
  have hsum : dist (z.2, z.1) (t0, sStar) < r := by
    have := dist_triangle (z.2, z.1) (t, sStar) (t0, sStar)
    linarith
  simpa using hball (z.2, z.1) hsum

lemma eventually_chiOfParam_eq_chiProd_ball (t0 : ℝ) :
    ∃ r > (0 : ℝ), ∀ p : ℝ × (Fin 6 → ℝ),
      dist p (t0, sStar) < r →
        chiOfParam t0 (p.2, p.1) = chiProd t0 p.1 p.2 := by
  have h := eventually_chiOfParam_eq_chiProd t0
  have hφ : Tendsto (fun p : ℝ × (Fin 6 → ℝ) => (p.2, p.1))
      (𝓝 (t0, sStar)) (𝓝 (sStar, t0)) :=
    continuous_snd.continuousAt.prodMk_nhds continuous_fst.continuousAt
  have h' : ∀ᶠ p : ℝ × (Fin 6 → ℝ) in 𝓝 (t0, sStar),
      chiOfParam t0 (p.2, p.1) = chiProd t0 p.1 p.2 :=
    hφ.eventually h
  rcases Metric.mem_nhds_iff.mp h' with ⟨r, hr, hsub⟩
  refine ⟨r, hr, ?_⟩
  intro p hp
  exact hsub hp

lemma exists_Icc_chiOfParam_eq_chiProd (t0 : ℝ) :
    ∃ δ > (0 : ℝ), ∀ᶠ s in 𝓝 sStar, ∀ t ∈ Set.Icc (t0 - δ) (t0 + δ),
      chiOfParam t0 (s, t) = chiProd t0 t s := by
  obtain ⟨r, hr, hball⟩ := eventually_chiOfParam_eq_chiProd_ball t0
  let δ : ℝ := r / 2
  have hδ : 0 < δ := half_pos hr
  refine ⟨δ, hδ, ?_⟩
  have hK : IsCompact (Set.Icc (t0 - δ) (t0 + δ)) := isCompact_Icc
  refine hK.eventually_forall_of_forall_eventually (x₀ := sStar) ?_
  intro t ht
  have htball : dist (t, sStar) (t0, sStar) < r := by
    have habs : |t - t0| ≤ δ := abs_le.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have hdist : dist (t, sStar) (t0, sStar) = |t - t0| := by
      simpa [Real.dist_eq] using dist_prod_same_right t t0 sStar
    have hr2 : r / 2 < r := half_lt_self hr
    have hδr : δ = r / 2 := rfl
    rw [hdist]
    linarith [habs, hδr, hr2]
  exact eventually_chiOfParam_eq_chiProd_prod t0 t hr hball htball

/-! `keplerFlow`: local IFT propagator glued across finitely many `t0` charts. -/

lemma eventually_propagator_norm_eq (t0 : ℝ) :
    ∀ᶠ p : ℝ × (Fin 6 → ℝ) in 𝓝 (t0, sStar),
      ‖propagator t0 p.2 p.1‖ = univF_dchi p.2 (chiProd t0 p.1 p.2) := by
  filter_upwards [eventually_hasDerivAt_chiProd t0, eventually_univF_chiProd t0]
    with p hp ht
  simpa [propagator] using kepler_fg_norm (s := p.2) (t := p.1)
    (χ := chiProd t0 p.1 p.2) hp.1 ht hp.2.1

lemma tendsto_propagator_norm (t0 : ℝ) :
    Tendsto (fun p : ℝ × (Fin 6 → ℝ) => ‖propagator t0 p.2 p.1‖)
      (𝓝 (t0, sStar)) (𝓝 (5 / 2 : ℝ)) := by
  have hρ : Tendsto (fun p : ℝ × (Fin 6 → ℝ) =>
      univF_dchi p.2 (chiProd t0 p.1 p.2)) (𝓝 (t0, sStar)) (𝓝 (5 / 2)) := by
    have hpair : Tendsto (fun p : ℝ × (Fin 6 → ℝ) => (p.2, chiProd t0 p.1 p.2))
        (𝓝 (t0, sStar)) (𝓝 (sStar, 2 * t0 / 5)) :=
      continuous_snd.continuousAt.prodMk_nhds
        (by simpa [chiProd_center t0] using (continuousAt_chiProd t0).tendsto)
    simpa [Function.comp_def, univF_dchi_sStar] using
      (continuousAt_univF_dchi (2 * t0 / 5)).tendsto.comp hpair
  have heq :
      (fun p : ℝ × (Fin 6 → ℝ) => univF_dchi p.2 (chiProd t0 p.1 p.2)) =ᶠ[𝓝 (t0, sStar)]
        fun p => ‖propagator t0 p.2 p.1‖ :=
    (eventually_propagator_norm_eq t0).mono fun _ h => h.symm
  exact Tendsto.congr' heq hρ

lemma eventually_propagator_inShell_ball (t0 : ℝ) :
    ∃ r > (0 : ℝ), ∀ p : ℝ × (Fin 6 → ℝ),
      dist p (t0, sStar) < r → ‖propagator t0 p.2 p.1‖ ∈ Set.Icc (2 : ℝ) 3 := by
  have h : ∀ᶠ p : ℝ × (Fin 6 → ℝ) in 𝓝 (t0, sStar),
      ‖propagator t0 p.2 p.1‖ ∈ Set.Ioo (9 / 4 : ℝ) (11 / 4) :=
    (tendsto_propagator_norm t0).eventually
      (isOpen_Ioo.mem_nhds (by constructor <;> norm_num))
  rcases Metric.mem_nhds_iff.mp h with ⟨r, hr, hsub⟩
  refine ⟨r, hr, ?_⟩
  intro p hp
  have hioo : ‖propagator t0 p.2 p.1‖ ∈ Set.Ioo (9 / 4 : ℝ) (11 / 4) := hsub hp
  exact ⟨by linarith [hioo.1], by linarith [hioo.2]⟩

lemma eventually_propagator_inShell_prod (t0 t : ℝ) {r : ℝ}
    (hr : 0 < r)
    (hball : ∀ p : ℝ × (Fin 6 → ℝ), dist p (t0, sStar) < r →
      ‖propagator t0 p.2 p.1‖ ∈ Set.Icc (2 : ℝ) 3)
    (ht : dist (t, sStar) (t0, sStar) < r) :
    ∀ᶠ z : (Fin 6 → ℝ) × ℝ in 𝓝 (sStar, t),
      ‖propagator t0 z.1 z.2‖ ∈ Set.Icc (2 : ℝ) 3 := by
  have hpos : 0 < r - dist (t, sStar) (t0, sStar) := sub_pos.mpr ht
  have hb : Metric.ball (t, sStar) (r - dist (t, sStar) (t0, sStar)) ∈ 𝓝 (t, sStar) :=
    Metric.ball_mem_nhds _ hpos
  have hφ : Tendsto (fun z : (Fin 6 → ℝ) × ℝ => (z.2, z.1))
      (𝓝 (sStar, t)) (𝓝 (t, sStar)) :=
    continuous_snd.continuousAt.prodMk_nhds continuous_fst.continuousAt
  filter_upwards [hφ.eventually (Filter.eventually_of_mem hb fun _ hp => hp)] with z hz
  have hlt : dist (z.2, z.1) (t, sStar) < r - dist (t, sStar) (t0, sStar) :=
    Metric.mem_ball.mp hz
  have hsum : dist (z.2, z.1) (t0, sStar) < r := by
    have := dist_triangle (z.2, z.1) (t, sStar) (t0, sStar)
    linarith
  exact hball (z.2, z.1) hsum

lemma exists_Icc_propagator_inShell (t0 : ℝ) :
    ∃ δ > (0 : ℝ), ∀ᶠ s in 𝓝 sStar, ∀ t ∈ Set.Icc (t0 - δ) (t0 + δ),
      ‖propagator t0 s t‖ ∈ Set.Icc (2 : ℝ) 3 := by
  obtain ⟨r, hr, hball⟩ := eventually_propagator_inShell_ball t0
  let δ : ℝ := r / 2
  have hδ : 0 < δ := half_pos hr
  refine ⟨δ, hδ, ?_⟩
  have hK : IsCompact (Set.Icc (t0 - δ) (t0 + δ)) := isCompact_Icc
  refine hK.eventually_forall_of_forall_eventually (x₀ := sStar) ?_
  intro t ht
  have htball : dist (t, sStar) (t0, sStar) < r := by
    have habs : |t - t0| ≤ δ := abs_le.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have hdist : dist (t, sStar) (t0, sStar) = |t - t0| := by
      simpa [Real.dist_eq] using dist_prod_same_right t t0 sStar
    have hδr : δ = r / 2 := rfl
    have hr2 : r / 2 < r := half_lt_self hr
    rw [hdist]
    linarith [habs, hδr, hr2]
  exact eventually_propagator_inShell_prod t0 t hr hball htball

lemma exists_Icc_mem_chiData_target (t0 : ℝ) :
    ∃ δ > (0 : ℝ), ∀ t ∈ Set.Icc (t0 - δ) (t0 + δ),
      (t, sStar) ∈ (chiData t0).toOpenPartialHomeomorph.target := by
  have hT : (chiData t0).toOpenPartialHomeomorph.target ∈ 𝓝 (t0, sStar) :=
    (chiData_open_target t0).mem_nhds (chiData_target_mem t0)
  rcases Metric.mem_nhds_iff.mp hT with ⟨r, hr, hsub⟩
  refine ⟨r / 2, half_pos hr, ?_⟩
  intro t ht
  have habs : |t - t0| ≤ r / 2 := abs_le.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hdist : dist (t, sStar) (t0, sStar) = |t - t0| := by
    simpa [Real.dist_eq] using dist_prod_same_right t t0 sStar
  have : dist (t, sStar) (t0, sStar) < r := by
    rw [hdist]; linarith [habs, half_lt_self hr]
  exact hsub this

noncomputable def keplerChartRadius (t0 : ℝ) : ℝ :=
  min (Classical.choose (exists_Icc_propagator_kepler t0))
    (min (Classical.choose (exists_Icc_propagator_inShell t0))
      (Classical.choose (exists_Icc_mem_chiData_target t0)))

lemma keplerChartRadius_pos (t0 : ℝ) : 0 < keplerChartRadius t0 :=
  lt_min (Classical.choose_spec (exists_Icc_propagator_kepler t0)).1
    (lt_min (Classical.choose_spec (exists_Icc_propagator_inShell t0)).1
      (Classical.choose_spec (exists_Icc_mem_chiData_target t0)).1)

lemma eventually_keplerChart (t0 : ℝ) :
    ∀ᶠ s in 𝓝 sStar, ∀ t ∈ Set.Icc (t0 - keplerChartRadius t0)
      (t0 + keplerChartRadius t0),
      propagator t0 s t ≠ 0 ∧
        HasDerivAt (propagator t0 s) (propagatorVel t0 s t) t ∧
        HasDerivAt (propagatorVel t0 s)
          (-(1 / ‖propagator t0 s t‖ ^ 3) • propagator t0 s t) t ∧
        ‖propagator t0 s t‖ ∈ Set.Icc (2 : ℝ) 3 := by
  have hk := (Classical.choose_spec (exists_Icc_propagator_kepler t0)).2
  have hs := (Classical.choose_spec (exists_Icc_propagator_inShell t0)).2
  filter_upwards [hk, hs] with s hK hS t ht
  have htK : t ∈ Set.Icc (t0 - Classical.choose (exists_Icc_propagator_kepler t0))
      (t0 + Classical.choose (exists_Icc_propagator_kepler t0)) := by
    have : keplerChartRadius t0 ≤ Classical.choose (exists_Icc_propagator_kepler t0) :=
      min_le_left _ _
    refine ⟨?_, ?_⟩
    · linarith [ht.1, this]
    · linarith [ht.2, this]
  have htS : t ∈ Set.Icc (t0 - Classical.choose (exists_Icc_propagator_inShell t0))
      (t0 + Classical.choose (exists_Icc_propagator_inShell t0)) := by
    have : keplerChartRadius t0 ≤ Classical.choose (exists_Icc_propagator_inShell t0) :=
      (min_le_right _ _).trans (min_le_left _ _)
    refine ⟨?_, ?_⟩
    · linarith [ht.1, this]
    · linarith [ht.2, this]
  exact ⟨(hK t htK).1, (hK t htK).2.1, (hK t htK).2.2, hS t htS⟩

lemma continuousAt_chiProd_of_mem_target {t0 t : ℝ} {s : Fin 6 → ℝ}
    (h : (t, s) ∈ (chiData t0).toOpenPartialHomeomorph.target) :
    ContinuousAt (fun p : ℝ × (Fin 6 → ℝ) => chiProd t0 p.1 p.2) (t, s) :=
  continuousAt_snd.comp
    ((chiData t0).toOpenPartialHomeomorph.continuousAt_symm h)

lemma eventually_chiProd_agree_slice (t0 t1 t : ℝ)
    (ht0 : (t, sStar) ∈ (chiData t0).toOpenPartialHomeomorph.target)
    (ht1 : (t, sStar) ∈ (chiData t1).toOpenPartialHomeomorph.target) :
    ∀ᶠ s in 𝓝 sStar, chiProd t0 t s = chiProd t1 t s := by
  have hF1 : ∀ᶠ s in 𝓝 sStar, univF s (chiProd t1 t s) = t := by
    have hpath : Tendsto (fun s : Fin 6 → ℝ => (t, s)) (𝓝 sStar) (𝓝 (t, sStar)) :=
      tendsto_const_nhds.prodMk_nhds tendsto_id
    have hT : (chiData t1).toOpenPartialHomeomorph.target ∈ 𝓝 (t, sStar) :=
      (chiData_open_target t1).mem_nhds ht1
    exact hpath.eventually (Filter.eventually_of_mem hT fun p hp =>
      (chiData_right_inv t1 p.1 p.2 hp).1)
  have hsrc : (sStar, 2 * t / 5) ∈ (chiData t0).toOpenPartialHomeomorph.source := by
    have := chiProd_mem_source ht0
    rwa [chiProd_sStar_of_mem_target ht0] at this
  have hsrcN : (chiData t0).toOpenPartialHomeomorph.source ∈
      𝓝 (sStar, 2 * t / 5) :=
    (chiData_open_source t0).mem_nhds hsrc
  have hχ : Tendsto (fun s : Fin 6 → ℝ => (s, chiProd t1 t s)) (𝓝 sStar)
      (𝓝 (sStar, 2 * t / 5)) := by
    have hval : Tendsto (fun s : Fin 6 → ℝ => chiProd t1 t s) (𝓝 sStar)
        (𝓝 (2 * t / 5)) := by
      have hc := continuousAt_chiProd_of_mem_target ht1
      have hp : Tendsto (fun s : Fin 6 → ℝ => (t, s)) (𝓝 sStar) (𝓝 (t, sStar)) :=
        tendsto_const_nhds.prodMk_nhds tendsto_id
      simpa [Function.comp_def, chiProd_sStar_of_mem_target ht1] using
        hc.tendsto.comp hp
    exact tendsto_id.prodMk_nhds hval
  filter_upwards [hF1, hχ.eventually (Filter.eventually_of_mem hsrcN fun _ h => h)]
    with s hF hsrcs
  have huniq := chiProd_unique_of_mem_source hsrcs
  rw [hF] at huniq
  exact huniq

lemma eventually_chiProd_agree_prod (t0 t1 t : ℝ)
    (ht0 : (t, sStar) ∈ (chiData t0).toOpenPartialHomeomorph.target)
    (ht1 : (t, sStar) ∈ (chiData t1).toOpenPartialHomeomorph.target) :
    ∀ᶠ z : (Fin 6 → ℝ) × ℝ in 𝓝 (sStar, t),
      chiProd t0 z.2 z.1 = chiProd t1 z.2 z.1 := by
  have hφ : Tendsto (fun z : (Fin 6 → ℝ) × ℝ => (z.2, z.1))
      (𝓝 (sStar, t)) (𝓝 (t, sStar)) :=
    continuous_snd.continuousAt.prodMk_nhds continuous_fst.continuousAt
  have hT1 : (chiData t1).toOpenPartialHomeomorph.target ∈ 𝓝 (t, sStar) :=
    (chiData_open_target t1).mem_nhds ht1
  have hsrc : (sStar, 2 * t / 5) ∈ (chiData t0).toOpenPartialHomeomorph.source := by
    have := chiProd_mem_source ht0
    rwa [chiProd_sStar_of_mem_target ht0] at this
  have hsrcN : (chiData t0).toOpenPartialHomeomorph.source ∈ 𝓝 (sStar, 2 * t / 5) :=
    (chiData_open_source t0).mem_nhds hsrc
  have hχ : Tendsto (fun z : (Fin 6 → ℝ) × ℝ => (z.1, chiProd t1 z.2 z.1))
      (𝓝 (sStar, t)) (𝓝 (sStar, 2 * t / 5)) := by
    have hc := continuousAt_chiProd_of_mem_target ht1
    have hval : Tendsto (fun z : (Fin 6 → ℝ) × ℝ => chiProd t1 z.2 z.1)
        (𝓝 (sStar, t)) (𝓝 (2 * t / 5)) := by
      simpa [Function.comp_def, chiProd_sStar_of_mem_target ht1] using
        hc.tendsto.comp hφ
    exact continuous_fst.continuousAt.prodMk_nhds hval
  filter_upwards [hφ.eventually (Filter.eventually_of_mem hT1 fun p hp =>
      (chiData_right_inv t1 p.1 p.2 hp).1),
    hχ.eventually (Filter.eventually_of_mem hsrcN fun _ h => h)] with z hF hsrcz
  have := chiProd_unique_of_mem_source (t0 := t0) hsrcz
  rw [hF] at this
  exact this

lemma exists_Icc_chiProd_agree (t0 t1 : ℝ) :
    ∃ δ > (0 : ℝ), ∀ᶠ s in 𝓝 sStar,
      ∀ t ∈ Set.Icc (t0 - δ) (t0 + δ) ∩ Set.Icc (t1 - δ) (t1 + δ),
        chiProd t0 t s = chiProd t1 t s := by
  obtain ⟨δ0, hδ0, ht0⟩ := exists_Icc_mem_chiData_target t0
  obtain ⟨δ1, hδ1, ht1⟩ := exists_Icc_mem_chiData_target t1
  let δ : ℝ := min δ0 δ1
  have hδ : 0 < δ := lt_min hδ0 hδ1
  refine ⟨δ, hδ, ?_⟩
  have hK : IsCompact
      (Set.Icc (t0 - δ) (t0 + δ) ∩ Set.Icc (t1 - δ) (t1 + δ)) :=
    isCompact_Icc.inter isCompact_Icc
  refine hK.eventually_forall_of_forall_eventually (x₀ := sStar) ?_
  intro t ht
  have h0 : t ∈ Set.Icc (t0 - δ0) (t0 + δ0) := by
    have := min_le_left δ0 δ1
    exact ⟨by linarith [ht.1.1], by linarith [ht.1.2]⟩
  have h1 : t ∈ Set.Icc (t1 - δ1) (t1 + δ1) := by
    have := min_le_right δ0 δ1
    exact ⟨by linarith [ht.2.1], by linarith [ht.2.2]⟩
  exact eventually_chiProd_agree_prod t0 t1 t (ht0 t h0) (ht1 t h1)

lemma exists_finite_chart_cover :
    ∃ F : Finset ℝ,
      Set.Icc (0 : ℝ) 1 ⊆ ⋃ t0 ∈ F,
        Set.Ioo (t0 - keplerChartRadius t0) (t0 + keplerChartRadius t0) := by
  let U : ℝ → Set ℝ := fun t0 =>
    Set.Ioo (t0 - keplerChartRadius t0) (t0 + keplerChartRadius t0)
  have hopen : ∀ t0, IsOpen (U t0) := fun _ => isOpen_Ioo
  have hcov : Set.Icc (0 : ℝ) 1 ⊆ ⋃ t0, U t0 := by
    intro t ht
    refine Set.mem_iUnion.2 ⟨t, ?_⟩
    have hδ := keplerChartRadius_pos t
    exact Set.mem_Ioo.2 ⟨sub_lt_self _ hδ, lt_add_of_pos_right _ hδ⟩
  obtain ⟨F, hF⟩ := isCompact_Icc.elim_finite_subcover U hopen hcov
  exact ⟨F, hF⟩

noncomputable def packCover : Finset ℝ :=
  Classical.choose exists_finite_chart_cover

lemma packCover_covers :
    Set.Icc (0 : ℝ) 1 ⊆ ⋃ t0 ∈ packCover,
      Set.Ioo (t0 - keplerChartRadius t0) (t0 + keplerChartRadius t0) :=
  Classical.choose_spec exists_finite_chart_cover

noncomputable def pickChart (t : ℝ) : ℝ :=
  if h : ∃ t0 ∈ packCover, t ∈ Set.Ioo (t0 - keplerChartRadius t0)
      (t0 + keplerChartRadius t0) then
    Classical.choose h
  else
    0

lemma pickChart_spec {t : ℝ}
    (h : ∃ t0 ∈ packCover, t ∈ Set.Ioo (t0 - keplerChartRadius t0)
      (t0 + keplerChartRadius t0)) :
    pickChart t ∈ packCover ∧
      t ∈ Set.Ioo (pickChart t - keplerChartRadius (pickChart t))
        (pickChart t + keplerChartRadius (pickChart t)) := by
  simp only [pickChart, dif_pos h]
  exact Classical.choose_spec h

lemma pickChart_spec_of_Icc {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    pickChart t ∈ packCover ∧
      t ∈ Set.Ioo (pickChart t - keplerChartRadius (pickChart t))
        (pickChart t + keplerChartRadius (pickChart t)) := by
  have h := packCover_covers ht
  rw [Set.mem_iUnion₂] at h
  rcases h with ⟨t0, ht0, htoo⟩
  exact pickChart_spec ⟨t0, ht0, htoo⟩

noncomputable def keplerFlow (s : Fin 6 → ℝ) (t : ℝ) : Vec :=
  propagator (pickChart t) s t

noncomputable def keplerFlowVel (s : Fin 6 → ℝ) (t : ℝ) : Vec :=
  propagatorVel (pickChart t) s t

lemma eventually_forall_finset {α β : Type*} {l : Filter α} {s : Finset β}
    {p : β → α → Prop} (h : ∀ i ∈ s, ∀ᶠ x in l, p i x) :
    ∀ᶠ x in l, ∀ i ∈ s, p i x := by
  classical
  have := (Filter.eventually_all (ι := s)).2 fun i => h i.1 i.2
  filter_upwards [this] with x hx i hi
  exact hx ⟨i, hi⟩

lemma eventually_packCover_kepler :
    ∀ᶠ s in 𝓝 sStar, ∀ t0 ∈ packCover,
      ∀ t ∈ Set.Icc (t0 - keplerChartRadius t0) (t0 + keplerChartRadius t0),
        propagator t0 s t ≠ 0 ∧
          HasDerivAt (propagator t0 s) (propagatorVel t0 s t) t ∧
          HasDerivAt (propagatorVel t0 s)
            (-(1 / ‖propagator t0 s t‖ ^ 3) • propagator t0 s t) t ∧
          ‖propagator t0 s t‖ ∈ Set.Icc (2 : ℝ) 3 :=
  eventually_forall_finset fun t0 _ => eventually_keplerChart t0

lemma mem_target_of_keplerIcc {t0 t : ℝ}
    (ht : t ∈ Set.Icc (t0 - keplerChartRadius t0) (t0 + keplerChartRadius t0)) :
    (t, sStar) ∈ (chiData t0).toOpenPartialHomeomorph.target := by
  have hδ := (Classical.choose_spec (exists_Icc_mem_chiData_target t0)).2
  have hle : keplerChartRadius t0 ≤
      Classical.choose (exists_Icc_mem_chiData_target t0) :=
    (min_le_right _ _).trans (min_le_right _ _)
  have ht' : t ∈ Set.Icc (t0 - Classical.choose (exists_Icc_mem_chiData_target t0))
      (t0 + Classical.choose (exists_Icc_mem_chiData_target t0)) :=
    ⟨by linarith [ht.1, hle], by linarith [ht.2, hle]⟩
  exact hδ t ht'

lemma eventually_packCover_chiProd_agree :
    ∀ᶠ s in 𝓝 sStar, ∀ t0 ∈ packCover, ∀ t1 ∈ packCover,
      ∀ t ∈ Set.Icc (t0 - keplerChartRadius t0) (t0 + keplerChartRadius t0) ∩
          Set.Icc (t1 - keplerChartRadius t1) (t1 + keplerChartRadius t1),
        chiProd t0 t s = chiProd t1 t s := by
  have h : ∀ t0 ∈ packCover, ∀ t1 ∈ packCover,
      ∀ᶠ s in 𝓝 sStar,
        ∀ t ∈ Set.Icc (t0 - keplerChartRadius t0) (t0 + keplerChartRadius t0) ∩
            Set.Icc (t1 - keplerChartRadius t1) (t1 + keplerChartRadius t1),
          chiProd t0 t s = chiProd t1 t s := by
    intro t0 _ t1 _
    have hK : IsCompact
        (Set.Icc (t0 - keplerChartRadius t0) (t0 + keplerChartRadius t0) ∩
          Set.Icc (t1 - keplerChartRadius t1) (t1 + keplerChartRadius t1)) :=
      isCompact_Icc.inter isCompact_Icc
    refine hK.eventually_forall_of_forall_eventually (x₀ := sStar) ?_
    intro t ht
    exact eventually_chiProd_agree_prod t0 t1 t
      (mem_target_of_keplerIcc ht.1) (mem_target_of_keplerIcc ht.2)
  exact eventually_forall_finset fun t0 ht0 =>
    eventually_forall_finset fun t1 ht1 => h t0 ht0 t1 ht1

lemma Ioo_subset_Icc_chart (t0 : ℝ) :
    Set.Ioo (t0 - keplerChartRadius t0) (t0 + keplerChartRadius t0) ⊆
      Set.Icc (t0 - keplerChartRadius t0) (t0 + keplerChartRadius t0) :=
  Set.Ioo_subset_Icc_self

lemma propagator_eq_of_chiProd {t0 t1 t : ℝ} {s : Fin 6 → ℝ}
    (h : chiProd t0 t s = chiProd t1 t s) :
    propagator t0 s t = propagator t1 s t := by
  simp [propagator, h]

lemma eventually_pack_ball :
    ∀ᶠ s in 𝓝 sStar,
      (∀ t0 ∈ packCover, ∀ t ∈ Set.Icc (t0 - keplerChartRadius t0)
          (t0 + keplerChartRadius t0),
        propagator t0 s t ≠ 0 ∧
          HasDerivAt (propagator t0 s) (propagatorVel t0 s t) t ∧
          HasDerivAt (propagatorVel t0 s)
            (-(1 / ‖propagator t0 s t‖ ^ 3) • propagator t0 s t) t ∧
          ‖propagator t0 s t‖ ∈ Set.Icc (2 : ℝ) 3) ∧
      (∀ t0 ∈ packCover, ∀ t1 ∈ packCover,
        ∀ t ∈ Set.Icc (t0 - keplerChartRadius t0) (t0 + keplerChartRadius t0) ∩
            Set.Icc (t1 - keplerChartRadius t1) (t1 + keplerChartRadius t1),
          chiProd t0 t s = chiProd t1 t s) :=
  eventually_packCover_kepler.and eventually_packCover_chiProd_agree

lemma exists_keplerFlow_ball :
    ∃ r > (0 : ℝ), ∀ s : Fin 6 → ℝ, ‖s - sStar‖ < r →
      (∀ t0 ∈ packCover, ∀ t ∈ Set.Icc (t0 - keplerChartRadius t0)
          (t0 + keplerChartRadius t0),
        propagator t0 s t ≠ 0 ∧
          HasDerivAt (propagator t0 s) (propagatorVel t0 s t) t ∧
          HasDerivAt (propagatorVel t0 s)
            (-(1 / ‖propagator t0 s t‖ ^ 3) • propagator t0 s t) t ∧
          ‖propagator t0 s t‖ ∈ Set.Icc (2 : ℝ) 3) ∧
      (∀ t0 ∈ packCover, ∀ t1 ∈ packCover,
        ∀ t ∈ Set.Icc (t0 - keplerChartRadius t0) (t0 + keplerChartRadius t0) ∩
            Set.Icc (t1 - keplerChartRadius t1) (t1 + keplerChartRadius t1),
          chiProd t0 t s = chiProd t1 t s) := by
  have h := eventually_pack_ball
  rcases Metric.mem_nhds_iff.mp h with ⟨r, hr, hsub⟩
  refine ⟨r, hr, ?_⟩
  intro s hs
  have : dist s sStar < r := by rwa [dist_eq_norm]
  exact hsub this

lemma keplerFlow_eq_propagator_of {s : Fin 6 → ℝ} {t t0 : ℝ}
    (hcov : t0 ∈ packCover)
    (htoo : t ∈ Set.Ioo (t0 - keplerChartRadius t0) (t0 + keplerChartRadius t0))
    (hag : ∀ t1 ∈ packCover,
      ∀ τ ∈ Set.Icc (t0 - keplerChartRadius t0) (t0 + keplerChartRadius t0) ∩
          Set.Icc (t1 - keplerChartRadius t1) (t1 + keplerChartRadius t1),
        chiProd t0 τ s = chiProd t1 τ s) :
    keplerFlow s t = propagator t0 s t := by
  have hex : ∃ t1 ∈ packCover,
      t ∈ Set.Ioo (t1 - keplerChartRadius t1) (t1 + keplerChartRadius t1) :=
    ⟨t0, hcov, htoo⟩
  have hpick := pickChart_spec hex
  have htI : t ∈ Set.Icc (t0 - keplerChartRadius t0) (t0 + keplerChartRadius t0) ∩
      Set.Icc (pickChart t - keplerChartRadius (pickChart t))
        (pickChart t + keplerChartRadius (pickChart t)) :=
    ⟨Set.Ioo_subset_Icc_self htoo, Set.Ioo_subset_Icc_self hpick.2⟩
  have hχ := hag (pickChart t) hpick.1 t htI
  simpa [keplerFlow] using propagator_eq_of_chiProd hχ.symm

lemma eventuallyEq_keplerFlow_propagator {s : Fin 6 → ℝ} {t t0 : ℝ}
    (hcov : t0 ∈ packCover)
    (htoo : t ∈ Set.Ioo (t0 - keplerChartRadius t0) (t0 + keplerChartRadius t0))
    (hag : ∀ t1 ∈ packCover,
      ∀ τ ∈ Set.Icc (t0 - keplerChartRadius t0) (t0 + keplerChartRadius t0) ∩
          Set.Icc (t1 - keplerChartRadius t1) (t1 + keplerChartRadius t1),
        chiProd t0 τ s = chiProd t1 τ s) :
    keplerFlow s =ᶠ[𝓝 t] propagator t0 s := by
  have hN : Set.Ioo (t0 - keplerChartRadius t0) (t0 + keplerChartRadius t0) ∈ 𝓝 t :=
    Ioo_mem_nhds htoo.1 htoo.2
  refine Filter.eventually_of_mem hN ?_
  intro τ hτ
  exact keplerFlow_eq_propagator_of hcov hτ hag

lemma isTarget_keplerFlow_of {s : Fin 6 → ℝ} {r : ℝ}
    (hr : ∀ t0 ∈ packCover, ∀ t ∈ Set.Icc (t0 - keplerChartRadius t0)
        (t0 + keplerChartRadius t0),
      propagator t0 s t ≠ 0 ∧
        HasDerivAt (propagator t0 s) (propagatorVel t0 s t) t ∧
        HasDerivAt (propagatorVel t0 s)
          (-(1 / ‖propagator t0 s t‖ ^ 3) • propagator t0 s t) t ∧
        ‖propagator t0 s t‖ ∈ Set.Icc (2 : ℝ) 3)
    (hag : ∀ t0 ∈ packCover, ∀ t1 ∈ packCover,
      ∀ t ∈ Set.Icc (t0 - keplerChartRadius t0) (t0 + keplerChartRadius t0) ∩
          Set.Icc (t1 - keplerChartRadius t1) (t1 + keplerChartRadius t1),
        chiProd t0 t s = chiProd t1 t s) :
    IsTarget (1 : ℝ) 2 3 1 (keplerFlow s) := by
  refine ⟨?_, ?_⟩
  · refine ⟨keplerFlowVel s, ?_, ?_, ?_⟩
    · intro t ht
      have hpc := pickChart_spec_of_Icc ht
      have hI := Set.Ioo_subset_Icc_self hpc.2
      have hne := (hr (pickChart t) hpc.1 t hI).1
      have heq := keplerFlow_eq_propagator_of hpc.1 hpc.2 (hag (pickChart t) hpc.1)
      simpa [heq]
    · intro t ht
      have hpc := pickChart_spec_of_Icc ht
      have hI := Set.Ioo_subset_Icc_self hpc.2
      have hder := (hr (pickChart t) hpc.1 t hI).2.1
      have hev := eventuallyEq_keplerFlow_propagator hpc.1 hpc.2
        (hag (pickChart t) hpc.1)
      have hval := keplerFlow_eq_propagator_of hpc.1 hpc.2 (hag (pickChart t) hpc.1)
      have : keplerFlowVel s t = propagatorVel (pickChart t) s t := rfl
      exact (hder.congr_of_eventuallyEq hev).congr_deriv (by simp [keplerFlowVel, hval])
    · intro t ht
      have hpc := pickChart_spec_of_Icc ht
      have hI := Set.Ioo_subset_Icc_self hpc.2
      have hder := (hr (pickChart t) hpc.1 t hI).2.2.1
      have hne := (hr (pickChart t) hpc.1 t hI).1
      have heq := keplerFlow_eq_propagator_of hpc.1 hpc.2 (hag (pickChart t) hpc.1)
      have hev : keplerFlowVel s =ᶠ[𝓝 t] propagatorVel (pickChart t) s := by
        have hN : Set.Ioo (pickChart t - keplerChartRadius (pickChart t))
            (pickChart t + keplerChartRadius (pickChart t)) ∈ 𝓝 t :=
          Ioo_mem_nhds hpc.2.1 hpc.2.2
        refine Filter.eventually_of_mem hN ?_
        intro τ hτ
        have hpcτ := pickChart_spec ⟨pickChart t, hpc.1, hτ⟩
        have hχ := hag (pickChart t) hpc.1 (pickChart τ) hpcτ.1 τ
          ⟨Set.Ioo_subset_Icc_self hτ, Set.Ioo_subset_Icc_self hpcτ.2⟩
        simp [keplerFlowVel, propagatorVel, hχ]
      refine (hder.congr_of_eventuallyEq hev).congr_deriv ?_
      simp [heq]
  · intro t ht
    have hpc := pickChart_spec_of_Icc ht
    have hI := Set.Ioo_subset_Icc_self hpc.2
    have hsh := (hr (pickChart t) hpc.1 t hI).2.2.2
    have heq := keplerFlow_eq_propagator_of hpc.1 hpc.2 (hag (pickChart t) hpc.1)
    simpa [heq] using hsh

lemma eventually_keplerFlow_eq_keplerIC_at (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    ∀ᶠ s in 𝓝 sStar, keplerFlow s t = keplerIC s t := by
  have hpc := pickChart_spec_of_Icc ht
  have hI := Set.Ioo_subset_Icc_self hpc.2
  filter_upwards [eventually_keplerIC_eq_propagator_diag t,
    eventually_chiProd_agree_slice (pickChart t) t t
      (mem_target_of_keplerIcc hI) (chiData_target_mem t),
    eventually_pack_ball] with s hdiag hχ hp
  have heq := keplerFlow_eq_propagator_of hpc.1 hpc.2 (hp.2 (pickChart t) hpc.1)
  have hprop : propagator (pickChart t) s t = propagator t s t :=
    propagator_eq_of_chiProd hχ
  exact heq.trans (hprop.trans hdiag.symm)

lemma eventually_sample_keplerIC_eq_flow :
    ∀ᶠ s in 𝓝 sStar,
      keplerFlow s 0 = keplerIC s 0 ∧
      keplerFlow s (1 / 4 : ℝ) = keplerIC s (1 / 4) ∧
      keplerFlow s (1 / 2 : ℝ) = keplerIC s (1 / 2) ∧
      keplerFlow s 1 = keplerIC s 1 := by
  filter_upwards [
    eventually_keplerFlow_eq_keplerIC_at 0 (by constructor <;> norm_num),
    eventually_keplerFlow_eq_keplerIC_at (1 / 4) (by constructor <;> norm_num),
    eventually_keplerFlow_eq_keplerIC_at (1 / 2) (by constructor <;> norm_num),
    eventually_keplerFlow_eq_keplerIC_at 1 (by constructor <;> norm_num)] with s a b c d
  exact ⟨a, b, c, d⟩

lemma secondDiff_eq_of {f g : ℝ → Vec} {h : ℝ}
    (h0 : f 0 = g 0) (hh : f h = g h) (h2 : f (2 * h) = g (2 * h)) :
    secondDiff f h = secondDiff g h := by
  unfold secondDiff
  rw [h0, hh, h2]

lemma sdCart_eq_flow {s : Fin 6 → ℝ}
    (h : keplerFlow s 0 = keplerIC s 0 ∧
      keplerFlow s (1 / 4 : ℝ) = keplerIC s (1 / 4) ∧
      keplerFlow s (1 / 2 : ℝ) = keplerIC s (1 / 2) ∧
      keplerFlow s 1 = keplerIC s 1) :
    sdCart s =
      sdPairCoord
        (secondDiff (fun t => los obs (keplerFlow s) t) hSD1)
        (secondDiff (fun t => los obs (keplerFlow s) t) hSD2) := by
  have L : ∀ t, keplerIC s t = keplerFlow s t →
      los obs (keplerIC s) t = los obs (keplerFlow s) t := by
    intro t ht; unfold los; rw [ht]
  have t14 : hSD1 = (1 / 4 : ℝ) := by unfold hSD1; norm_num
  have t12 : hSD2 = (1 / 2 : ℝ) := by unfold hSD2; norm_num
  have t2s : 2 * hSD1 = (1 / 2 : ℝ) := by unfold hSD1; norm_num
  have t21 : 2 * hSD2 = (1 : ℝ) := by unfold hSD2; norm_num
  have e1 := secondDiff_eq_of
    (L 0 h.1.symm)
    (L hSD1 (t14 ▸ h.2.1.symm))
    (L (2 * hSD1) (t2s ▸ h.2.2.1.symm))
  have e2 := secondDiff_eq_of
    (L 0 h.1.symm)
    (L hSD2 (t12 ▸ h.2.2.1.symm))
    (L (2 * hSD2) (t21 ▸ h.2.2.2.symm))
  exact congrArg₂ sdPairCoord e1 e2

lemma not_both_recovered_flow {ε : ℝ} {ξ : ℝ → Vec} {x y : Fin 6 → ℝ}
    (hxeq : keplerFlow x 0 = keplerIC x 0 ∧
      keplerFlow x (1 / 4 : ℝ) = keplerIC x (1 / 4) ∧
      keplerFlow x (1 / 2 : ℝ) = keplerIC x (1 / 2) ∧
      keplerFlow x 1 = keplerIC x 1)
    (hyeq : keplerFlow y 0 = keplerIC y 0 ∧
      keplerFlow y (1 / 4 : ℝ) = keplerIC y (1 / 4) ∧
      keplerFlow y (1 / 2 : ℝ) = keplerIC y (1 / 2) ∧
      keplerFlow y 1 = keplerIC y 1)
    (hε : 0 ≤ ε) (hsep : 8 * ε < ‖sdCart y - sdCart x‖)
    (hx : RecoveredBy obs ε 1 ξ (keplerFlow x))
    (hy : RecoveredBy obs ε 1 ξ (keplerFlow y)) : False := by
  have hx' := sdCart_eq_flow hxeq
  have hy' := sdCart_eq_flow hyeq
  have hdiff : sdCart y - sdCart x =
      sdPairCoord
        (secondDiff (fun t => los obs (keplerFlow y) t - los obs (keplerFlow x) t) hSD1)
        (secondDiff (fun t => los obs (keplerFlow y) t - los obs (keplerFlow x) t) hSD2) := by
    rw [hx', hy']
    simp [sdPairCoord_sub, secondDiff_sub]
  rw [hdiff] at hsep
  set w1 := secondDiff (fun t => los obs (keplerFlow y) t - los obs (keplerFlow x) t) hSD1
  set w2 := secondDiff (fun t => los obs (keplerFlow y) t - los obs (keplerFlow x) t) hSD2
  have hmax : ∃ i, 8 * ε < |sdPairCoord w1 w2 i| := by
    by_contra hnone
    push_neg at hnone
    have : ‖sdPairCoord w1 w2‖ ≤ 8 * ε :=
      (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => by
        simpa [Real.norm_eq_abs] using hnone i
    exact (hsep.trans_le this).false
  obtain ⟨i, hi⟩ := hmax
  fin_cases i
  · exact not_both_recovered hSD1_window (hi.trans_le (coord_le_euclidean w1 0)) hy hx
  · exact not_both_recovered hSD1_window (hi.trans_le (coord_le_euclidean w1 1)) hy hx
  · exact not_both_recovered hSD1_window (hi.trans_le (coord_le_euclidean w1 2)) hy hx
  · exact not_both_recovered hSD2_window (hi.trans_le (coord_le_euclidean w2 0)) hy hx
  · exact not_both_recovered hSD2_window (hi.trans_le (coord_le_euclidean w2 1)) hy hx
  · exact not_both_recovered hSD2_window (hi.trans_le (coord_le_euclidean w2 2)) hy hx

lemma exists_pack_radius :
    ∃ σ r : ℝ, 0 < σ ∧ 0 < r ∧
      (∀ s : Fin 6 → ℝ, ‖s - sStar‖ < r → IsTarget (1 : ℝ) 2 3 1 (keplerFlow s)) ∧
      (∀ s : Fin 6 → ℝ, ‖s - sStar‖ < r →
        keplerFlow s 0 = keplerIC s 0 ∧
          keplerFlow s (1 / 4 : ℝ) = keplerIC s (1 / 4) ∧
          keplerFlow s (1 / 2 : ℝ) = keplerIC s (1 / 2) ∧
          keplerFlow s 1 = keplerIC s 1) ∧
      (∀ x y : Fin 6 → ℝ, ‖x - sStar‖ < r → ‖y - sStar‖ < r →
        σ * ‖y - x‖ ≤ ‖sdCart y - sdCart x‖) := by
  obtain ⟨σ, r1, hσ, hr1, hlin⟩ := exists_sdCart_linear
  obtain ⟨r2, hr2, hflow⟩ := exists_keplerFlow_ball
  obtain ⟨r3, hr3, hsamp⟩ := Metric.mem_nhds_iff.mp eventually_sample_keplerIC_eq_flow
  let r : ℝ := min r1 (min r2 r3)
  have hr : 0 < r := lt_min hr1 (lt_min hr2 hr3)
  refine ⟨σ, r, hσ, hr, ?_, ?_, ?_⟩
  · intro s hs
    have hs2 : ‖s - sStar‖ < r2 :=
      hs.trans_le ((min_le_right r1 (min r2 r3)).trans (min_le_left r2 r3))
    have hf := hflow s hs2
    exact isTarget_keplerFlow_of (r := r2) hf.1 hf.2
  · intro s hs
    have hs3 : dist s sStar < r3 := by
      have : ‖s - sStar‖ < r3 :=
        hs.trans_le ((min_le_right r1 (min r2 r3)).trans (min_le_right r2 r3))
      rwa [dist_eq_norm]
    exact hsamp (Metric.mem_ball.mpr hs3)
  · intro x y hx hy
    exact hlin x y (hx.trans_le (min_le_left r1 _)) (hy.trans_le (min_le_left r1 _))

lemma exhaustive_ncard_ge_flow
    {ε : ℝ} {P : Set (Fin 6 → ℝ)} {S : Set (ℝ → Vec)}
    (hε : 0 ≤ ε) (hSfin : S.Finite)
    (hP : ∀ s ∈ P, IsTarget (1 : ℝ) 2 3 1 (keplerFlow s))
    (heq : ∀ s ∈ P,
      keplerFlow s 0 = keplerIC s 0 ∧
        keplerFlow s (1 / 4 : ℝ) = keplerIC s (1 / 4) ∧
        keplerFlow s (1 / 2 : ℝ) = keplerIC s (1 / 2) ∧
        keplerFlow s 1 = keplerIC s 1)
    (hsep : ∀ x ∈ P, ∀ y ∈ P, x ≠ y → 8 * ε < ‖sdCart y - sdCart x‖)
    (hcov : IsExhaustiveCover (1 : ℝ) 2 3 1 ε obs S) :
    P.ncard ≤ S.ncard := by
  classical
  obtain ⟨_, hrec⟩ := hcov
  let f : (Fin 6 → ℝ) → (ℝ → Vec) := fun s =>
    if hs : s ∈ P then Classical.choose (hrec (keplerFlow s) (hP s hs)) else obs
  have hfmem : ∀ s ∈ P, f s ∈ S := by
    intro s hs
    simpa [f, dif_pos hs] using (Classical.choose_spec (hrec (keplerFlow s) (hP s hs))).1
  have hfrec : ∀ s ∈ P, RecoveredBy obs ε 1 (f s) (keplerFlow s) := by
    intro s hs
    simpa [f, dif_pos hs] using (Classical.choose_spec (hrec (keplerFlow s) (hP s hs))).2
  refine Set.ncard_le_ncard_of_injOn f hfmem ?_ hSfin
  intro x hx y hy hxy
  by_contra hne
  exact not_both_recovered_flow (heq x hx) (heq y hy) hε (hsep x hx y hy hne)
    (hfrec x hx) (hxy ▸ hfrec y hy)

def statement : Prop :=
  ¬ (∀ μ R₁ R₂ : ℝ, 0 < μ → 1 < R₁ → R₁ < R₂ → μ ≤ R₁ ^ 3 →
    ∃ (d : ℕ) (C : ℝ), d ≤ 5 ∧ 0 < C ∧
      ∀ T ε : ℝ, 1 ≤ T → μ * T ^ 2 ≤ R₁ ^ 3 → 0 < ε → ε ≤ 1 →
        ∀ e : ℝ → Vec, IsObserver μ T e →
          ∃ S : Set (ℝ → Vec), S.Finite ∧
            (S.ncard : ℝ) * ε ^ d ≤ C ∧
            IsExhaustiveCover μ R₁ R₂ T ε e S)

theorem proof : statement := by
  intro H
  have hμ : (0 : ℝ) < 1 := by norm_num
  have hR₁ : (1 : ℝ) < 2 := by norm_num
  have hR₁₂ : (2 : ℝ) < 3 := by norm_num
  have hμR : (1 : ℝ) ≤ (2 : ℝ) ^ 3 := by norm_num
  obtain ⟨d, C, hd, hCpos, hall⟩ := H 1 2 3 hμ hR₁ hR₁₂ hμR
  obtain ⟨σ, r, hσ, hr, htarget, hsample, hlin⟩ := exists_pack_radius
  let c : ℝ := σ * r / 16
  have hc : 0 < c := by positivity
  let Pack : ℝ → Set (Fin 6 → ℝ) := fun ε =>
    Set.range (cartPt (Nat.floor (c / ε) + 1) (16 * ε / σ))
  have hlb : ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 2 → ((Pack ε).ncard : ℝ) ≥ (c / ε) ^ 6 := by
    intro ε hεpos hεle
    let δ : ℝ := 16 * ε / σ
    let n : ℕ := Nat.floor (c / ε) + 1
    have hδ : 0 < δ := by positivity
    have hn : 0 < n := Nat.succ_pos _
    have hceil : (c / ε) < (n : ℝ) := by
      simpa [n] using Nat.lt_floor_add_one (c / ε)
    have hnge : c / ε ≤ (n : ℝ) := le_of_lt hceil
    have hcε : 0 ≤ c / ε := le_of_lt (div_pos hc hεpos)
    have hpow : (c / ε) ^ 6 ≤ (n : ℝ) ^ 6 :=
      pow_le_pow_left₀ hcε hnge 6
    have hncard : ((Set.range (cartPt n δ)).ncard : ℝ) = (n : ℝ) ^ 6 :=
      packing_cartPt_ncard hδ
    simpa [Pack, δ, n] using (hpow.trans_eq hncard.symm)
  refine packing_eps5_unbounded_scaled Pack hc hlb ⟨C, ?_⟩
  intro ε hεpos hεle
  have hε1 : ε ≤ 1 := hεle.trans (by norm_num)
  have hT : (1 : ℝ) ≤ 1 := le_rfl
  have hμT : (1 : ℝ) * (1 : ℝ) ^ 2 ≤ (2 : ℝ) ^ 3 := by norm_num
  obtain ⟨S, hSfin, hbound, hcov⟩ :=
    hall 1 ε hT hμT hεpos hε1 obs (isObserver_obs 1)
  let δ : ℝ := 16 * ε / σ
  let n : ℕ := Nat.floor (c / ε) + 1
  have hδ : 0 < δ := by positivity
  have hn : 0 < n := Nat.succ_pos _
  have h8 : 8 * ε < σ * δ := by
    have heqδ : σ * δ = 16 * ε := by
      simp [δ]; field_simp [hσ.ne']
    rw [heqδ]; nlinarith
  have hbd : δ * ((n : ℝ) - 1) / 2 < r := by
    have hn1 : (n : ℝ) - 1 = (Nat.floor (c / ε) : ℝ) := by
      simp [n, Nat.cast_add, Nat.cast_one]
    have hfl : (Nat.floor (c / ε) : ℝ) ≤ c / ε :=
      Nat.floor_le (le_of_lt (div_pos hc hεpos))
    have hmid : δ * ((n : ℝ) - 1) / 2 ≤ δ * (c / ε) / 2 := by
      have hx : δ * ((n : ℝ) - 1) / 2 = (δ / 2) * ((n : ℝ) - 1) := by ring
      have hy : δ * (c / ε) / 2 = (δ / 2) * (c / ε) := by ring
      rw [hx, hy, hn1]
      exact mul_le_mul_of_nonneg_left hfl (by positivity)
    have hsimp : δ * (c / ε) / 2 = r / 2 := by
      simp only [δ, c]
      field_simp [hσ.ne', hεpos.ne']
    have hhalf : δ * ((n : ℝ) - 1) / 2 ≤ r / 2 := by
      simpa [hsimp] using hmid
    linarith
  let P : Set (Fin 6 → ℝ) := Set.range (cartPt n δ)
  have hP : ∀ s ∈ P, IsTarget (1 : ℝ) 2 3 1 (keplerFlow s) := by
    intro s hs
    obtain ⟨u, rfl⟩ := hs
    exact htarget _ (cartPt_mem_ball hn hδ.le hbd u)
  have heq : ∀ s ∈ P,
      keplerFlow s 0 = keplerIC s 0 ∧
        keplerFlow s (1 / 4 : ℝ) = keplerIC s (1 / 4) ∧
        keplerFlow s (1 / 2 : ℝ) = keplerIC s (1 / 2) ∧
        keplerFlow s 1 = keplerIC s 1 := by
    intro s hs
    obtain ⟨u, rfl⟩ := hs
    exact hsample _ (cartPt_mem_ball hn hδ.le hbd u)
  have hsep : ∀ x ∈ P, ∀ y ∈ P, x ≠ y → 8 * ε < ‖sdCart y - sdCart x‖ := by
    intro x hx y hy hne
    obtain ⟨u, rfl⟩ := hx
    obtain ⟨v, rfl⟩ := hy
    have huv : u ≠ v := fun h => hne (by rw [h])
    have hge := cartPt_sdCart_sep hσ hδ hr hn hlin hbd huv
    exact h8.trans_le hge
  have hε0 : 0 ≤ ε := hεpos.le
  have hnle : P.ncard ≤ S.ncard :=
    exhaustive_ncard_ge_flow hε0 hSfin hP heq hsep hcov
  have hPpack : P = Pack ε := by simp [P, Pack, n, δ]
  have hge : ((Pack ε).ncard : ℝ) * ε ^ 5 ≤ (S.ncard : ℝ) * ε ^ 5 := by
    have : (P.ncard : ℝ) ≤ (S.ncard : ℝ) := Nat.cast_le.mpr hnle
    have hpow0 : 0 ≤ ε ^ 5 := pow_nonneg hε0 5
    simpa [hPpack] using mul_le_mul_of_nonneg_right this hpow0
  have h5 : (S.ncard : ℝ) * ε ^ 5 ≤ C := by
    have hsplit : ε ^ 5 = ε ^ d * ε ^ (5 - d) := by
      rw [← pow_add, Nat.add_sub_of_le hd]
    have hpow1 : ε ^ (5 - d) ≤ 1 :=
      pow_le_one₀ hε0 (hε1)
    have hSn : 0 ≤ (S.ncard : ℝ) := Nat.cast_nonneg _
    have hεd : 0 ≤ ε ^ d := pow_nonneg hε0 d
    calc
      (S.ncard : ℝ) * ε ^ 5
          = (S.ncard : ℝ) * (ε ^ d * ε ^ (5 - d)) := by rw [hsplit]
      _ = ((S.ncard : ℝ) * ε ^ d) * ε ^ (5 - d) := by ring
      _ ≤ C * ε ^ (5 - d) := mul_le_mul_of_nonneg_right hbound (pow_nonneg hε0 _)
      _ ≤ C * 1 := mul_le_mul_of_nonneg_left hpow1 hCpos.le
      _ = C := mul_one C
  exact hge.trans h5

end

end Submissions.TestOrbitCoverFalse.Gtokman
