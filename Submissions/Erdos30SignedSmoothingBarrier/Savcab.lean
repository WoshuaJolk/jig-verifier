import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum

/-!
Aggregate-centered extension of declangessel's finite 13/18 obstruction.
The helper proofs are reused from Jig artifact
c8345672-b649-4393-8e1f-4aa2455e5c66, statement Erdos30SmoothingBarrier13_18,
module Submissions.Erdos30SmoothingBarrier13_18.Declan, retrieved 2026-09-07.
The only substantive change is that the aggregate midpoint mean equals m/2;
individual kernel symmetry is neither assumed nor used. This is a barrier
for the specified finite smoothing certificate family, not a Sidon bound.
-/
noncomputable section
namespace SmoothingLimit
open Finset

def cdfBefore (p : ℕ → ℝ) (n : ℕ) : ℝ := ∑ i ∈ range n, p i

def midpoint (p : ℕ → ℝ) (n : ℕ) : ℝ := cdfBefore p n + p n / 2

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

theorem half_weight_nonneg (C : ℕ → ℝ) (n : ℕ) (hn : 0 < n)
    (hC : ∀ q < n, 0 ≤ C q) :
    0 ≤ (∑ q ∈ range n, C q) - C 0/2 := by
  have h0 := hC 0 hn
  have hh : C 0 ≤ ∑ q ∈ range n, C q :=
    single_le_sum (fun q hq => hC q (mem_range.mp hq)) (mem_range.mpr hn)
  linarith

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

def aValue {R : Type*} [Fintype R] (m : ℕ) (lam : R → ℝ) (p : R → ℕ → ℝ) : ℝ :=
  (m:ℝ) * ∑ r, lam r * ∑ i ∈ range m, p r i ^ 2

def bValue {R : Type*} [Fintype R] (m L : ℕ) (lam : R → ℝ) (w : R → ℕ → ℝ) : ℝ :=
  1 + 2 * ((∑ r, lam r * ∑ j ∈ range (L*m), w r j ^ 2)/(m:ℝ) - L)

theorem certificate_remainder_bound {R : Type*} [Fintype R]
    (m L : ℕ) (hm : 0 < m) (hL : 0 < L)
    (lam : R → ℝ) (p w : R → ℕ → ℝ)
    (hlam_nonneg : ∀ r, 0 ≤ lam r) (hlam : ∑ r, lam r = 1)
    (hmass : ∀ r, ∑ i ∈ range m, p r i = 1)
    (hcenter : (∑ r, lam r * ∑ i ∈ range m, midpoint (p r) i) = (m:ℝ)/2)
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
        (m:ℝ) - (∑ j ∈ range m, midpoint (p r) j) -
          (∑ j ∈ range m, midpoint (p r) j * (1-midpoint (p r) j)) := by
      intro r
      have hn' : (m:ℝ) = ∑ j ∈ range m, (1:ℝ) := by simp
      rw [hn', ← sum_sub_distrib, ← sum_sub_distrib]
      apply sum_congr rfl
      intro j _
      ring
    simp_rw [he, mul_sub]
    rw [sum_sub_distrib, sum_sub_distrib, ← sum_mul, hlam, hcenter]
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

end SmoothingLimit


/-! Exact identities for finite, aperiodic correlations of signed kernels.
No positivity, symmetry, or probability hypothesis is used in the identities.
The imported midpoint definition and elementary prefix identity are attributed
in Generalized.lean to the existing Jig smoothing-barrier proof.
-/
noncomputable section
namespace SignedCorrelationBarrier
open Finset SmoothingLimit

def positiveCorrelation (p : ℕ → ℝ) (m d : ℕ) : ℝ :=
  ∑ i ∈ range (m-(d+1)), p (i+d+1)*p i

theorem triangular_reindex (f : ℕ → ℕ → ℝ) (m : ℕ) :
    (∑ d ∈ range m, ∑ i ∈ range (m-(d+1)), f i (i+d+1)) =
      ∑ j ∈ range m, ∑ i ∈ range j, f i j := by
  rw [sum_sigma', sum_sigma']
  refine sum_nbij' (fun x => ⟨x.2+x.1+1,x.2⟩)
    (fun y => ⟨y.1-y.2-1,y.2⟩) ?_ ?_ ?_ ?_ ?_
  · rintro ⟨d,i⟩ h
    simp only [mem_sigma, mem_range] at h ⊢
    omega
  · rintro ⟨j,i⟩ h
    simp only [mem_sigma, mem_range] at h ⊢
    omega
  · rintro ⟨d,i⟩ h
    apply Sigma.ext
    · dsimp
      omega
    · rfl
  · rintro ⟨j,i⟩ h
    simp only [mem_sigma, mem_range] at h
    apply Sigma.ext
    · dsimp
      omega
    · rfl
  · intro x hx
    rfl

theorem positiveCorrelation_total (p : ℕ → ℝ) (m : ℕ) :
    (∑ i ∈ range m, p i^2) + 2*(∑ d ∈ range m, positiveCorrelation p m d) =
      (cdfBefore p m)^2 := by
  unfold positiveCorrelation
  rw [triangular_reindex (fun i j => p j*p i) m]
  simp_rw [← mul_sum]
  have h := cdf_product_identity p p m
  simpa only [cdfBefore, pow_two] using (by nlinarith only [h] :
    (∑ i ∈ range m, p i*p i) +
      2*(∑ i ∈ range m, p i*cdfBefore p i) = (cdfBefore p m)^2)

theorem sum_midpoint (p : ℕ → ℝ) (m : ℕ) :
    (∑ i ∈ range m, midpoint p i) =
      (m:ℝ)*cdfBefore p m - (∑ i ∈ range m, (i:ℝ)*p i) - cdfBefore p m/2 := by
  induction m with
  | zero => simp [cdfBefore]
  | succ m ih =>
    rw [sum_range_succ, sum_range_succ, ih]
    have hf : cdfBefore p (m+1) = cdfBefore p m+p m := by
      simp [cdfBefore, sum_range_succ]
    rw [hf]
    simp only [midpoint, Nat.cast_add, Nat.cast_one]
    ring

theorem midpoint_distance_identity (p : ℕ → ℝ) (m : ℕ) :
    (∑ i ∈ range m, midpoint p i*(cdfBefore p m-midpoint p i)) =
      (∑ j ∈ range m, ∑ i ∈ range j, ((j:ℝ)-(i:ℝ))*p j*p i) +
        (∑ i ∈ range m, p i^2)/4 := by
  induction m with
  | zero => simp [cdfBefore]
  | succ m ih =>
    have hf : cdfBefore p (m+1) = cdfBefore p m+p m := by
      simp [cdfBefore, sum_range_succ]
    rw [sum_range_succ, sum_range_succ, sum_range_succ, hf]
    have hsplit :
        (∑ i ∈ range m, midpoint p i*(cdfBefore p m+p m-midpoint p i)) =
          (∑ i ∈ range m, midpoint p i*(cdfBefore p m-midpoint p i)) +
            p m*(∑ i ∈ range m, midpoint p i) := by
      rw [mul_sum, ← sum_add_distrib]
      apply sum_congr rfl
      intro i hi
      ring
    rw [hsplit, ih, sum_midpoint]
    have hdist : (∑ i ∈ range m, ((m:ℝ)-(i:ℝ))*p m*p i) =
        p m*((m:ℝ)*cdfBefore p m-(∑ i ∈ range m, (i:ℝ)*p i)) := by
      unfold cdfBefore
      rw [mul_sub]
      simp_rw [mul_sum]
      rw [← sum_sub_distrib]
      apply sum_congr rfl
      intro i hi
      ring
    rw [hdist]
    unfold midpoint
    ring

theorem midpoint_correlation_identity (p : ℕ → ℝ) (m : ℕ)
    (hmass : ∑ i ∈ range m, p i = 1) :
    (∑ i ∈ range m, midpoint p i*(1-midpoint p i)) =
      (∑ d ∈ range m, ((d:ℝ)+1)*positiveCorrelation p m d) +
        (∑ i ∈ range m, p i^2)/4 := by
  have h := midpoint_distance_identity p m
  have hm : cdfBefore p m = 1 := hmass
  rw [hm] at h
  rw [h]
  congr 1
  unfold positiveCorrelation
  simp_rw [mul_sum]
  have he : (∑ d ∈ range m, ∑ i ∈ range (m-(d+1)),
      ((d:ℝ)+1)*(p (i+d+1)*p i)) =
      ∑ d ∈ range m, ∑ i ∈ range (m-(d+1)),
        (((i+d+1:ℕ):ℝ)-(i:ℝ))*p (i+d+1)*p i := by
    apply sum_congr rfl
    intro d hd
    apply sum_congr rfl
    intro i hi
    push_cast
    ring
  rw [he, triangular_reindex (fun i j => ((j:ℝ)-(i:ℝ))*p j*p i) m]

end SignedCorrelationBarrier


/-!
Finite capped-correlation moment bound. For a zero-extended signed kernel,
use A=C(0) and c(i)=C(i+1); this algebraic lemma assumes the correlation
bounds explicitly. The application to boundary certificates also uses
SmoothingLimit.certificate_remainder_bound and midpoint_pairing, adapted
from declangessel's Erdos30SmoothingBarrier13_18 contribution.
-/
namespace SignedCorrelationBarrier
open Finset

/-- Concentrating bounded nonnegative masses at the earliest indices minimizes
this discrete first moment. No optimization or limiting argument is used. -/
theorem capped_sequence_moment (c : ℕ → ℝ) (A : ℝ) (n : ℕ) :
    (∀ i < n, 0 ≤ c i) → (∀ i < n, c i ≤ A) →
    (∑ i ∈ range n, c i)^2 ≤ A*(∑ i ∈ range n, (2*(i:ℝ)+1)*c i) := by
  induction n with
  | zero => simp
  | succ n ih =>
    intro h0 hcap
    have hn0 : 0 ≤ c n := h0 n (by omega)
    have hncap : c n ≤ A := hcap n (by omega)
    have hprev := ih (fun i hi => h0 i (by omega)) (fun i hi => hcap i (by omega))
    have hsum : (∑ i ∈ range n, c i) ≤ (n:ℝ)*A := by
      calc
        _ ≤ ∑ _i ∈ range n, A := sum_le_sum fun i hi => hcap i (by
          have := mem_range.mp hi
          omega)
        _ = _ := by simp
    have hcross := mul_le_mul_of_nonneg_right hsum hn0
    have hdiag := mul_le_mul_of_nonneg_right hncap hn0
    rw [sum_range_succ, sum_range_succ]
    nlinarith only [hprev, hcross, hdiag]

/-- Unit total correlation mass gives a uniform positive product, including
its exact finite diagonal correction. -/
theorem correlation_moment_lower (c : ℕ → ℝ) (A : ℝ) (n : ℕ)
    (h0 : ∀ i < n, 0 ≤ c i) (hcap : ∀ i < n, c i ≤ A)
    (hmass : A + 2*(∑ i ∈ range n, c i) = 1) :
    (1+A^2)/8 ≤ A*((∑ i ∈ range n, ((i:ℝ)+1)*c i)+A/4) := by
  have h := capped_sequence_moment c A n h0 hcap
  have he : (∑ i ∈ range n, (2*(i:ℝ)+1)*c i) =
      2*(∑ i ∈ range n, ((i:ℝ)+1)*c i) - ∑ i ∈ range n, c i := by
    rw [mul_sum, ← sum_sub_distrib]
    apply sum_congr rfl
    intro i _
    ring
  have hS : (∑ i ∈ range n, c i) = (1-A)/2 := by linarith
  rw [he, hS] at h
  nlinarith only [h]

theorem correlation_moment_ge_one_eighth (c : ℕ → ℝ) (A : ℝ) (n : ℕ)
    (h0 : ∀ i < n, 0 ≤ c i) (hcap : ∀ i < n, c i ≤ A)
    (hmass : A + 2*(∑ i ∈ range n, c i) = 1) :
    (1:ℝ)/8 ≤ A*((∑ i ∈ range n, ((i:ℝ)+1)*c i)+A/4) := by
  have h := correlation_moment_lower c A n h0 hcap hmass
  nlinarith [sq_nonneg A]

end SignedCorrelationBarrier


namespace SignedCorrelationBarrier
open Finset

/-- Every complete positive-shift autocorrelation is bounded above by the
zero-shift energy, even for signed finite kernels. -/
theorem aperiodic_correlation_le_energy (p : ℕ → ℝ) (m d : ℕ) :
    (∑ i ∈ range (m-(d+1)), p (i+d+1)*p i) ≤ ∑ i ∈ range m, (p i)^2 := by
  have hshift : (∑ i ∈ range (m-(d+1)), (p (i+d+1))^2) ≤
      ∑ i ∈ range m, (p i)^2 := by
    rw [← sum_image (f := fun j : ℕ => (p j)^2) (show Set.InjOn (fun i : ℕ => i+d+1)
      (range (m-(d+1)) : Set ℕ) from by
        intro i _ j _ he
        change i+d+1=j+d+1 at he
        omega)]
    apply sum_le_sum_of_subset_of_nonneg
    · intro j hj
      obtain ⟨i, hi, rfl⟩ := mem_image.mp hj
      have hi' := mem_range.mp hi
      apply mem_range.mpr
      omega
    · intro j _ _
      exact sq_nonneg (p j)
  have hprefix : (∑ i ∈ range (m-(d+1)), (p i)^2) ≤
      ∑ i ∈ range m, (p i)^2 :=
    sum_le_sum_of_subset_of_nonneg (range_mono (Nat.sub_le _ _))
      (fun j _ _ => sq_nonneg (p j))
  have htwice : 2*(∑ i ∈ range (m-(d+1)), p (i+d+1)*p i) ≤
      (∑ i ∈ range (m-(d+1)), (p (i+d+1))^2) +
        ∑ i ∈ range (m-(d+1)), (p i)^2 := by
    rw [mul_sum, ← sum_add_distrib]
    apply sum_le_sum
    intro i _
    nlinarith [sq_nonneg (p (i+d+1)-p i)]
  linarith

end SignedCorrelationBarrier


/-!
Conditional signed-kernel cover barrier. The explicit energy-moment
inequality is an assumption here; no kernel or midpoint positivity is used.
The cover remainder and midpoint pairing come from Generalized.lean,
which adapts declangessel's finite smoothing-certificate proof.
-/

noncomputable section
namespace SignedCorrelationBarrier
open Finset SmoothingLimit

/-- An explicit AU moment bound replaces the nonnegative-kernel argument. -/
theorem signed_remainder_obstruction {ι : Type*} [Fintype ι]
    (μ p V : ι → ℝ) (U a b m : ℝ)
    (hμ : ∀ i, 0 ≤ μ i)
    (hmoment : (1 + (∑ i, μ i * p i ^ 2)^2) / 8 ≤
      (∑ i, μ i * p i ^ 2) * U)
    (hpair : (1 : ℝ) / 2 ≤ ∑ i, μ i * p i * V i)
    (ha : a = m * ∑ i, μ i * p i ^ 2)
    (henergy : 2 * U + 2 * (∑ i, μ i * V i ^ 2) ≤ m * b) :
    (3 : ℝ) / 4 + (∑ i, μ i * p i ^ 2)^2 / 4 ≤ a * b := by
  have hA : 0 ≤ ∑ i, μ i * p i ^ 2 :=
    sum_nonneg fun i _ => mul_nonneg (hμ i) (sq_nonneg _)
  have hCS := weighted_cauchy μ p V hμ
  have hAS : (1 : ℝ) / 4 ≤
      (∑ i, μ i * p i ^ 2) * (∑ i, μ i * V i ^ 2) := by
    nlinarith [sq_nonneg ((∑ i, μ i * p i * V i) - 1 / 2)]
  have he := mul_le_mul_of_nonneg_left henergy hA
  rw [ha]
  nlinarith

private theorem flatten_sum {R : Type*} [Fintype R]
    (m : ℕ) (lam : R → ℝ) (f : R → ℕ → ℝ) :
    (∑ z : R × Fin m, lam z.1 * f z.1 z.2) =
      ∑ r, lam r * ∑ i ∈ range m, f r i := by
  rw [Fintype.sum_prod_type]
  apply sum_congr rfl
  intro r _
  dsimp only
  rw [Fin.sum_univ_eq_sum_range (fun i => lam r * f r i) m, mul_sum]

/-- Aggregate-centered mass-one signed covers obey the finite corrected bound
provided the stated AU moment inequality holds. -/
theorem signed_certificate_product_lower_bound {R : Type*} [Fintype R]
    (m L : ℕ) (hm : 0 < m) (hL : 0 < L)
    (lam : R → ℝ) (p w : R → ℕ → ℝ)
    (hlam_nonneg : ∀ r, 0 ≤ lam r) (hlam : ∑ r, lam r = 1)
    (hmass : ∀ r, ∑ i ∈ range m, p r i = 1)
    (hcenter : (∑ r, lam r * ∑ i ∈ range m, midpoint (p r) i) = (m : ℝ) / 2)
    (hw : ∀ r j, L * m ≤ j → w r j = 1)
    (hc : ∀ q ≤ L * m, 1 ≤ ∑ r, lam r * ∑ i ∈ range m, p r i * w r (q+i))
    (hmoment : (1 + (∑ r, lam r * ∑ i ∈ range m, p r i ^ 2)^2) / 8 ≤
      (∑ r, lam r * ∑ i ∈ range m, p r i ^ 2) *
      (∑ r, lam r * ∑ i ∈ range m, midpoint (p r) i * (1-midpoint (p r) i))) :
    (3 : ℝ) / 4 + (∑ r, lam r * ∑ i ∈ range m, p r i ^ 2)^2 / 4 ≤
      aValue m lam p * bValue m L lam w := by
  let μ : R × Fin m → ℝ := fun z => lam z.1
  let P : R × Fin m → ℝ := fun z => p z.1 z.2
  let V : R × Fin m → ℝ := fun z => w z.1 z.2 - midpoint (p z.1) z.2
  let U : ℝ := ∑ r, lam r * ∑ i ∈ range m,
    midpoint (p r) i * (1-midpoint (p r) i)
  have hμ : ∀ z, 0 ≤ μ z := fun z => hlam_nonneg z.1
  have heA : (∑ z, μ z * P z ^ 2) =
      ∑ r, lam r * ∑ i ∈ range m, p r i ^ 2 :=
    flatten_sum m lam (fun r i => p r i ^ 2)
  have heS : (∑ z, μ z * V z ^ 2) =
      ∑ r, lam r * ∑ i ∈ range m, (w r i - midpoint (p r) i)^2 :=
    flatten_sum m lam (fun r i => (w r i - midpoint (p r) i)^2)
  have hpair : (1 : ℝ) / 2 ≤ ∑ z, μ z * P z * V z := by
    have he : (∑ z, μ z * P z * V z) =
        ∑ r, lam r * ∑ i ∈ range m, p r i * (w r i-midpoint (p r) i) := by
      dsimp [μ, P, V]
      simp_rw [mul_assoc]
      exact flatten_sum m lam (fun r i => p r i * (w r i-midpoint (p r) i))
    have hPm : ∀ r, (∑ i ∈ range m, p r i * midpoint (p r) i) = (1 : ℝ) / 2 :=
      fun r => midpoint_pairing (p r) m (hmass r)
    rw [he]
    simp_rw [mul_sub, sum_sub_distrib, hPm, mul_sub]
    rw [sum_sub_distrib, ← sum_mul, hlam]
    have h0 : 1 ≤ ∑ r, lam r * ∑ i ∈ range m, p r i * w r i := by
      simpa only [zero_add] using hc 0 (by omega)
    linarith
  have henergy : 2 * U + 2 * (∑ z, μ z * V z ^ 2) ≤
      (m : ℝ) * bValue m L lam w := by
    rw [heS]
    exact certificate_remainder_bound m L hm hL lam p w
      hlam_nonneg hlam hmass hcenter hw hc
  have hmom : (1 + (∑ z, μ z * P z ^ 2)^2) / 8 ≤
      (∑ z, μ z * P z ^ 2) * U := by
    rw [heA]
    exact hmoment
  have ha : aValue m lam p = (m : ℝ) * ∑ z, μ z * P z ^ 2 := by
    rw [heA]
    rfl
  have h := signed_remainder_obstruction μ P V U (aValue m lam p)
    (bValue m L lam w) (m : ℝ) hμ hmom hpair ha henergy
  rwa [heA] at h

end SignedCorrelationBarrier


/-!
Aggregate-centered signed smoothing certificates with nonnegative aggregate
aperiodic positive correlations. Kernel entries and individual correlations
may have either sign. This proves a certificate barrier, not a Sidon bound.
-/
noncomputable section
namespace SignedCorrelationBarrier
open Finset SmoothingLimit

theorem centered_signed_product_lower_bound {R : Type*} [Fintype R]
    (m L : ℕ) (hm : 0 < m) (hL : 0 < L)
    (lam : R → ℝ) (p w : R → ℕ → ℝ)
    (hlam_nonneg : ∀ r, 0 ≤ lam r) (hlam : ∑ r, lam r = 1)
    (hmass : ∀ r, ∑ i ∈ range m, p r i = 1)
    (hcenter : (∑ r, lam r * ∑ i ∈ range m, midpoint (p r) i) = (m : ℝ) / 2)
    (hw : ∀ r j, L * m ≤ j → w r j = 1)
    (hc : ∀ q ≤ L * m, 1 ≤ ∑ r, lam r * ∑ i ∈ range m, p r i * w r (q+i))
    (hcor : ∀ d < m, 0 ≤ ∑ r, lam r * positiveCorrelation (p r) m d) :
    (3 : ℝ) / 4 + (∑ r, lam r * ∑ i ∈ range m, p r i ^ 2)^2 / 4 ≤
      aValue m lam p * bValue m L lam w := by
  let E : ℝ := ∑ r, lam r * ∑ i ∈ range m, p r i ^ 2
  let C : ℕ → ℝ := fun d => ∑ r, lam r * positiveCorrelation (p r) m d
  let U : ℝ := ∑ r, lam r * ∑ i ∈ range m,
    midpoint (p r) i * (1-midpoint (p r) i)
  have hcap : ∀ d < m, C d ≤ E := by
    intro d _
    apply sum_le_sum
    intro r _
    exact mul_le_mul_of_nonneg_left
      (aperiodic_correlation_le_energy (p r) m d) (hlam_nonneg r)
  have hCsum : (∑ d ∈ range m, C d) =
      ∑ r, lam r * ∑ d ∈ range m, positiveCorrelation (p r) m d := by
    dsimp [C]
    rw [sum_comm]
    simp_rw [← mul_sum]
  have htotal : E + 2 * (∑ d ∈ range m, C d) = 1 := by
    have hr : ∀ r, (∑ i ∈ range m, p r i ^ 2) +
        2 * (∑ d ∈ range m, positiveCorrelation (p r) m d) = 1 := by
      intro r
      simpa only [cdfBefore, hmass r, one_pow] using positiveCorrelation_total (p r) m
    rw [hCsum]
    dsimp [E]
    calc
      _ = ∑ r, lam r * ((∑ i ∈ range m, p r i ^ 2) +
          2 * (∑ d ∈ range m, positiveCorrelation (p r) m d)) := by
        rw [mul_sum, ← sum_add_distrib]
        apply sum_congr rfl
        intro r _
        ring
      _ = 1 := by simp_rw [hr, mul_one]; exact hlam
  have hU : U = (∑ d ∈ range m, ((d : ℝ)+1) * C d) + E / 4 := by
    have hsplit : U =
        (∑ r, lam r * ∑ d ∈ range m, ((d : ℝ)+1) * positiveCorrelation (p r) m d) +
          E / 4 := by
      dsimp [U, E]
      rw [sum_div, ← sum_add_distrib]
      apply sum_congr rfl
      intro r _
      rw [midpoint_correlation_identity (p r) m (hmass r)]
      ring
    rw [hsplit]
    congr 1
    dsimp [C]
    simp_rw [mul_sum]
    rw [sum_comm]
    apply sum_congr rfl
    intro d _
    apply sum_congr rfl
    intro r _
    ring
  have hmoment : (1 + E^2) / 8 ≤ E * U := by
    rw [hU]
    exact correlation_moment_lower C E m hcor hcap htotal
  exact signed_certificate_product_lower_bound m L hm hL lam p w
    hlam_nonneg hlam hmass hcenter hw hc hmoment

end SignedCorrelationBarrier


namespace SignedCorrelationBarrier
open Finset

/-- Reversing a finite signed kernel preserves every aperiodic correlation. -/
theorem positiveCorrelation_reverse (p : ℕ → ℝ) (m d : ℕ) :
    positiveCorrelation (fun i => p (m-1-i)) m d = positiveCorrelation p m d := by
  unfold positiveCorrelation
  calc
    _ = ∑ i ∈ range (m-(d+1)),
        p (m-(d+1)-1-i+d+1)*p (m-(d+1)-1-i) := by
      apply sum_congr rfl
      intro i hi
      have hi' := mem_range.mp hi
      have h1 : m-1-(i+d+1) = m-(d+1)-1-i := by omega
      have h2 : m-1-i = m-(d+1)-1-i+d+1 := by omega
      dsimp only
      rw [h1, h2]
      exact mul_comm _ _
    _ = _ := sum_range_reflect (fun i => p (i+d+1)*p i) (m-(d+1))

end SignedCorrelationBarrier


/-! Reflection helpers and cover pairing reuse the proof of Jig statement11,
artifact0a0bcaa2-b707-46cc-826a-d758c541323a, extending its scope to signed
kernels with nonnegative aggregate aperiodic correlations. No kernel value
or individual product is required to be nonnegative. -/
noncomputable section
namespace SmoothingLimit
open Finset

/-- Midpoint sums without a symmetry assumption. -/
theorem midpoint_sum_general (p : ℕ → ℝ) (m : ℕ)
    (hmass : cdfBefore p m = 1) :
    (∑ i ∈ range m, midpoint p i) =
      (m:ℝ) - 1/2 - ∑ i ∈ range m, (i:ℝ)*p i := by
  have hid := cdf_product_identity p (fun _ => 1) m
  simp only [cdfBefore, sum_const, card_range, nsmul_eq_mul, mul_one, one_mul] at hid
  have he : (∑ i ∈ range m, midpoint p i) =
      (∑ i ∈ range m, cdfBefore p i) + cdfBefore p m / 2 := by
    simp [midpoint, sum_add_distrib, ← sum_div, cdfBefore]
  rw [he, hmass]
  simp only [mul_comm (p _)] at hid
  change (∑ i ∈ range m, (i:ℝ)*p i) + (∑ i ∈ range m, cdfBefore p i) +
    (∑ i ∈ range m, p i) = (∑ i ∈ range m, p i) * (m:ℝ) at hid
  change (∑ i ∈ range m, p i) = 1 at hmass
  rw [hmass] at hid
  linarith

theorem reverse_mass (p : ℕ → ℝ) (m : ℕ) :
    (∑ i ∈ range m, p (m-1-i)) = ∑ i ∈ range m, p i :=
  sum_range_reflect p m

theorem midpoint_reverse_sum (p : ℕ → ℝ) (m : ℕ) (hm : 0 < m)
    (hmass : cdfBefore p m = 1) :
    (∑ i ∈ range m, midpoint p i) +
      (∑ i ∈ range m, midpoint (fun j => p (m-1-j)) i) = (m:ℝ) := by
  have hrev : cdfBefore (fun j => p (m-1-j)) m = 1 := by
    unfold cdfBefore
    rw [reverse_mass]
    exact hmass
  rw [midpoint_sum_general p m hmass,
    midpoint_sum_general (fun j => p (m-1-j)) m hrev]
  have he : (∑ i ∈ range m, (i:ℝ)*p (m-1-i)) =
      (m:ℝ)-1 - ∑ i ∈ range m, (i:ℝ)*p i := by
    have hr := sum_range_reflect (fun i => (i:ℝ)*p (m-1-i)) m
    have hsum : (∑ i ∈ range m,
        ((m-1-i:ℕ):ℝ)*p (m-1-(m-1-i))) =
        ((m:ℝ)-1)*cdfBefore p m - ∑ i ∈ range m, (i:ℝ)*p i := by
      unfold cdfBefore
      rw [mul_sum, ← sum_sub_distrib]
      apply sum_congr rfl
      intro i hi
      have hi' := mem_range.mp hi
      have hn : m-1-(m-1-i) = i := by omega
      have hc : ((m-1-i:ℕ):ℝ) = (m:ℝ)-1-i := by
        rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega), Nat.cast_one]
      rw [hn,hc]
      ring
    rw [hsum,hmass] at hr
    linarith
  rw [he]
  ring

end SmoothingLimit

namespace SignedCorrelationBarrier
open Finset SmoothingLimit

/-- Signed reflected pairs preserve the aggregate aperiodic correlations. -/
theorem asymmetric_signed_product_lower_bound {R : Type*} [Fintype R]
    (m L : ℕ) (hm : 0 < m) (hL : 0 < L)
    (lam : R → ℝ) (p wLeft wRight : R → ℕ → ℝ)
    (hlam_nonneg : ∀ r, 0 ≤ lam r) (hlam : ∑ r, lam r = 1)
    (hmass : ∀ r, ∑ i ∈ range m, p r i = 1)
    (hcor : ∀ d < m, 0 ≤ ∑ r, lam r * positiveCorrelation (p r) m d)
    (hwl : ∀ r j, L*m ≤ j → wLeft r j = 1)
    (hwr : ∀ r j, L*m ≤ j → wRight r j = 1)
    (hcl : ∀ q ≤ L*m, 1 ≤ ∑ r, lam r * ∑ i ∈ range m, p r i*wLeft r (q+i))
    (hcr : ∀ q ≤ L*m, 1 ≤ ∑ r, lam r * ∑ i ∈ range m, p r (m-1-i)*wRight r (q+i)) :
    (3:ℝ)/4 + (∑ r, lam r * ∑ i ∈ range m, p r i ^ 2)^2/4 ≤
      ((m:ℝ) * ∑ r, lam r * ∑ i ∈ range m, p r i ^ 2) *
      (1 + (∑ r, lam r * ∑ j ∈ range (L*m),
        (wLeft r j ^ 2 + wRight r j ^ 2))/(m:ℝ) - 2*L) := by
  let μ : R × Bool → ℝ := fun z => lam z.1/2
  let P : R × Bool → ℕ → ℝ := fun z i => if z.2 then p z.1 (m-1-i) else p z.1 i
  let W : R × Bool → ℕ → ℝ := fun z j => if z.2 then wRight z.1 j else wLeft z.1 j
  have hμ : ∀ z, 0 ≤ μ z := fun z => div_nonneg (hlam_nonneg z.1) (by norm_num)
  have hμsum : ∑ z, μ z = 1 := by
    simp only [μ, Fintype.sum_prod_type, Fintype.sum_bool]
    have he : (∑ r, (lam r/2+lam r/2)) = ∑ r, lam r := by
      apply sum_congr rfl
      intro r _
      ring
    rw [he, hlam]
  have hPsum : ∀ z, ∑ i ∈ range m, P z i = 1 := by
    rintro ⟨r,b⟩
    cases b <;> simp [P, reverse_mass, hmass]
  have hWtail : ∀ z j, L*m ≤ j → W z j = 1 := by
    rintro ⟨r,b⟩ j hj
    cases b <;> simp [W, hwl r j hj, hwr r j hj]
  have hcenter : (∑ z, μ z * ∑ i ∈ range m, midpoint (P z) i) = (m:ℝ)/2 := by
    rw [Fintype.sum_prod_type]
    have he : ∀ r, (∑ b : Bool, μ (r,b) * ∑ i ∈ range m, midpoint (P (r,b)) i) =
        lam r * (m:ℝ)/2 := by
      intro r
      simp only [μ, P, Fintype.sum_bool, Bool.false_eq_true, ↓reduceIte]
      have hr := midpoint_reverse_sum (p r) m hm (hmass r)
      nlinarith only [congrArg (fun x => lam r/2*x) hr]
    simp_rw [he]
    rw [← sum_div, ← sum_mul, hlam]
    ring
  have hcover : ∀ q ≤ L*m, 1 ≤ ∑ z, μ z * ∑ i ∈ range m, P z i*W z (q+i) := by
    intro q hq
    have hl := hcl q hq
    have hr := hcr q hq
    have he : (∑ z, μ z * ∑ i ∈ range m, P z i*W z (q+i)) =
        ((∑ r, lam r * ∑ i ∈ range m, p r i*wLeft r (q+i)) +
         (∑ r, lam r * ∑ i ∈ range m, p r (m-1-i)*wRight r (q+i)))/2 := by
      rw [Fintype.sum_prod_type]
      simp only [μ, P, W, Fintype.sum_bool, Bool.false_eq_true, ↓reduceIte]
      rw [sum_add_distrib]
      simp_rw [div_mul_eq_mul_div]
      rw [← sum_div, ← sum_div]
      ring
    rw [he]
    linarith
  have hE : (∑ z, μ z * ∑ i ∈ range m, P z i^2) =
      ∑ r, lam r * ∑ i ∈ range m, p r i^2 := by
    rw [Fintype.sum_prod_type]
    apply sum_congr rfl
    intro r _
    simp only [μ, P, Fintype.sum_bool, Bool.false_eq_true, ↓reduceIte]
    rw [reverse_mass (fun i => p r i^2)]
    ring
  have hA : aValue m μ P = (m:ℝ) * ∑ r, lam r * ∑ i ∈ range m, p r i^2 := by
    unfold aValue
    rw [hE]
  have hC : ∀ d < m, 0 ≤ ∑ z, μ z * positiveCorrelation (P z) m d := by
    intro d hd
    have he : (∑ z, μ z * positiveCorrelation (P z) m d) =
        ∑ r, lam r * positiveCorrelation (p r) m d := by
      rw [Fintype.sum_prod_type]
      apply sum_congr rfl
      intro r _
      simp only [μ, P, Fintype.sum_bool, Bool.false_eq_true, ↓reduceIte]
      rw [positiveCorrelation_reverse]
      ring
    rw [he]
    exact hcor d hd
  have hB : bValue m L μ W =
      1 + (∑ r, lam r * ∑ j ∈ range (L*m),
        (wLeft r j^2+wRight r j^2))/(m:ℝ)-2*L := by
    unfold bValue
    rw [Fintype.sum_prod_type]
    have he : (∑ r, ∑ b : Bool, μ (r,b) * ∑ j ∈ range (L*m), W (r,b) j^2) =
        (∑ r, lam r * ∑ j ∈ range (L*m), (wLeft r j^2+wRight r j^2))/2 := by
      rw [sum_div]
      apply sum_congr rfl
      intro r _
      simp only [μ, W, Fintype.sum_bool, Bool.false_eq_true, ↓reduceIte, sum_add_distrib]
      ring
    rw [he]
    ring
  have hh := centered_signed_product_lower_bound m L hm hL μ P W
    hμ hμsum hPsum hcenter hWtail hcover hC
  rw [hE,hA,hB] at hh
  exact hh
end SignedCorrelationBarrier


namespace Submissions.Erdos30SignedSmoothingBarrier.Savcab
open Finset
 theorem proof : ∀ (R m L : ℕ), 0 < m → 0 < L →
    ∀ (lam : Fin R → ℝ) (p wLeft wRight : Fin R → ℕ → ℝ),
    (∀ r, 0 ≤ lam r) → (∑ r, lam r = 1) →
    (∀ r, ∑ i ∈ range m, p r i = 1) →
    (∀ d < m, 0 ≤ ∑ r, lam r *
      ∑ i ∈ range (m-(d+1)), p r (i+d+1)*p r i) →
    (∀ r j, L*m ≤ j → wLeft r j = 1) →
    (∀ r j, L*m ≤ j → wRight r j = 1) →
    (∀ q ≤ L*m, 1 ≤ ∑ r, lam r * ∑ i ∈ range m, p r i*wLeft r (q+i)) →
    (∀ q ≤ L*m, 1 ≤ ∑ r, lam r * ∑ i ∈ range m, p r (m-1-i)*wRight r (q+i)) →
    (3:ℝ)/4 + (∑ r, lam r * ∑ i ∈ range m, p r i^2)^2/4 ≤
      ((m:ℝ) * ∑ r, lam r * ∑ i ∈ range m, p r i^2) *
      (1 + (∑ r, lam r * ∑ j ∈ range (L*m),
        (wLeft r j^2+wRight r j^2))/(m:ℝ) - 2*L) := by
  intro R m L hm hL lam p wLeft wRight hlam_nonneg hlam hmass hcor hwl hwr hcl hcr
  exact SignedCorrelationBarrier.asymmetric_signed_product_lower_bound m L hm hL
    lam p wLeft wRight hlam_nonneg hlam hmass hcor hwl hwr hcl hcr
end Submissions.Erdos30SignedSmoothingBarrier.Savcab
