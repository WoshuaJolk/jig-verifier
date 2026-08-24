import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Star.Basic
import Mathlib.LinearAlgebra.LinearIndependent.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Dimension.OrzechProperty
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Algebra.Star.BigOperators
import Mathlib.Tactic

namespace Submissions.SeedLocalObstruction.Obstruction

open scoped BigOperators
open Finset

noncomputable section

def pair {k : ℕ} (x y : Fin k → ℂ) : ℂ := ∑ r, star (x r) * y r

def Tight {k m : ℕ} (v : Fin m → Fin k → ℂ) : Prop :=
  ∀ S : Finset (Fin m), S.card + 1 ≤ k →
    LinearIndependent ℂ fun i : (S : Set (Fin m)) => v i

lemma pair_add_left {k : ℕ} (x z y : Fin k → ℂ) :
    pair (x + z) y = pair x y + pair z y := by
  simp [pair, add_mul, Finset.sum_add_distrib]

lemma pair_smul_left {k : ℕ} (c : ℂ) (x y : Fin k → ℂ) :
    pair (c • x) y = star c * pair x y := by
  unfold pair
  simp only [Pi.smul_apply, smul_eq_mul, star_mul]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  ring

lemma pair_add_right {k : ℕ} (x y z : Fin k → ℂ) :
    pair x (y + z) = pair x y + pair x z := by
  simp [pair, mul_add, Finset.sum_add_distrib]

lemma pair_smul_right {k : ℕ} (c : ℂ) (x y : Fin k → ℂ) :
    pair x (c • y) = c * pair x y := by
  unfold pair
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  ring

lemma pair_star {k : ℕ} (x y : Fin k → ℂ) : star (pair x y) = pair y x := by
  unfold pair
  rw [star_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [star_mul, star_star, mul_comm]

lemma pair_sum_left {n k : ℕ} (c : Fin n → ℂ) (x : Fin n → Fin k → ℂ)
    (y : Fin k → ℂ) :
    pair (∑ i, c i • x i) y = ∑ i, star (c i) * pair (x i) y := by
  have h : ∀ s : Finset (Fin n),
      pair (∑ i ∈ s, c i • x i) y = ∑ i ∈ s, star (c i) * pair (x i) y := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp [pair]
    | insert i s hi ih =>
        rw [sum_insert hi, sum_insert hi, pair_add_left, pair_smul_left, ih]
  simpa using h univ

lemma pair_self_ne_zero {k : ℕ} {x : Fin k → ℂ} (hx : x ≠ 0) : pair x x ≠ 0 := by
  obtain ⟨r₀, hr₀⟩ : ∃ r, x r ≠ 0 := by
    by_contra hc
    push Not at hc
    exact hx (funext hc)
  have key : ∀ r : Fin k, star (x r) * x r = ((‖x r‖ ^ 2 : ℝ) : ℂ) := by
    intro r
    have h := Complex.conj_mul' (x r)
    simpa [Complex.star_def] using h
  have hsum : pair x x = ((∑ r, ‖x r‖ ^ 2 : ℝ) : ℂ) := by
    rw [pair, Complex.ofReal_sum]
    exact Finset.sum_congr rfl (fun r _ => key r)
  rw [hsum]
  simp only [ne_eq, Complex.ofReal_eq_zero]
  intro hzero
  have hall := (Finset.sum_eq_zero_iff_of_nonneg
    (fun r (_ : r ∈ Finset.univ) => sq_nonneg ‖x r‖)).1 hzero
  have hn : ‖x r₀‖ = 0 := by
    have h2 := hall r₀ (Finset.mem_univ r₀)
    nlinarith [norm_nonneg (x r₀)]
  exact hr₀ (norm_eq_zero.1 hn)

lemma pair_self_eq_zero {k : ℕ} {x : Fin k → ℂ} (h : pair x x = 0) : x = 0 := by
  by_contra hx
  exact pair_self_ne_zero hx h

def orthMap {n k : ℕ} (x : Fin n → Fin k → ℂ) :
    (Fin k → ℂ) →ₗ[ℂ] (Fin n → ℂ) :=
  LinearMap.pi fun i =>
    { toFun := fun y => pair (x i) y
      map_add' := fun y z => pair_add_right (x i) y z
      map_smul' := fun c y => by
        simp [pair_smul_right, RingHom.id_apply] }

lemma orthMap_apply {n k : ℕ} (x : Fin n → Fin k → ℂ) (y : Fin k → ℂ) (i : Fin n) :
    orthMap x y i = pair (x i) y := rfl

theorem proof :
    ∀ (k m : ℕ) (v : Fin m → Fin k → ℂ),
      2 ≤ k →
      Tight v →
      ∀ j : ℕ, 2 ≤ j → j + 1 ≤ k →
        ∀ T : Finset (Fin m), T.card = j →
          ¬ ∃ U : Finset (Fin m),
              U.card = k + 1 - j ∧
              ∀ u ∈ U, ∀ t ∈ T, pair (v u) (v t) = 0 := by
  intro k m v hk htight j hj2 hjk T hTcard
  rintro ⟨U, hUcard, hUorth⟩
  have hTcard' : T.card + 1 ≤ k := by omega
  have hUcard' : U.card + 1 ≤ k := by omega
  have hTli : LinearIndependent ℂ (fun i : (T : Set (Fin m)) => v i) :=
    htight T hTcard'
  have hUli : LinearIndependent ℂ (fun i : (U : Set (Fin m)) => v i) :=
    htight U hUcard'
  let eT := T.orderIsoOfFin hTcard
  let nU := k + 1 - j
  let eU := U.orderIsoOfFin hUcard
  have hTli' : LinearIndependent ℂ (fun i : Fin j => v (eT i)) :=
    hTli.comp (fun i => (eT i : (T : Set (Fin m)))) eT.injective
  have hUli' : LinearIndependent ℂ (fun i : Fin nU => v (eU i)) :=
    hUli.comp (fun i => (eU i : (U : Set (Fin m)))) eU.injective
  let xT : Fin j → Fin k → ℂ := fun i => v (eT i)
  let φ := orthMap xT
  have hTspan :
      Module.finrank ℂ (Submodule.span ℂ (Set.range xT)) = j := by
    have h := (linearIndependent_iff_card_eq_finrank_span (R := ℂ) (b := xT)).mp hTli'
    simpa [Fintype.card_fin, Set.finrank] using h.symm
  have hUspan :
      Module.finrank ℂ
        (Submodule.span ℂ (Set.range fun i : Fin nU => v (eU i))) = nU := by
    have h := (linearIndependent_iff_card_eq_finrank_span (R := ℂ)
      (b := fun i : Fin nU => v (eU i))).mp hUli'
    simpa [Fintype.card_fin, Set.finrank] using h.symm
  have hUker : ∀ i : Fin nU, φ (v (eU i)) = 0 := by
    intro i
    ext t
    have ht : (eT t : Fin m) ∈ T := (eT t).property
    have hu : (eU i : Fin m) ∈ U := (eU i).property
    have hvu : pair (v (eU i)) (v (eT t)) = 0 := hUorth _ hu _ ht
    have : pair (v (eT t)) (v (eU i)) = 0 := by
      have h := pair_star (v (eU i)) (v (eT t))
      simpa [hvu] using h.symm
    simpa [φ, orthMap_apply, xT] using this
  have hspanU_le_ker :
      Submodule.span ℂ (Set.range fun i : Fin nU => v (eU i)) ≤ LinearMap.ker φ := by
    intro w hw
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hw
    rw [LinearMap.mem_ker]
    have hmap : φ (∑ i, c i • v (eU i)) = ∑ i, c i • φ (v (eU i)) := by
      simp [map_sum, map_smul]
    rw [hmap]
    simp [hUker]
  have hUle : nU ≤ Module.finrank ℂ (LinearMap.ker φ) := by
    have hmono := Submodule.finrank_mono hspanU_le_ker
    exact hUspan.symm.trans_le hmono
  have hinf :
      Submodule.span ℂ (Set.range xT) ⊓ LinearMap.ker φ = ⊥ := by
    ext w
    constructor
    · intro hw
      have hwspan : w ∈ Submodule.span ℂ (Set.range xT) := hw.1
      have hwker : w ∈ LinearMap.ker φ := hw.2
      obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hwspan
      have hφ0 : φ (∑ i, c i • xT i) = 0 := LinearMap.mem_ker.mp hwker
      have horth : ∀ i : Fin j, pair (xT i) (∑ t, c t • xT t) = 0 := by
        intro i
        have hi := congrArg (fun f : Fin j → ℂ => f i) hφ0
        simpa [φ, orthMap_apply] using hi
      have hself : pair (∑ i, c i • xT i) (∑ t, c t • xT t) = 0 := by
        rw [pair_sum_left]
        refine Finset.sum_eq_zero fun i _ => ?_
        simp [horth]
      exact pair_self_eq_zero hself
    · intro hw
      rw [Submodule.mem_bot] at hw
      subst hw
      exact ⟨Submodule.zero_mem _, LinearMap.mem_ker.mpr (map_zero φ)⟩
  have hsumle :
      Module.finrank ℂ (Submodule.span ℂ (Set.range xT)) +
        Module.finrank ℂ (LinearMap.ker φ)
        ≤ Module.finrank ℂ (Fin k → ℂ) := by
    have h := Submodule.finrank_sup_add_finrank_inf_eq
      (Submodule.span ℂ (Set.range xT)) (LinearMap.ker φ)
    have hinf0 : Module.finrank ℂ
        (Submodule.span ℂ (Set.range xT) ⊓ LinearMap.ker φ :
          Submodule ℂ (Fin k → ℂ)) = 0 := by
      rw [hinf, finrank_bot]
    have hsuple : Module.finrank ℂ
        (Submodule.span ℂ (Set.range xT) ⊔ LinearMap.ker φ :
          Submodule ℂ (Fin k → ℂ))
          ≤ Module.finrank ℂ (Fin k → ℂ) := Submodule.finrank_le _
    omega
  have hV : Module.finrank ℂ (Fin k → ℂ) = k := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
  have hjnUle : j + nU ≤ k := by
    have hsum' := hsumle
    rw [hTspan, hV] at hsum'
    have hkerle : Module.finrank ℂ (LinearMap.ker φ) ≤ k - j := by omega
    have : nU ≤ k - j := le_trans hUle hkerle
    omega
  have hjnUeq : j + nU = k + 1 := by
    dsimp [nU]
    omega
  omega

end

end Submissions.SeedLocalObstruction.Obstruction
