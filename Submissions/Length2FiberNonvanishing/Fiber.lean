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

namespace Submissions.Length2FiberNonvanishing.Fiber

open scoped BigOperators
open Finset

noncomputable section

def pair {k : ℕ} (x y : Fin k → ℂ) : ℂ := ∑ r, star (x r) * y r

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

lemma pair_neg_right {k : ℕ} (x y : Fin k → ℂ) :
    pair x (-y) = - pair x y := by
  have h := pair_smul_right (c := (-1 : ℂ)) x y
  simpa [neg_one_smul] using h

lemma pair_sub_right {k : ℕ} (x y z : Fin k → ℂ) :
    pair x (y - z) = pair x y - pair x z := by
  rw [sub_eq_add_neg, pair_add_right, pair_neg_right, sub_eq_add_neg]

lemma pair_star {k : ℕ} (x y : Fin k → ℂ) : star (pair x y) = pair y x := by
  unfold pair
  rw [star_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [star_mul, star_star, mul_comm]

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

def pairRight {k : ℕ} (r : Fin k → ℂ) : (Fin k → ℂ) →ₗ[ℂ] ℂ where
  toFun y := pair r y
  map_add' y z := pair_add_right r y z
  map_smul' c y := by simp [pair_smul_right, RingHom.id_apply]

lemma pairRight_apply {k : ℕ} (r y : Fin k → ℂ) : pairRight r y = pair r y := rfl

lemma pairRight_surjective {k : ℕ} {r : Fin k → ℂ} (hr : r ≠ 0) :
    Function.Surjective (pairRight r) := by
  intro c
  refine ⟨(c / pair r r) • r, ?_⟩
  have hrr : pair r r ≠ 0 := pair_self_ne_zero hr
  simp [pairRight_apply, div_mul_cancel₀ _ hrr]

lemma finrank_range_pairRight {k : ℕ} {r : Fin k → ℂ} (hr : r ≠ 0) :
    Module.finrank ℂ (LinearMap.range (pairRight r)) = 1 := by
  rw [LinearMap.range_eq_top.2 (pairRight_surjective hr), finrank_top]
  exact Module.finrank_self ℂ

lemma finrank_ker_pairRight {k : ℕ} {r : Fin k → ℂ} (hr : r ≠ 0) :
    Module.finrank ℂ (LinearMap.ker (pairRight r)) = k - 1 := by
  have hν := LinearMap.finrank_range_add_finrank_ker (pairRight r)
  have hV : Module.finrank ℂ (Fin k → ℂ) = k := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
  have hrng := finrank_range_pairRight hr
  have : 1 + Module.finrank ℂ (LinearMap.ker (pairRight r)) = k := by
    simpa [hV, hrng] using hν
  omega

lemma finrank_ker_pairRight_four {r : Fin 4 → ℂ} (hr : r ≠ 0) :
    Module.finrank ℂ (LinearMap.ker (pairRight r)) = 3 := by
  simpa using finrank_ker_pairRight (k := 4) hr

lemma range3
    {p q r : Fin 4 → ℂ} :
    (Set.range fun i : Fin 3 => (![p, q, r] : Fin 3 → Fin 4 → ℂ) i) =
      ({p, q, r} : Set (Fin 4 → ℂ)) := by
  ext x
  constructor
  · rintro ⟨i, rfl⟩
    fin_cases i <;> simp
  · intro hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with h | h | h
    · exact ⟨0, h.symm ▸ rfl⟩
    · exact ⟨1, h.symm ▸ rfl⟩
    · exact ⟨2, h.symm ▸ rfl⟩

lemma range4
    {b p q r : Fin 4 → ℂ} :
    (Set.range fun i : Fin 4 => (![b, p, q, r] : Fin 4 → Fin 4 → ℂ) i) =
      ({b, p, q, r} : Set (Fin 4 → ℂ)) := by
  ext x
  constructor
  · rintro ⟨i, rfl⟩
    fin_cases i <;> simp
  · intro hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with h | h | h | h
    · exact ⟨0, h.symm ▸ rfl⟩
    · exact ⟨1, h.symm ▸ rfl⟩
    · exact ⟨2, h.symm ▸ rfl⟩
    · exact ⟨3, h.symm ▸ rfl⟩

lemma finrank_span3
    {p q r : Fin 4 → ℂ} (hli : LinearIndependent ℂ ![p, q, r]) :
    Module.finrank ℂ (Submodule.span ℂ ({p, q, r} : Set (Fin 4 → ℂ))) = 3 := by
  have h := (linearIndependent_iff_card_eq_finrank_span (R := ℂ)
    (b := fun i : Fin 3 => (![p, q, r] : Fin 3 → Fin 4 → ℂ) i)).mp hli
  have h' : Set.finrank ℂ
      (Set.range fun i : Fin 3 => (![p, q, r] : Fin 3 → Fin 4 → ℂ) i) = 3 := by
    simpa [Fintype.card_fin] using h.symm
  rw [range3, Set.finrank] at h'
  exact h'

lemma finrank_span4
    {b p q r : Fin 4 → ℂ} (hli : LinearIndependent ℂ ![b, p, q, r]) :
    Module.finrank ℂ (Submodule.span ℂ ({b, p, q, r} : Set (Fin 4 → ℂ))) = 4 := by
  have h := (linearIndependent_iff_card_eq_finrank_span (R := ℂ)
    (b := fun i : Fin 4 => (![b, p, q, r] : Fin 4 → Fin 4 → ℂ) i)).mp hli
  have h' : Set.finrank ℂ
      (Set.range fun i : Fin 4 => (![b, p, q, r] : Fin 4 → Fin 4 → ℂ) i) = 4 := by
    simpa [Fintype.card_fin] using h.symm
  rw [range4, Set.finrank] at h'
  exact h'

lemma li4_of_not_mem
    {b p q r : Fin 4 → ℂ}
    (h3 : LinearIndependent ℂ ![p, q, r])
    (hb : b ∉ Submodule.span ℂ ({p, q, r} : Set (Fin 4 → ℂ))) :
    LinearIndependent ℂ ![b, p, q, r] := by
  rw [Fintype.linearIndependent_iff] at h3 ⊢
  intro h hh
  have hsum :
      h 0 • b + h 1 • p + h 2 • q + h 3 • r = 0 := by
    simpa [Fin.sum_univ_four, Pi.add_apply, Pi.smul_apply] using hh
  intro i
  by_cases h0 : h 0 = 0
  · have h3sum : h 1 • p + h 2 • q + h 3 • r = 0 := by
      simpa [h0] using hsum
    let g : Fin 3 → ℂ := ![h 1, h 2, h 3]
    have hg : ∑ j : Fin 3, g j • (![p, q, r] : Fin 3 → Fin 4 → ℂ) j = 0 := by
      simp [g, Fin.sum_univ_three, h3sum]
    have hg0 := h3 g hg
    fin_cases i
    · exact h0
    · simpa [g] using hg0 0
    · simpa [g] using hg0 1
    · simpa [g] using hg0 2
  · have hbmem : b ∈ Submodule.span ℂ ({p, q, r} : Set (Fin 4 → ℂ)) := by
      let U := Submodule.span ℂ ({p, q, r} : Set (Fin 4 → ℂ))
      have hpU : p ∈ U := Submodule.subset_span (by simp : p ∈ ({p, q, r} : Set _))
      have hqU : q ∈ U := Submodule.subset_span (by simp : q ∈ ({p, q, r} : Set _))
      have hrU : r ∈ U := Submodule.subset_span (by simp : r ∈ ({p, q, r} : Set _))
      have hcomb : h 0 • b ∈ U := by
        have hsum' : h 0 • b + (h 1 • p + h 2 • q + h 3 • r) = 0 := by
          convert hsum using 1
          abel
        have : h 0 • b = -(h 1 • p) + -(h 2 • q) + -(h 3 • r) := by
          have hneg := eq_neg_of_add_eq_zero_left hsum'
          rw [neg_add, neg_add] at hneg
          exact hneg
        rw [this]
        exact add_mem
          (add_mem
            (neg_mem (U.smul_mem (h 1) hpU))
            (neg_mem (U.smul_mem (h 2) hqU)))
          (neg_mem (U.smul_mem (h 3) hrU))
      have := Submodule.smul_mem U (h 0)⁻¹ hcomb
      rwa [smul_smul, inv_mul_cancel₀ h0, one_smul] at this
    exact (hb hbmem).elim

lemma decompose_nperp
    {r n y : Fin 4 → ℂ}
    (hr : r ≠ 0) (hnr : pair n r = 0) (hny : pair n y = 0) :
    let α := pair r y / pair r r
    pair r (y - α • r) = 0 ∧ pair n (y - α • r) = 0 := by
  intro α
  have hrr : pair r r ≠ 0 := pair_self_ne_zero hr
  constructor
  · have : pair r (y - α • r) = pair r y - α * pair r r := by
      simp [pair_sub_right, pair_smul_right]
    rw [this]
    simp [α, div_mul_cancel₀ _ hrr]
  · have : pair n (y - α • r) = pair n y - α * pair n r := by
      simp [pair_sub_right, pair_smul_right]
    rw [this, hny, hnr]
    ring

lemma ker_le_of_fiber_le
    {r n : Fin 4 → ℂ}
    {U : Submodule ℂ (Fin 4 → ℂ)}
    (hr : r ≠ 0) (hnr : pair n r = 0)
    (hrU : r ∈ U)
    (hW : LinearMap.ker (pairRight r) ⊓ LinearMap.ker (pairRight n) ≤ U) :
    LinearMap.ker (pairRight n) ≤ U := by
  intro y hy
  have hny : pair n y = 0 := by
    simpa [pairRight_apply] using LinearMap.mem_ker.mp hy
  have hdec := decompose_nperp (r := r) (n := n) (y := y) hr hnr hny
  set α := pair r y / pair r r
  have hy'ker :
      y - α • r ∈ LinearMap.ker (pairRight r) ⊓ LinearMap.ker (pairRight n) := by
    refine Submodule.mem_inf.2 ?_
    constructor
    · rw [LinearMap.mem_ker, pairRight_apply]; exact hdec.1
    · rw [LinearMap.mem_ker, pairRight_apply]; exact hdec.2
  have hy'U : y - α • r ∈ U := hW hy'ker
  have : y = (y - α • r) + α • r := by abel
  rw [this]
  exact add_mem hy'U (Submodule.smul_mem _ _ hrU)

theorem proof :
    ∀ (r n p q : Fin 4 → ℂ),
      LinearIndependent ℂ ![r, n] →
      pair r n = 0 →
      LinearIndependent ℂ ![p, q, r] →
      ((∃ b : Fin 4 → ℂ,
          pair r b = 0 ∧ pair n b = 0 ∧ LinearIndependent ℂ ![b, p, q, r]) ↔
        ¬ (pair n p = 0 ∧ pair n q = 0)) := by
  intro r n p q hli_rn hrn hli_pqr
  have hr : r ≠ 0 := hli_rn.ne_zero 0
  have hn : n ≠ 0 := hli_rn.ne_zero 1
  have hnr : pair n r = 0 := by
    have h := pair_star r n
    simpa [hrn] using h.symm
  let U : Submodule ℂ (Fin 4 → ℂ) := Submodule.span ℂ ({p, q, r} : Set (Fin 4 → ℂ))
  have hU3 : Module.finrank ℂ U = 3 := finrank_span3 hli_pqr
  have hker3 : Module.finrank ℂ (LinearMap.ker (pairRight n)) = 3 :=
    finrank_ker_pairRight_four hn
  have hrU : r ∈ U := Submodule.subset_span (by simp : r ∈ ({p, q, r} : Set _))
  constructor
  · rintro ⟨b, hrb, hnb, hli4⟩ hboth
    obtain ⟨hnp, hnq⟩ := hboth
    have hbK : b ∈ LinearMap.ker (pairRight n) := by
      rw [LinearMap.mem_ker, pairRight_apply]; exact hnb
    have hpK : p ∈ LinearMap.ker (pairRight n) := by
      rw [LinearMap.mem_ker, pairRight_apply]; exact hnp
    have hqK : q ∈ LinearMap.ker (pairRight n) := by
      rw [LinearMap.mem_ker, pairRight_apply]; exact hnq
    have hrK : r ∈ LinearMap.ker (pairRight n) := by
      rw [LinearMap.mem_ker, pairRight_apply]; exact hnr
    have hspan_le :
        Submodule.span ℂ ({b, p, q, r} : Set (Fin 4 → ℂ)) ≤
          LinearMap.ker (pairRight n) := by
      rw [Submodule.span_le]
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact hbK
      · exact hpK
      · exact hqK
      · exact hrK
    have hspan4 := finrank_span4 hli4
    have hle : 4 ≤ 3 := by
      have := Submodule.finrank_mono hspan_le
      simpa [hspan4, hker3] using this
    omega
  · intro hnot
    by_contra hnone
    have hWle : LinearMap.ker (pairRight r) ⊓ LinearMap.ker (pairRight n) ≤ U := by
      intro b hb
      have hrb : pair r b = 0 := by
        have := (Submodule.mem_inf.mp hb).1
        simpa [pairRight_apply] using LinearMap.mem_ker.mp this
      have hnb : pair n b = 0 := by
        have := (Submodule.mem_inf.mp hb).2
        simpa [pairRight_apply] using LinearMap.mem_ker.mp this
      by_contra hbU
      have hli4 := li4_of_not_mem hli_pqr hbU
      exact hnone ⟨b, hrb, hnb, hli4⟩
    have hker_le := ker_le_of_fiber_le hr hnr hrU hWle
    have heq : LinearMap.ker (pairRight n) = U :=
      Submodule.eq_of_le_of_finrank_eq hker_le (hker3.trans hU3.symm)
    have hpK : p ∈ LinearMap.ker (pairRight n) := by
      rw [heq]
      exact Submodule.subset_span (by simp : p ∈ ({p, q, r} : Set _))
    have hqK : q ∈ LinearMap.ker (pairRight n) := by
      rw [heq]
      exact Submodule.subset_span (by simp : q ∈ ({p, q, r} : Set _))
    have hnp : pair n p = 0 := by
      simpa [pairRight_apply] using LinearMap.mem_ker.mp hpK
    have hnq : pair n q = 0 := by
      simpa [pairRight_apply] using LinearMap.mem_ker.mp hqK
    exact hnot ⟨hnp, hnq⟩

end

end Submissions.Length2FiberNonvanishing.Fiber
