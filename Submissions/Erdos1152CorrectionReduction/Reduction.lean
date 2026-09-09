import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Topology.ContinuousOn

open Polynomial Filter MeasureTheory
open scoped Topology

namespace Submissions.Erdos1152CorrectionReduction.Reduction


lemma interpolation_normal_form {n : ℕ} (nodes values : Fin n → ℝ)
    (hinj : Function.Injective nodes) (p : ℝ[X]) :
    (∀ i, p.eval (nodes i) = values i) ↔
      ∃ q : ℝ[X], p = Lagrange.interpolate Finset.univ nodes values +
        Lagrange.nodal Finset.univ nodes * q := by
  classical
  have hnodes : Set.InjOn nodes (Finset.univ : Finset (Fin n)) :=
    fun _ _ _ _ h => hinj h
  constructor
  · intro hp
    have hrem : p %ₘ Lagrange.nodal Finset.univ nodes =
        Lagrange.interpolate Finset.univ nodes values := by
      apply Lagrange.eq_interpolate_of_eval_eq values hnodes
      · simpa using degree_modByMonic_lt p
          (Lagrange.nodal_monic (s := Finset.univ) (v := nodes))
      · intro i hi
        rw [modByMonic_eq_sub_mul_div, eval_sub, eval_mul,
          Lagrange.eval_nodal_at_node hi, zero_mul, sub_zero, hp i]
    exact ⟨p /ₘ Lagrange.nodal Finset.univ nodes,
      (modByMonic_add_div p _).symm.trans (by rw [hrem])⟩
  · rintro ⟨q, rfl⟩ i
    rw [eval_add, eval_mul, Lagrange.eval_nodal_at_node (Finset.mem_univ i),
      zero_mul, add_zero, Lagrange.eval_interpolate_at_node values hnodes (Finset.mem_univ i)]

lemma lagrange_natDegree_lt {n : ℕ} (hn : 1 ≤ n) (nodes values : Fin n → ℝ)
    (hinj : Function.Injective nodes) :
    (Lagrange.interpolate Finset.univ nodes values).natDegree < n := by
  classical
  have h := Lagrange.degree_interpolate_lt values
    (show Set.InjOn nodes (Finset.univ : Finset (Fin n)) from fun _ _ _ _ h => hinj h)
  by_cases hz : Lagrange.interpolate Finset.univ nodes values = 0
  · simpa [hz] using (show 0 < n by omega)
  · exact (natDegree_lt_iff_degree_lt hz).mpr (by simpa using h)

lemma normal_form_degree {n : ℕ} (hn : 1 ≤ n) (nodes values : Fin n → ℝ)
    (hinj : Function.Injective nodes) {q : ℝ[X]} (hq : q ≠ 0) :
    (Lagrange.interpolate Finset.univ nodes values +
      Lagrange.nodal Finset.univ nodes * q).natDegree = n + q.natDegree := by
  have hmul : (Lagrange.nodal Finset.univ nodes * q).natDegree = n + q.natDegree := by
    rw [natDegree_mul (Lagrange.nodal_ne_zero) hq]
    simp
  rw [natDegree_add_eq_right_of_natDegree_lt, hmul]
  rw [hmul]
  exact lt_of_lt_of_le (lagrange_natDegree_lt hn nodes values hinj) (Nat.le_add_right _ _)

theorem normal_form :
    ∀ (n : ℕ), 1 ≤ n → ∀ (nodes values : Fin n → ℝ), Function.Injective nodes →
      ∀ (ε : ℝ), 0 < ε → ∀ p : ℝ[X],
        (((p.natDegree : ℝ) < (1 + ε) * n) ∧ ∀ i, p.eval (nodes i) = values i) ↔
          ∃ q : ℝ[X], p = Lagrange.interpolate Finset.univ nodes values +
            Lagrange.nodal Finset.univ nodes * q ∧ (q.natDegree : ℝ) < ε * n := by
  intro n hn nodes values hinj ε hε p
  have hnreal : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  constructor
  · rintro ⟨hdeg, hval⟩
    obtain ⟨q, rfl⟩ := (interpolation_normal_form nodes values hinj p).mp hval
    refine ⟨q, rfl, ?_⟩
    by_cases hq : q = 0
    · simp only [hq, natDegree_zero, Nat.cast_zero]
      exact mul_pos hε hnreal
    · rw [normal_form_degree hn nodes values hinj hq, Nat.cast_add] at hdeg
      nlinarith
  · rintro ⟨q, rfl, hdeg⟩
    refine ⟨?_, (interpolation_normal_form nodes values hinj _).mpr ⟨q, rfl⟩⟩
    by_cases hz : q = 0
    · simp only [hz, mul_zero, add_zero]
      have hsmall : ((Lagrange.interpolate Finset.univ nodes values).natDegree : ℝ) < n :=
        Nat.cast_lt.mpr (lagrange_natDegree_lt hn nodes values hinj)
      nlinarith
    · rw [normal_form_degree hn nodes values hinj hz, Nat.cast_add]
      nlinarith



def AdmissibleNodes (nodes : ∀ n : ℕ, Fin n → ℝ) : Prop :=
  (∀ n i, nodes n i ∈ Set.Icc (-1 : ℝ) 1) ∧
    ∀ n, Function.Injective (nodes n)

def InterpolatesWithin
    (nodes : ∀ n : ℕ, Fin n → ℝ)
    (surplus : ℕ → ℝ) (f : ℝ → ℝ)
    (p : ℕ → ℝ[X]) : Prop :=
  ∀ n : ℕ, 1 ≤ n →
    ((p n).natDegree : ℝ) < (1 + surplus n) * n ∧
      ∀ i : Fin n, (p n).eval (nodes n i) = f (nodes n i)

abbrev Original : Prop :=
  ∀ nodes : ∀ n : ℕ, Fin n → ℝ,
    AdmissibleNodes nodes →
      ∀ surplus : ℕ → ℝ,
        (∀ n, 0 < surplus n) →
          Tendsto surplus atTop (𝓝 0) →
            ∃ f : ℝ → ℝ,
              ContinuousOn f (Set.Icc (-1 : ℝ) 1) ∧
                ∀ p : ℕ → ℝ[X],
                  InterpolatesWithin nodes surplus f p →
                    ∀ᵐ x ∂volume.restrict (Set.Icc (-1 : ℝ) 1),
                      ¬ Tendsto (fun n ↦ (p n).eval x) atTop (𝓝 (f x))


abbrev CorrectionForm : Prop :=
  ∀ nodes : ∀ n : ℕ, Fin n → ℝ,
    AdmissibleNodes nodes →
      ∀ surplus : ℕ → ℝ,
        (∀ n, 0 < surplus n) →
          Tendsto surplus atTop (𝓝 0) →
            ∃ f : ℝ → ℝ,
              ContinuousOn f (Set.Icc (-1 : ℝ) 1) ∧
                ∀ q : ℕ → ℝ[X],
                  (∀ n : ℕ, 1 ≤ n → ((q n).natDegree : ℝ) < surplus n * n) →
                    ∀ᵐ x ∂volume.restrict (Set.Icc (-1 : ℝ) 1),
                      ¬ Tendsto (fun n ↦
                        (Lagrange.interpolate Finset.univ (nodes n) (fun i ↦ f (nodes n i))).eval x +
                          (Lagrange.nodal Finset.univ (nodes n)).eval x * (q n).eval x)
                        atTop (𝓝 (f x))

theorem proof : Original ↔ CorrectionForm := by
  constructor
  · intro horig nodes hnodes surplus hpos hlim
    obtain ⟨f, hf, hbad⟩ := horig nodes hnodes surplus hpos hlim
    refine ⟨f, hf, ?_⟩
    intro q hq
    let p : ℕ → ℝ[X] := fun n ↦
      Lagrange.interpolate Finset.univ (nodes n) (fun i ↦ f (nodes n i)) +
        Lagrange.nodal Finset.univ (nodes n) * q n
    have hp : InterpolatesWithin nodes surplus f p := by
      intro n hn
      exact (normal_form n hn (nodes n) (fun i ↦ f (nodes n i))
        (hnodes.2 n) (surplus n) (hpos n) (p n)).mpr ⟨q n, rfl, hq n hn⟩
    simpa only [p, eval_add, eval_mul] using hbad p hp
  · intro hcorrect nodes hnodes surplus hpos hlim
    obtain ⟨f, hf, hbad⟩ := hcorrect nodes hnodes surplus hpos hlim
    refine ⟨f, hf, ?_⟩
    intro p hp
    have hex : ∀ n : ℕ, ∃ q : ℝ[X], 1 ≤ n →
        p n = Lagrange.interpolate Finset.univ (nodes n) (fun i ↦ f (nodes n i)) +
          Lagrange.nodal Finset.univ (nodes n) * q ∧ (q.natDegree : ℝ) < surplus n * n := by
      intro n
      by_cases hn : 1 ≤ n
      · obtain ⟨q, heq, hdeg⟩ := (normal_form n hn (nodes n) (fun i ↦ f (nodes n i))
          (hnodes.2 n) (surplus n) (hpos n) (p n)).mp (hp n hn)
        exact ⟨q, fun _ ↦ ⟨heq, hdeg⟩⟩
      · exact ⟨0, fun h ↦ (hn h).elim⟩
    choose q hq using hex
    filter_upwards [hbad q (fun n hn ↦ (hq n hn).2)] with x hx
    intro hconv
    apply hx
    apply hconv.congr'
    filter_upwards [eventually_ge_atTop 1] with n hn
    rw [(hq n hn).1, eval_add, eval_mul]

end Submissions.Erdos1152CorrectionReduction.Reduction
