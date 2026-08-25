import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Geometry.Euclidean.Basic
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Tactic

open Set Metric

namespace Submissions.Erdos99OptimalThreePointCase.Worker03Equilateral

abbrev Plane := EuclideanSpace ℝ (Fin 2)

def HasMinDist1 (A : Finset Plane) : Prop :=
  (∀ p ∈ A, ∀ q ∈ A, p ≠ q → dist p q ≥ 1) ∧
  (∃ p ∈ A, ∃ q ∈ A, dist p q = 1)

def FormsEquilateralTriangle (p q r : Plane) : Prop :=
  dist p q = 1 ∧ dist q r = 1 ∧ dist p r = 1

noncomputable section

private abbrev p₀ : Plane := !₂[(0 : ℝ), 0]
private abbrev p₁ : Plane := !₂[(1 : ℝ), 0]
private abbrev p₂ : Plane := !₂[(1 : ℝ) / 2, Real.sqrt 3 / 2]

private def E : Finset Plane := {p₀, p₁, p₂}

private lemma eucl_dist_one_of_sq {x y : Plane} (h : dist x y ^ 2 = 1) :
    dist x y = 1 := by
  nlinarith [dist_nonneg (x := x) (y := y), sq_nonneg (dist x y)]

private lemma hd01 : dist p₀ p₁ = 1 := eucl_dist_one_of_sq <| by
  rw [EuclideanSpace.dist_sq_eq, Fin.sum_univ_two]
  simp [Real.dist_eq]

private lemma hd02 : dist p₀ p₂ = 1 := eucl_dist_one_of_sq <| by
  rw [EuclideanSpace.dist_sq_eq, Fin.sum_univ_two, Real.dist_eq, Real.dist_eq]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  nlinarith [Real.sq_sqrt (show (3 : ℝ) ≥ 0 by norm_num), Real.sqrt_nonneg 3,
    sq_abs ((0 : ℝ) - 1 / 2), sq_abs ((0 : ℝ) - Real.sqrt 3 / 2)]

private lemma hd12 : dist p₁ p₂ = 1 := eucl_dist_one_of_sq <| by
  rw [EuclideanSpace.dist_sq_eq, Fin.sum_univ_two, Real.dist_eq, Real.dist_eq]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  nlinarith [Real.sq_sqrt (show (3 : ℝ) ≥ 0 by norm_num), Real.sqrt_nonneg 3,
    sq_abs ((1 : ℝ) - 1 / 2), sq_abs ((0 : ℝ) - Real.sqrt 3 / 2)]

private lemma E_card : E.card = 3 := by
  simp [E, p₀, p₁, p₂]

private lemma E_minDist : HasMinDist1 E := by
  constructor
  · intro p hp q hq hpq
    simp only [E, Finset.mem_insert, Finset.mem_singleton] at hp hq
    rcases hp with rfl | rfl | rfl <;>
      rcases hq with rfl | rfl | rfl <;>
      simp_all [hd01, hd02, hd12, dist_comm]
  · exact ⟨p₀, by simp [E], p₁, by simp [E], hd01⟩

private lemma E_diam : diam (E : Set Plane) = 1 := by
  simp only [E, Finset.coe_insert, Finset.coe_singleton]
  rw [Metric.diam_triple, hd01, hd02, hd12]
  norm_num

private lemma diameter_one_rigidity (A : Finset Plane) (hcard : 3 ≤ A.card)
    (hmin : HasMinDist1 A) (hdiam : diam (A : Set Plane) ≤ 1) :
    ∃ p ∈ A, ∃ q ∈ A, ∃ r ∈ A, FormsEquilateralTriangle p q r := by
  have hthree : 2 < A.card := by omega
  rcases Finset.two_lt_card.mp hthree with
    ⟨p, hp, q, hq, r, hr, hpq, hpr, hqr⟩
  have upper (x : Plane) (hx : x ∈ A) (y : Plane) (hy : y ∈ A) :
      dist x y ≤ 1 :=
    (Metric.dist_le_diam_of_mem A.finite_toSet.isBounded hx hy).trans hdiam
  have hpq1 : dist p q = 1 :=
    le_antisymm (upper p hp q hq) (hmin.1 p hp q hq hpq)
  have hqr1 : dist q r = 1 :=
    le_antisymm (upper q hq r hr) (hmin.1 q hq r hr hqr)
  have hpr1 : dist p r = 1 :=
    le_antisymm (upper p hp r hr) (hmin.1 p hp r hr hpr)
  exact ⟨p, hp, q, hq, r, hr, hpq1, hqr1, hpr1⟩

theorem proof :
    ∀ A : Finset Plane, A.card = 3 → HasMinDist1 A →
      IsMinOn (fun B : Finset Plane ↦ diam (B : Set Plane))
        {B : Finset Plane | B.card = 3 ∧ HasMinDist1 B} A →
      ∃ p ∈ A, ∃ q ∈ A, ∃ r ∈ A, FormsEquilateralTriangle p q r := by
  intro A hcard hmin hopt
  have hdiam : diam (A : Set Plane) ≤ 1 := by
    rw [← E_diam]
    exact hopt ⟨E_card, E_minDist⟩
  exact diameter_one_rigidity A (by omega) hmin hdiam

end

end Submissions.Erdos99OptimalThreePointCase.Worker03Equilateral
