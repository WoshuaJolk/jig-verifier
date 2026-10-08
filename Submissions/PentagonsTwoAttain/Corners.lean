import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic

namespace Submissions.PentagonsTwoAttain.Corners

open Real

/-- Circumradius of a regular pentagon with unit side length. -/
noncomputable def circumradius : ℝ := 1 / (2 * Real.sin (Real.pi / 5))

/-- The closed regular pentagon with unit side, centre `(a, b)`, rotated by `θ`. -/
noncomputable def pentagon (a b θ : ℝ) : Set (ℝ × ℝ) :=
  convexHull ℝ (Set.range fun k : Fin 5 =>
    (a + circumradius * Real.cos (θ + 2 * Real.pi * (k : ℕ) / 5),
     b + circumradius * Real.sin (θ + 2 * Real.pi * (k : ℕ) / 5)))

/-- `n` unit regular pentagons, each with arbitrary position and rotation, fit inside the
axis-parallel square `[0, s] × [0, s]` with pairwise disjoint interiors. -/
def PacksInSquare (n : ℕ) (s : ℝ) : Prop :=
  ∃ a b θ : Fin n → ℝ,
    (∀ i, pentagon (a i) (b i) (θ i) ⊆ Set.Icc 0 s ×ˢ Set.Icc 0 s) ∧
    (∀ i j, i ≠ j →
      Disjoint (interior (pentagon (a i) (b i) (θ i)))
        (interior (pentagon (a j) (b j) (θ j))))

/-- Side of the smallest known square for two unit pentagons:
`C (3 + C - 2 C²) / (S (S + C))` with `C = cos (π/5)`, `S = sin (π/5)` (≈ 2.46345). -/
noncomputable def sStar : ℝ :=
  Real.cos (Real.pi / 5) * (3 + Real.cos (Real.pi / 5) - 2 * Real.cos (Real.pi / 5) ^ 2) /
    (Real.sin (Real.pi / 5) * (Real.sin (Real.pi / 5) + Real.cos (Real.pi / 5)))


lemma S_pos : 0 < sin (π / 5) := sin_pos_of_pos_of_lt_pi (by positivity) (by linarith [pi_pos])
lemma C_eq : cos (π / 5) = (1 + √5) / 4 := cos_pi_div_five
lemma C_pos : 0 < cos (π / 5) := by rw [C_eq]; positivity
lemma SC_sq : sin (π / 5) ^ 2 + cos (π / 5) ^ 2 = 1 := sin_sq_add_cos_sq _
lemma R_mul_S : circumradius * sin (π / 5) = 1 / 2 := by
  have := S_pos; unfold circumradius; field_simp
lemma R_pos : 0 < circumradius := by unfold circumradius; have := S_pos; positivity

/-- cos and sin of the vertex angles `π/10 + 2πk/5`, times the circumradius. -/
lemma cos10 : cos (π / 10) = 2 * sin (π / 5) * cos (π / 5) := by
  rw [← sin_pi_div_two_sub, show π / 2 - π / 10 = 2 * (π / 5) by ring, sin_two_mul]
lemma sin10 : sin (π / 10) = 2 * cos (π / 5) ^ 2 - 1 := by
  rw [← cos_pi_div_two_sub, show π / 2 - π / 10 = 2 * (π / 5) by ring, cos_two_mul]
lemma cos310 : cos (3 * π / 10) = sin (π / 5) := by
  rw [← sin_pi_div_two_sub, show π / 2 - 3 * π / 10 = π / 5 by ring]
lemma sin310 : sin (3 * π / 10) = cos (π / 5) := by
  rw [← cos_pi_div_two_sub, show π / 2 - 3 * π / 10 = π / 5 by ring]

lemma vtx (k : ℕ) (hk : k < 5) :
    ∃ X Y : ℝ, circumradius * cos (π / 10 + 2 * π * (k : ℝ) / 5) = X ∧
      circumradius * sin (π / 10 + 2 * π * (k : ℝ) / 5) = Y ∧
      ((X = cos (π / 5) ∧ Y = circumradius * (2 * cos (π / 5) ^ 2 - 1)) ∨
       (X = 0 ∧ Y = circumradius) ∨
       (X = -cos (π / 5) ∧ Y = circumradius * (2 * cos (π / 5) ^ 2 - 1)) ∨
       (X = -(1 / 2) ∧ Y = -(circumradius * cos (π / 5))) ∨
       (X = 1 / 2 ∧ Y = -(circumradius * cos (π / 5)))) := by
  have hRS := R_mul_S
  interval_cases k
  · refine ⟨_, _, rfl, rfl, Or.inl ⟨?_, ?_⟩⟩
    · rw [show π / 10 + 2 * π * ((0:ℕ):ℝ) / 5 = π / 10 by push_cast; ring, cos10]
      linear_combination (2 * cos (π / 5)) * hRS
    · rw [show π / 10 + 2 * π * ((0:ℕ):ℝ) / 5 = π / 10 by push_cast; ring, sin10]
  · refine ⟨_, _, rfl, rfl, Or.inr (Or.inl ⟨?_, ?_⟩)⟩
    · rw [show π / 10 + 2 * π * ((1:ℕ):ℝ) / 5 = π / 2 by push_cast; ring, cos_pi_div_two, mul_zero]
    · rw [show π / 10 + 2 * π * ((1:ℕ):ℝ) / 5 = π / 2 by push_cast; ring, sin_pi_div_two, mul_one]
  · refine ⟨_, _, rfl, rfl, Or.inr (Or.inr (Or.inl ⟨?_, ?_⟩))⟩
    · rw [show π / 10 + 2 * π * ((2:ℕ):ℝ) / 5 = π - π / 10 by push_cast; ring, cos_pi_sub, cos10]
      linear_combination (-2 * cos (π / 5)) * hRS
    · rw [show π / 10 + 2 * π * ((2:ℕ):ℝ) / 5 = π - π / 10 by push_cast; ring, sin_pi_sub, sin10]
  · refine ⟨_, _, rfl, rfl, Or.inr (Or.inr (Or.inr (Or.inl ⟨?_, ?_⟩)))⟩
    · rw [show π / 10 + 2 * π * ((3:ℕ):ℝ) / 5 = 3 * π / 10 + π by push_cast; ring, cos_add_pi, cos310]
      linear_combination -hRS
    · rw [show π / 10 + 2 * π * ((3:ℕ):ℝ) / 5 = 3 * π / 10 + π by push_cast; ring, sin_add_pi, sin310]
      ring
  · refine ⟨_, _, rfl, rfl, Or.inr (Or.inr (Or.inr (Or.inr ⟨?_, ?_⟩)))⟩
    · rw [show π / 10 + 2 * π * ((4:ℕ):ℝ) / 5 = -(3 * π / 10) + 2 * π by push_cast; ring,
        cos_add_two_pi, cos_neg, cos310]
      exact hRS
    · rw [show π / 10 + 2 * π * ((4:ℕ):ℝ) / 5 = -(3 * π / 10) + 2 * π by push_cast; ring,
        sin_add_two_pi, sin_neg, sin310]
      ring

lemma hull_sub {a b θ : ℝ} {T : Set (ℝ × ℝ)} (hT : Convex ℝ T)
    (h : ∀ k : ℕ, k < 5 → (a + circumradius * cos (θ + 2 * π * (k : ℝ) / 5),
      b + circumradius * sin (θ + 2 * π * (k : ℝ) / 5)) ∈ T) :
    pentagon a b θ ⊆ T := by
  apply convexHull_min _ hT
  rintro _ ⟨k, rfl⟩
  exact h k k.isLt

lemma convex_le (n1 n2 c : ℝ) : Convex ℝ {x : ℝ × ℝ | n1 * x.1 + n2 * x.2 ≤ c} := by
  intro x hx y hy t u ht hu htu
  simp only [Set.mem_setOf_eq, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
    smul_eq_mul] at *
  have e : n1 * (t * x.1 + u * y.1) + n2 * (t * x.2 + u * y.2)
      = t * (n1 * x.1 + n2 * x.2) + u * (n1 * y.1 + n2 * y.2) := by ring
  rw [e]
  have hc : t * c + u * c = c := by rw [← add_mul, htu, one_mul]
  linarith [mul_le_mul_of_nonneg_left hx ht, mul_le_mul_of_nonneg_left hy hu]

lemma convex_ge (n1 n2 c : ℝ) : Convex ℝ {x : ℝ × ℝ | c ≤ n1 * x.1 + n2 * x.2} := by
  intro x hx y hy t u ht hu htu
  simp only [Set.mem_setOf_eq, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
    smul_eq_mul] at *
  have e : n1 * (t * x.1 + u * y.1) + n2 * (t * x.2 + u * y.2)
      = t * (n1 * x.1 + n2 * x.2) + u * (n1 * y.1 + n2 * y.2) := by ring
  rw [e]
  have hc : t * c + u * c = c := by rw [← add_mul, htu, one_mul]
  linarith [mul_le_mul_of_nonneg_left hx ht, mul_le_mul_of_nonneg_left hy hu]

/-- Closed half-planes on either side of a line with nonzero normal: interiors are disjoint. -/
lemma halfplane_disjoint {P Q : Set (ℝ × ℝ)} (n1 n2 c : ℝ) (hn : 0 < n1 ^ 2 + n2 ^ 2)
    (hP : P ⊆ {x | n1 * x.1 + n2 * x.2 ≤ c}) (hQ : Q ⊆ {x | c ≤ n1 * x.1 + n2 * x.2}) :
    Disjoint (interior P) (interior Q) := by
  rw [Set.disjoint_left]
  intro x hxP hxQ
  have h1 : n1 * x.1 + n2 * x.2 ≤ c := hP (interior_subset hxP)
  have h2 : c ≤ n1 * x.1 + n2 * x.2 := hQ (interior_subset hxQ)
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp isOpen_interior x hxP
  set δ := ε / (2 * (|n1| + |n2| + 1)) with hδ
  have hδpos : 0 < δ := by positivity
  have hy : (x.1 + δ * n1, x.2 + δ * n2) ∈ Metric.ball x ε := by
    rw [Metric.mem_ball, Prod.dist_eq, Real.dist_eq, Real.dist_eq]
    simp only [add_sub_cancel_left, abs_mul, abs_of_pos hδpos]
    have k1 : δ * |n1| < ε := by
      rw [hδ, div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
      nlinarith [abs_nonneg n1, abs_nonneg n2]
    have k2 : δ * |n2| < ε := by
      rw [hδ, div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
      nlinarith [abs_nonneg n1, abs_nonneg n2]
    exact max_lt k1 k2
  have := hP (interior_subset (hball hy))
  simp only [Set.mem_setOf_eq] at this
  nlinarith [mul_pos hδpos hn]

lemma sStar_eq : sStar * (sin (π / 5) + cos (π / 5)) =
    2 * (sin (π / 5) * cos (π / 5) + (circumradius * cos (π / 5)) * (1 + cos (π / 5))) := by
  have hS := S_pos; have hC := C_pos
  have h1 := SC_sq
  unfold sStar circumradius
  field_simp
  linear_combination (-2) * h1

lemma sStar_ge : 2 * cos (π / 5) ≤ sStar ∧ circumradius * (1 + cos (π / 5)) ≤ sStar := by
  -- numeric: sStar ≈ 2.4635, 2C ≈ 1.618, R(1+C) ≈ 1.539
  have hS := S_pos; have hC := C_pos; have h1 := SC_sq; have hR := R_mul_S
  have hR0 := R_pos
  have e := sStar_eq
  have h5 : (2 : ℝ) < √5 ∧ √5 < 3 := by
    constructor
    · rw [Real.lt_sqrt (by norm_num)]; norm_num
    · rw [Real.sqrt_lt' (by norm_num)]; norm_num
  have hCv := C_eq
  have hSC : 0 < sin (π / 5) + cos (π / 5) := by linarith
  have hS1 : sin (π / 5) < 1 := by nlinarith
  have hCb : 3 / 4 < cos (π / 5) ∧ cos (π / 5) < 1 := by rw [hCv]; constructor <;> linarith
  constructor
  · by_contra hc; push_neg at hc
    have := mul_lt_mul_of_pos_right hc hSC
    nlinarith [mul_pos hS hC, mul_pos hR0 hC]
  · by_contra hc; push_neg at hc
    have := mul_lt_mul_of_pos_right hc hSC
    nlinarith [mul_pos hS hC, mul_pos hR0 hC]

lemma C_gt : 3 / 4 < cos (π / 5) ∧ cos (π / 5) < 1 := by
  rw [C_eq]
  have h1 : (2:ℝ) < √5 := by rw [Real.lt_sqrt (by norm_num)]; norm_num
  have h2 : √5 < 3 := by rw [Real.sqrt_lt' (by norm_num)]; norm_num
  constructor <;> linarith

lemma A_pos : 0 < 2 * cos (π / 5) ^ 2 - 1 := by nlinarith [C_gt.1]

lemma box1 : pentagon (cos (π / 5)) (circumradius * cos (π / 5)) (π / 10) ⊆
    Set.Icc 0 sStar ×ˢ Set.Icc 0 sStar := by
  have hS := S_pos; have hC := C_pos; have hR0 := R_pos; have hge := sStar_ge; have hA := A_pos
  apply hull_sub ((convex_Icc _ _).prod (convex_Icc _ _))
  intro k hk
  obtain ⟨X, Y, hX, hY, hcase⟩ := vtx k hk
  simp only [Set.mem_prod, Set.mem_Icc]
  rw [hX, hY]
  rcases hcase with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> nlinarith [mul_pos hR0 hC, mul_pos hR0 hA, C_gt.1, C_gt.2]

lemma box2 : pentagon (sStar - cos (π / 5)) (sStar - circumradius * cos (π / 5)) (π / 10 + π) ⊆
    Set.Icc 0 sStar ×ˢ Set.Icc 0 sStar := by
  have hS := S_pos; have hC := C_pos; have hR0 := R_pos; have hge := sStar_ge; have hA := A_pos
  apply hull_sub ((convex_Icc _ _).prod (convex_Icc _ _))
  intro k hk
  obtain ⟨X, Y, hX, hY, hcase⟩ := vtx k hk
  simp only [Set.mem_prod, Set.mem_Icc]
  rw [show π / 10 + π + 2 * π * (k : ℝ) / 5 = (π / 10 + 2 * π * (k : ℝ) / 5) + π by ring,
    cos_add_pi, sin_add_pi, mul_neg, mul_neg, hX, hY]
  rcases hcase with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> nlinarith [mul_pos hR0 hC, mul_pos hR0 hA, C_gt.1, C_gt.2]

lemma disj12 : Disjoint (interior (pentagon (cos (π / 5)) (circumradius * cos (π / 5)) (π / 10)))
    (interior (pentagon (sStar - cos (π / 5)) (sStar - circumradius * cos (π / 5)) (π / 10 + π))) := by
  have hS := S_pos; have hC := C_pos; have hR0 := R_pos; have heq := sStar_eq; have hRS := R_mul_S
  have h1 := SC_sq
  apply halfplane_disjoint (sin (π / 5)) (cos (π / 5))
    (sin (π / 5) * cos (π / 5) + (circumradius * cos (π / 5)) * cos (π / 5) +
      circumradius * cos (π / 5)) (by positivity)
  · apply hull_sub (convex_le _ _ _)
    intro k hk
    obtain ⟨X, Y, hX, hY, hcase⟩ := vtx k hk
    simp only [Set.mem_setOf_eq]
    rw [hX, hY]
    rcases hcase with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      nlinarith [mul_pos hR0 hC, mul_pos hS hC, C_gt.1, A_pos]
  · apply hull_sub (convex_ge _ _ _)
    intro k hk
    obtain ⟨X, Y, hX, hY, hcase⟩ := vtx k hk
    simp only [Set.mem_setOf_eq]
    rw [show π / 10 + π + 2 * π * (k : ℝ) / 5 = (π / 10 + 2 * π * (k : ℝ) / 5) + π by ring,
      cos_add_pi, sin_add_pi, mul_neg, mul_neg, hX, hY]
    rcases hcase with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      nlinarith [mul_pos hR0 hC, mul_pos hS hC, C_gt.1, A_pos]

theorem proof : PacksInSquare 2 sStar := by
  refine ⟨![cos (π / 5), sStar - cos (π / 5)],
    ![circumradius * cos (π / 5), sStar - circumradius * cos (π / 5)], ![π / 10, π / 10 + π], ?_, ?_⟩
  · intro i
    fin_cases i
    · exact box1
    · exact box2
  · intro i j hij
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · exact disj12
    · exact disj12.symm
    · exact absurd rfl hij

end Submissions.PentagonsTwoAttain.Corners
