import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.Normed.Affine.AddTorsorBases
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.Tactic
import Mathlib.Topology.Instances.Real.Lemmas

namespace Submissions.PentagonsTwoOptimal.Full

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

namespace Att

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



end Att

namespace Red

lemma collinear_det {p₁ p₂ p₃ : ℝ × ℝ} (h : Collinear ℝ ({p₁, p₂, p₃} : Set (ℝ × ℝ))) :
    (p₂.1 - p₁.1) * (p₃.2 - p₁.2) - (p₃.1 - p₁.1) * (p₂.2 - p₁.2) = 0 := by
  rw [collinear_iff_of_mem (p₀ := p₁) (by simp)] at h
  obtain ⟨v, hv⟩ := h
  obtain ⟨r₂, h₂⟩ := hv p₂ (by simp)
  obtain ⟨r₃, h₃⟩ := hv p₃ (by simp)
  subst h₂ h₃
  simp; ring

theorem pentagon_interior_nonempty (a b θ : ℝ) : (interior (pentagon a b θ)).Nonempty := by
  have hR : 0 < circumradius := by
    unfold circumradius
    have : 0 < Real.sin (Real.pi / 5) :=
      Real.sin_pos_of_pos_of_lt_pi (by positivity) (by linarith [Real.pi_pos])
    positivity
  set v : Fin 5 → ℝ × ℝ := fun k =>
    (a + circumradius * Real.cos (θ + 2 * Real.pi * ((k : ℕ) : ℝ) / 5),
     b + circumradius * Real.sin (θ + 2 * Real.pi * ((k : ℕ) : ℝ) / 5)) with hv
  have hpent : pentagon a b θ = convexHull ℝ (Set.range v) := rfl
  rw [hpent, interior_convexHull_nonempty_iff_affineSpan_eq_top]
  -- three vertices are not collinear
  have hS : 0 < Real.sin (Real.pi / 5) :=
    Real.sin_pos_of_pos_of_lt_pi (by positivity) (by linarith [Real.pi_pos])
  have hC : Real.cos (Real.pi / 5) = (1 + Real.sqrt 5) / 4 := Real.cos_pi_div_five
  have h5 : (2 : ℝ) < Real.sqrt 5 := by
    rw [show (2:ℝ) = Real.sqrt 4 by rw [show (4:ℝ) = 2^2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  have hnc : ¬ Collinear ℝ ({v 0, v 1, v 2} : Set (ℝ × ℝ)) := by
    intro h
    have hd := collinear_det h
    simp only [hv] at hd
    have e1 : θ + 2 * Real.pi * ((((1 : Fin 5)) : ℕ) : ℝ) / 5 = θ + 2 * (Real.pi / 5) := by
      simp; ring
    have e2 : θ + 2 * Real.pi * ((((2 : Fin 5)) : ℕ) : ℝ) / 5 = θ + (Real.pi - Real.pi / 5) := by
      simp; ring
    have e0 : θ + 2 * Real.pi * ((((0 : Fin 5)) : ℕ) : ℝ) / 5 = θ := by simp
    rw [e0, e1, e2] at hd
    simp only [Real.cos_add, Real.sin_add, Real.cos_two_mul, Real.sin_two_mul,
      Real.cos_pi_sub, Real.sin_pi_sub, hC] at hd
    have key : circumradius ^ 2 * (2 * Real.sin (Real.pi / 5) *
        (2 * ((1 + Real.sqrt 5) / 4) - 1) * ((1 + Real.sqrt 5) / 4 + 1)) = 0 := by
      rw [← hd]
      have hs5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
      have hsc : Real.sin (Real.pi/5) ^ 2 = 1 - ((1 + Real.sqrt 5) / 4) ^ 2 := by
        rw [← hC, ← Real.cos_sq_add_sin_sq (Real.pi/5)]; ring
      linear_combination (circumradius ^ 2 * (2 * Real.sin (Real.pi / 5) *
        (2 * ((1 + Real.sqrt 5) / 4) - 1) * ((1 + Real.sqrt 5) / 4 + 1))
        - 2 * Real.sqrt 5 * circumradius ^ 2 * Real.sin (Real.pi / 5)) * (Real.sin_sq_add_cos_sq θ)
        + (circumradius ^ 2 * Real.sin (Real.pi / 5) *
            (1 / 2 - (Real.cos θ ^ 2 + Real.sin θ ^ 2) / 2)) * hs5
    have : 0 < circumradius ^ 2 * (2 * Real.sin (Real.pi / 5) *
        (2 * ((1 + Real.sqrt 5) / 4) - 1) * ((1 + Real.sqrt 5) / 4 + 1)) := by
      apply mul_pos (by positivity)
      apply mul_pos (mul_pos (by positivity) (by linarith)) (by positivity)
    linarith
  have hai : AffineIndependent ℝ ![v 0, v 1, v 2] := by
    rw [affineIndependent_iff_not_collinear_set]; exact hnc
  have htop : affineSpan ℝ (Set.range ![v 0, v 1, v 2]) = ⊤ := by
    rw [hai.affineSpan_eq_top_iff_card_eq_finrank_add_one]
    simp [Module.finrank_prod]
  apply eq_top_iff.mpr
  rw [← htop]
  apply affineSpan_mono
  rintro _ ⟨i, rfl⟩
  fin_cases i <;> simp


/-! ### Basic vertex facts -/

lemma vert_mem (a b θ : ℝ) (m : ℤ) :
    (a + circumradius * cos (θ + 2 * π * (m : ℝ) / 5),
      b + circumradius * sin (θ + 2 * π * (m : ℝ) / 5)) ∈ pentagon a b θ := by
  have hk : (m % 5).toNat < 5 := by omega
  apply subset_convexHull
  refine ⟨⟨(m % 5).toNat, hk⟩, ?_⟩
  have h1 : (((m % 5).toNat : ℕ) : ℤ) = m % 5 := Int.toNat_of_nonneg (Int.emod_nonneg _ (by norm_num))
  have h2 : (m : ℝ) = 5 * ((m / 5 : ℤ) : ℝ) + (((m % 5).toNat : ℕ) : ℝ) := by
    have h3 : ((((m % 5).toNat : ℕ)) : ℝ) = ((m % 5 : ℤ) : ℝ) := by exact_mod_cast h1
    rw [h3]
    have h4 : m = m % 5 + 5 * (m / 5) := by omega
    have h5 : (m : ℝ) = ((m % 5 : ℤ) : ℝ) + 5 * ((m / 5 : ℤ) : ℝ) := by exact_mod_cast h4
    linarith
  have e : θ + 2 * π * (m : ℝ) / 5
      = θ + 2 * π * (((m % 5).toNat : ℕ) : ℝ) / 5 + ((m / 5 : ℤ) : ℝ) * (2 * π) := by
    rw [h2]; ring
  simp only
  rw [e, cos_add_int_mul_two_pi, sin_add_int_mul_two_pi]

/-- An affine map of the form `x ↦ (e₁ x₁ + c₁, e₂ x₂ + c₂)`. -/
def σ (e1 c1 e2 c2 : ℝ) (x : ℝ × ℝ) : ℝ × ℝ := (e1 * x.1 + c1, e2 * x.2 + c2)

lemma convex_preimage {K : Set (ℝ × ℝ)} (hK : Convex ℝ K) (e1 c1 e2 c2 : ℝ) :
    Convex ℝ {x | σ e1 c1 e2 c2 x ∈ K} := by
  intro x hx y hy t u ht hu htu
  simp only [Set.mem_setOf_eq] at *
  have := hK hx hy ht hu htu
  convert this using 1
  simp only [σ, Prod.smul_mk, Prod.mk_add_mk, Prod.fst_add, Prod.snd_add, Prod.smul_fst,
    Prod.smul_snd, smul_eq_mul, Prod.mk.injEq]
  constructor
  · linear_combination (-c1) * htu
  · linear_combination (-c2) * htu

/-- Transport along `σ`: if every vertex of `N` is mapped by `σ` to a vertex of `P`, then
`σ` maps `N` into `P`. -/
lemma image_sub {a b θ a' b' θ' e1 c1 e2 c2 : ℝ}
    (hv : ∀ m : ℤ, ∃ m' : ℤ,
      σ e1 c1 e2 c2 (a' + circumradius * cos (θ' + 2 * π * (m : ℝ) / 5),
        b' + circumradius * sin (θ' + 2 * π * (m : ℝ) / 5)) =
      (a + circumradius * cos (θ + 2 * π * (m' : ℝ) / 5),
        b + circumradius * sin (θ + 2 * π * (m' : ℝ) / 5)))
    {p : ℝ × ℝ} (hp : p ∈ pentagon a' b' θ') : σ e1 c1 e2 c2 p ∈ pentagon a b θ := by
  have hsub : pentagon a' b' θ' ⊆ {x | σ e1 c1 e2 c2 x ∈ pentagon a b θ} := by
    apply convexHull_min _ (convex_preimage (convex_convexHull ℝ _) _ _ _ _)
    rintro _ ⟨k, rfl⟩
    obtain ⟨m', hm'⟩ := hv (k : ℕ)
    simp only [Set.mem_setOf_eq]
    have := vert_mem a b θ m'
    rw [← hm'] at this
    push_cast at this
    exact this
  exact hsub hp

/-- Vertices of `N` lie in the quadrant if they are `σ`-images of vertices of a pentagon in a box. -/
lemma quad_of_box {a b θ a' b' θ' s : ℝ} (e1 c1 e2 c2 : ℝ)
    (hbox : pentagon a b θ ⊆ Set.Icc 0 s ×ˢ Set.Icc 0 s)
    (hq : ∀ x : ℝ × ℝ, x ∈ Set.Icc 0 s ×ˢ Set.Icc 0 s → σ e1 c1 e2 c2 x ∈ Set.Ici 0 ×ˢ Set.Ici 0)
    (hv : ∀ m : ℤ, ∃ m' : ℤ,
      (a' + circumradius * cos (θ' + 2 * π * (m : ℝ) / 5),
        b' + circumradius * sin (θ' + 2 * π * (m : ℝ) / 5)) =
      σ e1 c1 e2 c2 (a + circumradius * cos (θ + 2 * π * (m' : ℝ) / 5),
        b + circumradius * sin (θ + 2 * π * (m' : ℝ) / 5))) :
    pentagon a' b' θ' ⊆ Set.Ici 0 ×ˢ Set.Ici 0 := by
  apply convexHull_min _ ((convex_Ici _).prod (convex_Ici _))
  rintro _ ⟨k, rfl⟩
  obtain ⟨m', hm'⟩ := hv (k : ℕ)
  have := hq _ (hbox (vert_mem a b θ m'))
  rw [← hm'] at this
  push_cast at this
  exact this

/-- The corner lemma at all four corners of the square `[0,s]²`. -/
lemma corners (H : ∀ a b θ : ℝ, pentagon a b θ ⊆ Set.Ici 0 ×ˢ Set.Ici 0 →
      ∃ p ∈ pentagon a b θ, sStar / 2 ≤ p.1 ∧ sStar / 2 ≤ p.2)
    {a b θ s : ℝ} (hbox : pentagon a b θ ⊆ Set.Icc 0 s ×ˢ Set.Icc 0 s) :
    (∃ p ∈ pentagon a b θ, sStar / 2 ≤ p.1 ∧ sStar / 2 ≤ p.2) ∧
    (∃ p ∈ pentagon a b θ, p.1 ≤ s - sStar / 2 ∧ sStar / 2 ≤ p.2) ∧
    (∃ p ∈ pentagon a b θ, sStar / 2 ≤ p.1 ∧ p.2 ≤ s - sStar / 2) ∧
    (∃ p ∈ pentagon a b θ, p.1 ≤ s - sStar / 2 ∧ p.2 ≤ s - sStar / 2) := by
  have hq0 : pentagon a b θ ⊆ Set.Ici 0 ×ˢ Set.Ici 0 := fun x hx => by
    obtain ⟨⟨h1, -⟩, ⟨h2, -⟩⟩ := hbox hx; exact ⟨h1, h2⟩
  refine ⟨H a b θ hq0, ?_, ?_, ?_⟩
  · -- reflect x ↦ s - x
    have hN := quad_of_box (a' := s - a) (b' := b) (θ' := π - θ) (-1) s 1 0 hbox
      (fun x ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩ => ⟨by simp [σ]; linarith, by simp [σ]; linarith⟩)
      (fun m => ⟨-m, by
        simp only [σ, Prod.mk.injEq]; push_cast
        rw [show π - θ + 2 * π * (m : ℝ) / 5 = π - (θ + 2 * π * (-(m : ℝ)) / 5) by ring,
          cos_pi_sub, sin_pi_sub]
        constructor <;> ring⟩)
    obtain ⟨p, hp, h1, h2⟩ := H _ _ _ hN
    refine ⟨σ (-1) s 1 0 p, image_sub (fun m => ⟨-m, ?_⟩) hp, ?_, ?_⟩
    · simp only [σ, Prod.mk.injEq]; push_cast
      rw [show π - θ + 2 * π * (m : ℝ) / 5 = π - (θ + 2 * π * (-(m : ℝ)) / 5) by ring,
        cos_pi_sub, sin_pi_sub]
      constructor <;> ring
    · simp only [σ]; linarith
    · simp only [σ]; linarith
  · -- reflect y ↦ s - y
    have hN := quad_of_box (a' := a) (b' := s - b) (θ' := -θ) 1 0 (-1) s hbox
      (fun x ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩ => ⟨by simp [σ]; linarith, by simp [σ]; linarith⟩)
      (fun m => ⟨-m, by
        simp only [σ, Prod.mk.injEq]; push_cast
        rw [show -θ + 2 * π * (m : ℝ) / 5 = -(θ + 2 * π * (-(m : ℝ)) / 5) by ring,
          cos_neg, sin_neg]
        constructor <;> ring⟩)
    obtain ⟨p, hp, h1, h2⟩ := H _ _ _ hN
    refine ⟨σ 1 0 (-1) s p, image_sub (fun m => ⟨-m, ?_⟩) hp, ?_, ?_⟩
    · simp only [σ, Prod.mk.injEq]; push_cast
      rw [show -θ + 2 * π * (m : ℝ) / 5 = -(θ + 2 * π * (-(m : ℝ)) / 5) by ring,
        cos_neg, sin_neg]
      constructor <;> ring
    · simp only [σ]; linarith
    · simp only [σ]; linarith
  · -- point reflection
    have hN := quad_of_box (a' := s - a) (b' := s - b) (θ' := θ + π) (-1) s (-1) s hbox
      (fun x ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩ => ⟨by simp [σ]; linarith, by simp [σ]; linarith⟩)
      (fun m => ⟨m, by
        simp only [σ, Prod.mk.injEq]
        rw [show θ + π + 2 * π * (m : ℝ) / 5 = (θ + 2 * π * (m : ℝ) / 5) + π by ring,
          cos_add_pi, sin_add_pi]
        constructor <;> ring⟩)
    obtain ⟨p, hp, h1, h2⟩ := H _ _ _ hN
    refine ⟨σ (-1) s (-1) s p, image_sub (fun m => ⟨m, ?_⟩) hp, ?_, ?_⟩
    · simp only [σ, Prod.mk.injEq]
      rw [show θ + π + 2 * π * (m : ℝ) / 5 = (θ + 2 * π * (m : ℝ) / 5) + π by ring,
        cos_add_pi, sin_add_pi]
      constructor <;> ring
    · simp only [σ]; linarith
    · simp only [σ]; linarith

/-! ### Separation of two pentagons with disjoint interiors -/

lemma pentagon_closed (a b θ : ℝ) : IsClosed (pentagon a b θ) :=
  (Set.finite_range _).isClosed_convexHull ℝ

lemma separate {a b θ a' b' θ' : ℝ}
    (hd : Disjoint (interior (pentagon a b θ)) (interior (pentagon a' b' θ'))) :
    ∃ u1 u2 u : ℝ, (u1 ≠ 0 ∨ u2 ≠ 0) ∧
      (∀ x ∈ pentagon a b θ, u1 * x.1 + u2 * x.2 ≤ u) ∧
      (∀ x ∈ pentagon a' b' θ', u ≤ u1 * x.1 + u2 * x.2) := by
  have hP := pentagon_interior_nonempty a b θ
  have hQ := pentagon_interior_nonempty a' b' θ'
  have cP : Convex ℝ (pentagon a b θ) := convex_convexHull ℝ _
  have cQ : Convex ℝ (pentagon a' b' θ') := convex_convexHull ℝ _
  obtain ⟨f, u, hf1, hf2⟩ := geometric_hahn_banach_open_open cP.interior isOpen_interior
    cQ.interior isOpen_interior hd
  have hlin : ∀ x : ℝ × ℝ, f x = f (1, 0) * x.1 + f (0, 1) * x.2 := by
    intro x
    have : x = x.1 • ((1:ℝ), (0:ℝ)) + x.2 • ((0:ℝ), (1:ℝ)) := by ext <;> simp
    conv_lhs => rw [this]
    rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]; ring
  refine ⟨f (1, 0), f (0, 1), u, ?_, ?_, ?_⟩
  · by_contra h
    push_neg at h
    obtain ⟨x, hx⟩ := hP; obtain ⟨y, hy⟩ := hQ
    have h1 := hf1 x hx; have h2 := hf2 y hy
    rw [hlin, h.1, h.2] at h1 h2
    linarith
  · intro x hx
    have hcl : pentagon a b θ ⊆ closure (interior (pentagon a b θ)) := by
      rw [cP.closure_interior_eq_closure_of_nonempty_interior hP, (pentagon_closed a b θ).closure_eq]
    have hsub : closure (interior (pentagon a b θ)) ⊆ {x | f x ≤ u} :=
      closure_minimal (fun y hy => (hf1 y hy).le) (isClosed_le f.continuous continuous_const)
    have := hsub (hcl hx)
    simp only [Set.mem_setOf_eq] at this
    rwa [hlin] at this
  · intro x hx
    have hcl : pentagon a' b' θ' ⊆ closure (interior (pentagon a' b' θ')) := by
      rw [cQ.closure_interior_eq_closure_of_nonempty_interior hQ, (pentagon_closed a' b' θ').closure_eq]
    have hsub : closure (interior (pentagon a' b' θ')) ⊆ {x | u ≤ f x} :=
      closure_minimal (fun y hy => (hf2 y hy).le) (isClosed_le continuous_const f.continuous)
    have := hsub (hcl hx)
    simp only [Set.mem_setOf_eq] at this
    rwa [hlin] at this

theorem proof : (∀ a b θ : ℝ, pentagon a b θ ⊆ Set.Ici 0 ×ˢ Set.Ici 0 →
      ∃ p ∈ pentagon a b θ, sStar / 2 ≤ p.1 ∧ sStar / 2 ≤ p.2) →
    ∀ s : ℝ, PacksInSquare 2 s → sStar ≤ s := by
  intro H s ⟨a, b, θ, hbox, hdisj⟩
  obtain ⟨u1, u2, u, hu, hP, hQ⟩ := separate (hdisj 0 1 (by decide))
  obtain ⟨P1, P2, P3, P4⟩ := corners H (hbox 0)
  obtain ⟨Q1, Q2, Q3, Q4⟩ := corners H (hbox 1)
  rcases le_total 0 u1 with h1 | h1 <;> rcases le_total 0 u2 with h2 | h2
  · obtain ⟨p, hp, hp1, hp2⟩ := P1; obtain ⟨q, hq, hq1, hq2⟩ := Q4
    have := hP p hp; have := hQ q hq
    have hpos : 0 < u1 + u2 := by
      rcases hu with hu | hu
      · exact add_pos_of_pos_of_nonneg (lt_of_le_of_ne h1 (Ne.symm hu)) h2
      · exact add_pos_of_nonneg_of_pos h1 (lt_of_le_of_ne h2 (Ne.symm hu))
    nlinarith [mul_le_mul_of_nonneg_left (show q.1 - p.1 ≤ s - sStar by linarith) h1,
      mul_le_mul_of_nonneg_left (show q.2 - p.2 ≤ s - sStar by linarith) h2]
  · obtain ⟨p, hp, hp1, hp2⟩ := P3; obtain ⟨q, hq, hq1, hq2⟩ := Q2
    have := hP p hp; have := hQ q hq
    have hpos : 0 < u1 - u2 := by
      rcases hu with hu | hu
      · have := lt_of_le_of_ne h1 (Ne.symm hu); linarith
      · have := lt_of_le_of_ne h2 hu; linarith
    nlinarith [mul_le_mul_of_nonneg_left (show q.1 - p.1 ≤ s - sStar by linarith) h1,
      mul_le_mul_of_nonneg_left (show p.2 - q.2 ≤ s - sStar by linarith) (neg_nonneg.mpr h2)]
  · obtain ⟨p, hp, hp1, hp2⟩ := P2; obtain ⟨q, hq, hq1, hq2⟩ := Q3
    have := hP p hp; have := hQ q hq
    have hpos : 0 < u2 - u1 := by
      rcases hu with hu | hu
      · have := lt_of_le_of_ne h1 hu; linarith
      · have := lt_of_le_of_ne h2 (Ne.symm hu); linarith
    nlinarith [mul_le_mul_of_nonneg_left (show p.1 - q.1 ≤ s - sStar by linarith) (neg_nonneg.mpr h1),
      mul_le_mul_of_nonneg_left (show q.2 - p.2 ≤ s - sStar by linarith) h2]
  · obtain ⟨p, hp, hp1, hp2⟩ := P4; obtain ⟨q, hq, hq1, hq2⟩ := Q1
    have := hP p hp; have := hQ q hq
    have hpos : 0 < -u1 - u2 := by
      rcases hu with hu | hu
      · have := lt_of_le_of_ne h1 hu; linarith
      · have := lt_of_le_of_ne h2 hu; linarith
    nlinarith [mul_le_mul_of_nonneg_left (show p.1 - q.1 ≤ s - sStar by linarith) (neg_nonneg.mpr h1),
      mul_le_mul_of_nonneg_left (show p.2 - q.2 ≤ s - sStar by linarith) (neg_nonneg.mpr h2)]



end Red

namespace Cor

local notation "𝒞" => Real.cos (Real.pi / 5)
local notation "𝒮" => Real.sin (Real.pi / 5)

lemma S_pos : 0 < 𝒮 := sin_pos_of_pos_of_lt_pi (by positivity) (by linarith [pi_pos])
lemma C_eq : 𝒞 = (1 + √5) / 4 := cos_pi_div_five
lemma C_pos : 0 < 𝒞 := by rw [C_eq]; positivity
lemma hSC' : 𝒮 ^ 2 + 𝒞 ^ 2 = 1 := sin_sq_add_cos_sq _
lemma hC2' : 4 * 𝒞 ^ 2 - 2 * 𝒞 - 1 = 0 := by
  rw [C_eq]; have := Real.sq_sqrt (show (0:ℝ) ≤ 5 by norm_num); nlinarith
lemma C_tight : (809016 / 1000000 : ℝ) < 𝒞 ∧ 𝒞 < 809018 / 1000000 := by
  rw [C_eq]
  have h1 : (2236064 / 1000000 : ℝ) < √5 := by rw [Real.lt_sqrt (by norm_num)]; norm_num
  have h2 : √5 < 2236072 / 1000000 := by rw [Real.sqrt_lt' (by norm_num)]; norm_num
  constructor <;> linarith
lemma C_bnd : (80901 / 100000 : ℝ) ≤ 𝒞 ∧ 𝒞 ≤ 80902 / 100000 := by
  obtain ⟨h1, h2⟩ := C_tight; constructor <;> linarith
lemma S_bnd : (58778 / 100000 : ℝ) ≤ 𝒮 ∧ 𝒮 ≤ 58779 / 100000 := by
  obtain ⟨h1, h2⟩ := C_tight; have h3 := hSC'; have h4 := S_pos
  constructor
  · by_contra h; have h' := (not_le.mp h); nlinarith
  · by_contra h; have h' := (not_le.mp h); nlinarith
lemma P_bnd : (475519 / 1000000 : ℝ) ≤ 𝒞 * 𝒮 ∧ 𝒞 * 𝒮 ≤ 475535 / 1000000 := by
  obtain ⟨h1, h2⟩ := C_bnd; obtain ⟨h3, h4⟩ := S_bnd
  constructor <;> nlinarith

lemma cos10 : cos (π / 10) = 2 * 𝒮 * 𝒞 := by
  rw [← sin_pi_div_two_sub, show π / 2 - π / 10 = 2 * (π / 5) by ring, sin_two_mul]
lemma sin10 : sin (π / 10) = 2 * 𝒞 ^ 2 - 1 := by
  rw [← cos_pi_div_two_sub, show π / 2 - π / 10 = 2 * (π / 5) by ring, cos_two_mul]
lemma cos310 : cos (3 * π / 10) = 𝒮 := by
  rw [← sin_pi_div_two_sub, show π / 2 - 3 * π / 10 = π / 5 by ring]
lemma sin310 : sin (3 * π / 10) = 𝒞 := by
  rw [← cos_pi_div_two_sub, show π / 2 - 3 * π / 10 = π / 5 by ring]

lemma tab_c_0 : cos 0 = 1 := cos_zero
lemma tab_s_0 : sin 0 = 0 := sin_zero
lemma tab_c_72 : cos (2 * π / 5) = 2 * 𝒞 ^ 2 - 1 := by
  rw [show 2 * π / 5 = 2 * (π / 5) by ring, cos_two_mul]
lemma tab_s_72 : sin (2 * π / 5) = 2 * 𝒮 * 𝒞 := by
  rw [show 2 * π / 5 = 2 * (π / 5) by ring, sin_two_mul]
lemma tab_c_144 : cos (4 * π / 5) = -𝒞 := by
  rw [show 4 * π / 5 = π - π / 5 by ring, cos_pi_sub]
lemma tab_s_144 : sin (4 * π / 5) = 𝒮 := by
  rw [show 4 * π / 5 = π - π / 5 by ring, sin_pi_sub]
lemma tab_c_216 : cos (6 * π / 5) = -𝒞 := by
  rw [show 6 * π / 5 = π / 5 + π by ring, cos_add_pi]
lemma tab_s_216 : sin (6 * π / 5) = -𝒮 := by
  rw [show 6 * π / 5 = π / 5 + π by ring, sin_add_pi]
lemma tab_c_288 : cos (8 * π / 5) = 2 * 𝒞 ^ 2 - 1 := by
  rw [show 8 * π / 5 = -(2 * (π / 5)) + 2 * π by ring, cos_add_two_pi, cos_neg, cos_two_mul]
lemma tab_s_288 : sin (8 * π / 5) = -(2 * 𝒮 * 𝒞) := by
  rw [show 8 * π / 5 = -(2 * (π / 5)) + 2 * π by ring, sin_add_two_pi, sin_neg, sin_two_mul]
lemma tab_c_18 : cos (π / 10) = 2 * 𝒮 * 𝒞 := cos10
lemma tab_s_18 : sin (π / 10) = 2 * 𝒞 ^ 2 - 1 := sin10
lemma tab_c_90 : cos (π / 2) = 0 := cos_pi_div_two
lemma tab_s_90 : sin (π / 2) = 1 := sin_pi_div_two
lemma tab_c_162 : cos (9 * π / 10) = -(2 * 𝒮 * 𝒞) := by
  rw [show 9 * π / 10 = π - π / 10 by ring, cos_pi_sub, cos10]
lemma tab_s_162 : sin (9 * π / 10) = 2 * 𝒞 ^ 2 - 1 := by
  rw [show 9 * π / 10 = π - π / 10 by ring, sin_pi_sub, sin10]
lemma tab_c_234 : cos (13 * π / 10) = -𝒮 := by
  rw [show 13 * π / 10 = 3 * π / 10 + π by ring, cos_add_pi, cos310]
lemma tab_s_234 : sin (13 * π / 10) = -𝒞 := by
  rw [show 13 * π / 10 = 3 * π / 10 + π by ring, sin_add_pi, sin310]
lemma tab_c_306 : cos (17 * π / 10) = 𝒮 := by
  rw [show 17 * π / 10 = -(3 * π / 10) + 2 * π by ring, cos_add_two_pi, cos_neg, cos310]
lemma tab_s_306 : sin (17 * π / 10) = -𝒞 := by
  rw [show 17 * π / 10 = -(3 * π / 10) + 2 * π by ring, sin_add_two_pi, sin_neg, sin310]

lemma vert_mem (a b θ : ℝ) (m : ℤ) :
    (a + circumradius * cos (θ + 2 * π * (m : ℝ) / 5),
      b + circumradius * sin (θ + 2 * π * (m : ℝ) / 5)) ∈ pentagon a b θ := by
  have hk : (m % 5).toNat < 5 := by omega
  apply subset_convexHull
  refine ⟨⟨(m % 5).toNat, hk⟩, ?_⟩
  have h1 : (((m % 5).toNat : ℕ) : ℤ) = m % 5 := Int.toNat_of_nonneg (Int.emod_nonneg _ (by norm_num))
  have h2 : (m : ℝ) = 5 * ((m / 5 : ℤ) : ℝ) + (((m % 5).toNat : ℕ) : ℝ) := by
    have h3 : ((((m % 5).toNat : ℕ)) : ℝ) = ((m % 5 : ℤ) : ℝ) := by exact_mod_cast h1
    rw [h3]
    have h4 : m = m % 5 + 5 * (m / 5) := by omega
    have h5 : (m : ℝ) = ((m % 5 : ℤ) : ℝ) + 5 * ((m / 5 : ℤ) : ℝ) := by exact_mod_cast h4
    linarith
  have e : θ + 2 * π * (m : ℝ) / 5
      = θ + 2 * π * (((m % 5).toNat : ℕ) : ℝ) / 5 + ((m / 5 : ℤ) : ℝ) * (2 * π) := by
    rw [h2]; ring
  simp only
  rw [e, cos_add_int_mul_two_pi, sin_add_int_mul_two_pi]


lemma pos_R1_pA1 (c s : ℝ) (hcl : ((111 : ℝ) / 125) ≤ c) (hch : c ≤ (1 : ℝ)) (hsl : ((-189 : ℝ) / 400) ≤ s) (hsh : s ≤ (0 : ℝ)) :
    (0:ℝ) < (-1 : ℝ) * (𝒞) ^ 2 + (-3 : ℝ) * (𝒞) + (2 : ℝ) * (𝒞) ^ 3 + (1 : ℝ) * (𝒞) * (c) + (1 : ℝ) * (𝒮) * (c) + (1 : ℝ) * (c) * (𝒞) ^ 2 + (-1 : ℝ) * (s) * (𝒮) ^ 2 + (1 : ℝ) * (𝒞) * (𝒮) * (c) + (-1 : ℝ) * (𝒞) * (𝒮) * (s) := by
  have hSC := hSC'; have hC2 := hC2'
  obtain ⟨hCl, hCh⟩ := C_bnd; obtain ⟨hSl, hSh⟩ := S_bnd; obtain ⟨hPl, hPh⟩ := P_bnd
  have e : (-1 : ℝ) * (𝒞) ^ 2 + (-3 : ℝ) * (𝒞) + (2 : ℝ) * (𝒞) ^ 3 + (1 : ℝ) * (𝒞) * (c) + (1 : ℝ) * (𝒮) * (c) + (1 : ℝ) * (c) * (𝒞) ^ 2 + (-1 : ℝ) * (s) * (𝒮) ^ 2 + (1 : ℝ) * (𝒞) * (𝒮) * (c) + (-1 : ℝ) * (𝒞) * (𝒮) * (s) = ((-5 : ℝ) / 2) * (𝒞) + ((-3 : ℝ) / 4) * (s) + ((1 : ℝ) / 4) * (c) + (1 : ℝ) * (𝒮) * (c) + ((1 : ℝ) / 2) * (𝒞) * (s) + ((3 : ℝ) / 2) * (𝒞) * (c) + (1 : ℝ) * (𝒞) * (𝒮) * (c) + (-1 : ℝ) * (𝒞) * (𝒮) * (s) := by
    linear_combination ((-1 : ℝ) * (s)) * hSC + (((1 : ℝ) / 2) * (𝒞) + ((1 : ℝ) / 4) * (c) + ((1 : ℝ) / 4) * (s)) * hC2
  rw [e]
  have k0 : ((-40451 : ℝ) / 20000) ≤ ((-5 : ℝ) / 2) * (𝒞) := by linarith
  have k1l : ((1263407 : ℝ) / 500000) ≤ ((1 : ℝ) / 4) + (1 : ℝ) * (𝒮) + ((3 : ℝ) / 2) * (𝒞) + (1 : ℝ) * (𝒞) * (𝒮) := by linarith
  have k1h : ((1 : ℝ) / 4) + (1 : ℝ) * (𝒮) + ((3 : ℝ) / 2) * (𝒞) + (1 : ℝ) * (𝒞) * (𝒮) ≤ ((505371 : ℝ) / 200000) := by linarith
  have k2l : ((-82103 : ℝ) / 100000) ≤ ((-3 : ℝ) / 4) + ((1 : ℝ) / 2) * (𝒞) + (-1 : ℝ) * (𝒞) * (𝒮) := by linarith
  have k2h : ((-3 : ℝ) / 4) + ((1 : ℝ) / 2) * (𝒞) + (-1 : ℝ) * (𝒞) * (𝒮) ≤ ((-821009 : ℝ) / 1000000) := by linarith
  nlinarith [mul_nonneg (sub_nonneg.2 k1l) (sub_nonneg.2 hcl), mul_nonneg (sub_nonneg.2 k1h) (sub_nonneg.2 hch), mul_nonneg (sub_nonneg.2 k1l) (sub_nonneg.2 hch), mul_nonneg (sub_nonneg.2 k1h) (sub_nonneg.2 hcl), mul_nonneg (sub_nonneg.2 k2l) (sub_nonneg.2 hsl), mul_nonneg (sub_nonneg.2 k2h) (sub_nonneg.2 hsh), mul_nonneg (sub_nonneg.2 k2l) (sub_nonneg.2 hsh), mul_nonneg (sub_nonneg.2 k2h) (sub_nonneg.2 hsl)]

lemma pos_R1_pB2 (c s : ℝ) (hcl : ((111 : ℝ) / 125) ≤ c) (hch : c ≤ (1 : ℝ)) (hsl : ((-189 : ℝ) / 400) ≤ s) (hsh : s ≤ (0 : ℝ)) :
    (0:ℝ) ≤ (-1 : ℝ) * (𝒞) ^ 2 + (-3 : ℝ) * (𝒞) + (2 : ℝ) * (𝒞) ^ 3 + (4 : ℝ) * (𝒞) * (c) * (𝒮) ^ 2 + (4 : ℝ) * (𝒮) * (c) * (𝒞) ^ 2 := by
  have hSC := hSC'; have hC2 := hC2'
  obtain ⟨hCl, hCh⟩ := C_bnd; obtain ⟨hSl, hSh⟩ := S_bnd; obtain ⟨hPl, hPh⟩ := P_bnd
  have e : (-1 : ℝ) * (𝒞) ^ 2 + (-3 : ℝ) * (𝒞) + (2 : ℝ) * (𝒞) ^ 3 + (4 : ℝ) * (𝒞) * (c) * (𝒮) ^ 2 + (4 : ℝ) * (𝒮) * (c) * (𝒞) ^ 2 = ((-5 : ℝ) / 2) * (𝒞) + ((-1 : ℝ) / 2) * (c) + (1 : ℝ) * (𝒮) * (c) + (2 : ℝ) * (𝒞) * (c) + (2 : ℝ) * (𝒞) * (𝒮) * (c) := by
    linear_combination ((4 : ℝ) * (𝒞) * (c)) * hSC + (((1 : ℝ) / 2) * (𝒞) + ((-1 : ℝ) / 2) * (c) + (1 : ℝ) * (𝒮) * (c) + (-1 : ℝ) * (𝒞) * (c)) * hC2
  rw [e]
  have k0 : ((-40451 : ℝ) / 20000) ≤ ((-5 : ℝ) / 2) * (𝒞) := by linarith
  have k1l : ((1328419 : ℝ) / 500000) ≤ ((-1 : ℝ) / 2) + (1 : ℝ) * (𝒮) + (2 : ℝ) * (𝒞) + (2 : ℝ) * (𝒞) * (𝒮) := by linarith
  have k1h : ((-1 : ℝ) / 2) + (1 : ℝ) * (𝒮) + (2 : ℝ) * (𝒞) + (2 : ℝ) * (𝒞) * (𝒮) ≤ ((26569 : ℝ) / 10000) := by linarith
  have k2l : (0 : ℝ) ≤ (0 : ℝ) := by linarith
  have k2h : (0 : ℝ) ≤ (0 : ℝ) := by linarith
  nlinarith [mul_nonneg (sub_nonneg.2 k1l) (sub_nonneg.2 hcl), mul_nonneg (sub_nonneg.2 k1h) (sub_nonneg.2 hch), mul_nonneg (sub_nonneg.2 k1l) (sub_nonneg.2 hch), mul_nonneg (sub_nonneg.2 k1h) (sub_nonneg.2 hcl), mul_nonneg (sub_nonneg.2 k2l) (sub_nonneg.2 hsl), mul_nonneg (sub_nonneg.2 k2h) (sub_nonneg.2 hsh), mul_nonneg (sub_nonneg.2 k2l) (sub_nonneg.2 hsh), mul_nonneg (sub_nonneg.2 k2h) (sub_nonneg.2 hsl)]

lemma pos_R1_pM1 (c s : ℝ) (hcl : ((111 : ℝ) / 125) ≤ c) (hch : c ≤ (1 : ℝ)) (hsl : ((-189 : ℝ) / 400) ≤ s) (hsh : s ≤ (0 : ℝ)) :
    (0:ℝ) ≤ (-2 : ℝ) * (c) + ((5 : ℝ) / 4) * (𝒮) + ((5 : ℝ) / 4) * (s) + (-1 : ℝ) * (𝒮) * (s) + (3 : ℝ) * (𝒞) * (c) + ((3 : ℝ) / 2) * (𝒮) * (c) + (-1 : ℝ) * (𝒞) * (𝒮) * (c) + (4 : ℝ) * (𝒞) * (𝒮) * (s) := by
  have hSC := hSC'; have hC2 := hC2'
  obtain ⟨hCl, hCh⟩ := C_bnd; obtain ⟨hSl, hSh⟩ := S_bnd; obtain ⟨hPl, hPh⟩ := P_bnd
  have e : (-2 : ℝ) * (c) + ((5 : ℝ) / 4) * (𝒮) + ((5 : ℝ) / 4) * (s) + (-1 : ℝ) * (𝒮) * (s) + (3 : ℝ) * (𝒞) * (c) + ((3 : ℝ) / 2) * (𝒮) * (c) + (-1 : ℝ) * (𝒞) * (𝒮) * (c) + (4 : ℝ) * (𝒞) * (𝒮) * (s) = (-2 : ℝ) * (c) + ((5 : ℝ) / 4) * (𝒮) + ((5 : ℝ) / 4) * (s) + (-1 : ℝ) * (𝒮) * (s) + (3 : ℝ) * (𝒞) * (c) + ((3 : ℝ) / 2) * (𝒮) * (c) + (-1 : ℝ) * (𝒞) * (𝒮) * (c) + (4 : ℝ) * (𝒞) * (𝒮) * (s) := by
    linear_combination ((0 : ℝ)) * hSC + ((0 : ℝ)) * hC2
  rw [e]
  have k0 : ((29389 : ℝ) / 40000) ≤ ((5 : ℝ) / 4) * (𝒮) := by linarith
  have k1l : ((166633 : ℝ) / 200000) ≤ (-2 : ℝ) + (3 : ℝ) * (𝒞) + ((3 : ℝ) / 2) * (𝒮) + (-1 : ℝ) * (𝒞) * (𝒮) := by linarith
  have k1h : (-2 : ℝ) + (3 : ℝ) * (𝒞) + ((3 : ℝ) / 2) * (𝒮) + (-1 : ℝ) * (𝒞) * (𝒮) ≤ ((416613 : ℝ) / 500000) := by linarith
  have k2l : ((1282143 : ℝ) / 500000) ≤ ((5 : ℝ) / 4) + (-1 : ℝ) * (𝒮) + (4 : ℝ) * (𝒞) * (𝒮) := by linarith
  have k2h : ((5 : ℝ) / 4) + (-1 : ℝ) * (𝒮) + (4 : ℝ) * (𝒞) * (𝒮) ≤ ((64109 : ℝ) / 25000) := by linarith
  nlinarith [mul_nonneg (sub_nonneg.2 k1l) (sub_nonneg.2 hcl), mul_nonneg (sub_nonneg.2 k1h) (sub_nonneg.2 hch), mul_nonneg (sub_nonneg.2 k1l) (sub_nonneg.2 hch), mul_nonneg (sub_nonneg.2 k1h) (sub_nonneg.2 hcl), mul_nonneg (sub_nonneg.2 k2l) (sub_nonneg.2 hsl), mul_nonneg (sub_nonneg.2 k2h) (sub_nonneg.2 hsh), mul_nonneg (sub_nonneg.2 k2l) (sub_nonneg.2 hsh), mul_nonneg (sub_nonneg.2 k2h) (sub_nonneg.2 hsl)]

lemma pos_R1_pM2 (c s : ℝ) (hcl : ((111 : ℝ) / 125) ≤ c) (hch : c ≤ (1 : ℝ)) (hsl : ((-189 : ℝ) / 400) ≤ s) (hsh : s ≤ (0 : ℝ)) :
    (0:ℝ) ≤ ((5 : ℝ) / 4) + ((5 : ℝ) / 4) * (𝒞) + (5 : ℝ) * (𝒞) * (𝒮) := by
  have hSC := hSC'; have hC2 := hC2'
  obtain ⟨hCl, hCh⟩ := C_bnd; obtain ⟨hSl, hSh⟩ := S_bnd; obtain ⟨hPl, hPh⟩ := P_bnd
  have e : ((5 : ℝ) / 4) + ((5 : ℝ) / 4) * (𝒞) + (5 : ℝ) * (𝒞) * (𝒮) = ((5 : ℝ) / 4) + ((5 : ℝ) / 4) * (𝒞) + (5 : ℝ) * (𝒞) * (𝒮) := by
    linear_combination ((0 : ℝ)) * hSC + ((0 : ℝ)) * hC2
  rw [e]
  have k0 : ((1855543 : ℝ) / 400000) ≤ ((5 : ℝ) / 4) + ((5 : ℝ) / 4) * (𝒞) + (5 : ℝ) * (𝒞) * (𝒮) := by linarith
  have k1l : (0 : ℝ) ≤ (0 : ℝ) := by linarith
  have k1h : (0 : ℝ) ≤ (0 : ℝ) := by linarith
  have k2l : (0 : ℝ) ≤ (0 : ℝ) := by linarith
  have k2h : (0 : ℝ) ≤ (0 : ℝ) := by linarith
  nlinarith [mul_nonneg (sub_nonneg.2 k1l) (sub_nonneg.2 hcl), mul_nonneg (sub_nonneg.2 k1h) (sub_nonneg.2 hch), mul_nonneg (sub_nonneg.2 k1l) (sub_nonneg.2 hch), mul_nonneg (sub_nonneg.2 k1h) (sub_nonneg.2 hcl), mul_nonneg (sub_nonneg.2 k2l) (sub_nonneg.2 hsl), mul_nonneg (sub_nonneg.2 k2h) (sub_nonneg.2 hsh), mul_nonneg (sub_nonneg.2 k2l) (sub_nonneg.2 hsh), mul_nonneg (sub_nonneg.2 k2h) (sub_nonneg.2 hsl)]

lemma pos_R2_pA1 (c s : ℝ) (hcl : ((19 : ℝ) / 20) ≤ c) (hch : c ≤ (1 : ℝ)) (hsl : (0 : ℝ) ≤ s) (hsh : s ≤ ((1571 : ℝ) / 5000)) :
    (0:ℝ) < (-1 : ℝ) * (𝒞) ^ 2 + (-3 : ℝ) * (𝒞) + (2 : ℝ) * (𝒞) ^ 3 + (1 : ℝ) * (𝒞) * (c) + (1 : ℝ) * (𝒮) * (c) + (1 : ℝ) * (c) * (𝒞) ^ 2 + (1 : ℝ) * (s) * (𝒮) ^ 2 + (1 : ℝ) * (𝒞) * (𝒮) * (c) + (1 : ℝ) * (𝒞) * (𝒮) * (s) := by
  have hSC := hSC'; have hC2 := hC2'
  obtain ⟨hCl, hCh⟩ := C_bnd; obtain ⟨hSl, hSh⟩ := S_bnd; obtain ⟨hPl, hPh⟩ := P_bnd
  have e : (-1 : ℝ) * (𝒞) ^ 2 + (-3 : ℝ) * (𝒞) + (2 : ℝ) * (𝒞) ^ 3 + (1 : ℝ) * (𝒞) * (c) + (1 : ℝ) * (𝒮) * (c) + (1 : ℝ) * (c) * (𝒞) ^ 2 + (1 : ℝ) * (s) * (𝒮) ^ 2 + (1 : ℝ) * (𝒞) * (𝒮) * (c) + (1 : ℝ) * (𝒞) * (𝒮) * (s) = ((-5 : ℝ) / 2) * (𝒞) + ((1 : ℝ) / 4) * (c) + ((3 : ℝ) / 4) * (s) + (1 : ℝ) * (𝒮) * (c) + ((-1 : ℝ) / 2) * (𝒞) * (s) + ((3 : ℝ) / 2) * (𝒞) * (c) + (1 : ℝ) * (𝒞) * (𝒮) * (c) + (1 : ℝ) * (𝒞) * (𝒮) * (s) := by
    linear_combination ((1 : ℝ) * (s)) * hSC + (((1 : ℝ) / 2) * (𝒞) + ((-1 : ℝ) / 4) * (s) + ((1 : ℝ) / 4) * (c)) * hC2
  rw [e]
  have k0 : ((-40451 : ℝ) / 20000) ≤ ((-5 : ℝ) / 2) * (𝒞) := by linarith
  have k1l : ((1263407 : ℝ) / 500000) ≤ ((1 : ℝ) / 4) + (1 : ℝ) * (𝒮) + ((3 : ℝ) / 2) * (𝒞) + (1 : ℝ) * (𝒞) * (𝒮) := by linarith
  have k1h : ((1 : ℝ) / 4) + (1 : ℝ) * (𝒮) + ((3 : ℝ) / 2) * (𝒞) + (1 : ℝ) * (𝒞) * (𝒮) ≤ ((505371 : ℝ) / 200000) := by linarith
  have k2l : ((821009 : ℝ) / 1000000) ≤ ((3 : ℝ) / 4) + ((-1 : ℝ) / 2) * (𝒞) + (1 : ℝ) * (𝒞) * (𝒮) := by linarith
  have k2h : ((3 : ℝ) / 4) + ((-1 : ℝ) / 2) * (𝒞) + (1 : ℝ) * (𝒞) * (𝒮) ≤ ((82103 : ℝ) / 100000) := by linarith
  nlinarith [mul_nonneg (sub_nonneg.2 k1l) (sub_nonneg.2 hcl), mul_nonneg (sub_nonneg.2 k1h) (sub_nonneg.2 hch), mul_nonneg (sub_nonneg.2 k1l) (sub_nonneg.2 hch), mul_nonneg (sub_nonneg.2 k1h) (sub_nonneg.2 hcl), mul_nonneg (sub_nonneg.2 k2l) (sub_nonneg.2 hsl), mul_nonneg (sub_nonneg.2 k2h) (sub_nonneg.2 hsh), mul_nonneg (sub_nonneg.2 k2l) (sub_nonneg.2 hsh), mul_nonneg (sub_nonneg.2 k2h) (sub_nonneg.2 hsl)]

lemma pos_R2_pB2 (c s : ℝ) (hcl : ((19 : ℝ) / 20) ≤ c) (hch : c ≤ (1 : ℝ)) (hsl : (0 : ℝ) ≤ s) (hsh : s ≤ ((1571 : ℝ) / 5000)) :
    (0:ℝ) ≤ (-1 : ℝ) * (𝒞) ^ 2 + (-3 : ℝ) * (𝒞) + (2 : ℝ) * (𝒞) ^ 3 + (4 : ℝ) * (𝒞) * (c) * (𝒮) ^ 2 + (4 : ℝ) * (𝒮) * (c) * (𝒞) ^ 2 := by
  have hSC := hSC'; have hC2 := hC2'
  obtain ⟨hCl, hCh⟩ := C_bnd; obtain ⟨hSl, hSh⟩ := S_bnd; obtain ⟨hPl, hPh⟩ := P_bnd
  have e : (-1 : ℝ) * (𝒞) ^ 2 + (-3 : ℝ) * (𝒞) + (2 : ℝ) * (𝒞) ^ 3 + (4 : ℝ) * (𝒞) * (c) * (𝒮) ^ 2 + (4 : ℝ) * (𝒮) * (c) * (𝒞) ^ 2 = ((-5 : ℝ) / 2) * (𝒞) + ((-1 : ℝ) / 2) * (c) + (1 : ℝ) * (𝒮) * (c) + (2 : ℝ) * (𝒞) * (c) + (2 : ℝ) * (𝒞) * (𝒮) * (c) := by
    linear_combination ((4 : ℝ) * (𝒞) * (c)) * hSC + (((1 : ℝ) / 2) * (𝒞) + ((-1 : ℝ) / 2) * (c) + (1 : ℝ) * (𝒮) * (c) + (-1 : ℝ) * (𝒞) * (c)) * hC2
  rw [e]
  have k0 : ((-40451 : ℝ) / 20000) ≤ ((-5 : ℝ) / 2) * (𝒞) := by linarith
  have k1l : ((1328419 : ℝ) / 500000) ≤ ((-1 : ℝ) / 2) + (1 : ℝ) * (𝒮) + (2 : ℝ) * (𝒞) + (2 : ℝ) * (𝒞) * (𝒮) := by linarith
  have k1h : ((-1 : ℝ) / 2) + (1 : ℝ) * (𝒮) + (2 : ℝ) * (𝒞) + (2 : ℝ) * (𝒞) * (𝒮) ≤ ((26569 : ℝ) / 10000) := by linarith
  have k2l : (0 : ℝ) ≤ (0 : ℝ) := by linarith
  have k2h : (0 : ℝ) ≤ (0 : ℝ) := by linarith
  nlinarith [mul_nonneg (sub_nonneg.2 k1l) (sub_nonneg.2 hcl), mul_nonneg (sub_nonneg.2 k1h) (sub_nonneg.2 hch), mul_nonneg (sub_nonneg.2 k1l) (sub_nonneg.2 hch), mul_nonneg (sub_nonneg.2 k1h) (sub_nonneg.2 hcl), mul_nonneg (sub_nonneg.2 k2l) (sub_nonneg.2 hsl), mul_nonneg (sub_nonneg.2 k2h) (sub_nonneg.2 hsh), mul_nonneg (sub_nonneg.2 k2l) (sub_nonneg.2 hsh), mul_nonneg (sub_nonneg.2 k2h) (sub_nonneg.2 hsl)]

lemma pos_R2_pM1 (c s : ℝ) (hcl : ((19 : ℝ) / 20) ≤ c) (hch : c ≤ (1 : ℝ)) (hsl : (0 : ℝ) ≤ s) (hsh : s ≤ ((1571 : ℝ) / 5000)) :
    (0:ℝ) ≤ (2 : ℝ) + (-3 : ℝ) * (𝒞) + (-3 : ℝ) * (𝒮) + ((-1 : ℝ) / 2) * (s) + ((13 : ℝ) / 4) * (c) + (1 : ℝ) * (𝒮) * (s) + (2 : ℝ) * (𝒞) * (𝒮) + (2 : ℝ) * (𝒞) * (s) + (2 : ℝ) * (𝒮) * (c) + ((9 : ℝ) / 2) * (𝒞) * (c) + (1 : ℝ) * (𝒞) * (𝒮) * (s) + (12 : ℝ) * (𝒞) * (𝒮) * (c) := by
  have hSC := hSC'; have hC2 := hC2'
  obtain ⟨hCl, hCh⟩ := C_bnd; obtain ⟨hSl, hSh⟩ := S_bnd; obtain ⟨hPl, hPh⟩ := P_bnd
  have e : (2 : ℝ) + (-3 : ℝ) * (𝒞) + (-3 : ℝ) * (𝒮) + ((-1 : ℝ) / 2) * (s) + ((13 : ℝ) / 4) * (c) + (1 : ℝ) * (𝒮) * (s) + (2 : ℝ) * (𝒞) * (𝒮) + (2 : ℝ) * (𝒞) * (s) + (2 : ℝ) * (𝒮) * (c) + ((9 : ℝ) / 2) * (𝒞) * (c) + (1 : ℝ) * (𝒞) * (𝒮) * (s) + (12 : ℝ) * (𝒞) * (𝒮) * (c) = (2 : ℝ) + (-3 : ℝ) * (𝒞) + (-3 : ℝ) * (𝒮) + ((-1 : ℝ) / 2) * (s) + ((13 : ℝ) / 4) * (c) + (1 : ℝ) * (𝒮) * (s) + (2 : ℝ) * (𝒞) * (𝒮) + (2 : ℝ) * (𝒞) * (s) + (2 : ℝ) * (𝒮) * (c) + ((9 : ℝ) / 2) * (𝒞) * (c) + (1 : ℝ) * (𝒞) * (𝒮) * (s) + (12 : ℝ) * (𝒞) * (𝒮) * (c) := by
    linear_combination ((0 : ℝ)) * hSC + ((0 : ℝ)) * hC2
  rw [e]
  have k0 : ((-38731 : ℝ) / 31250) ≤ (2 : ℝ) + (-3 : ℝ) * (𝒞) + (-3 : ℝ) * (𝒮) + (2 : ℝ) * (𝒞) * (𝒮) := by linarith
  have k1l : ((13772333 : ℝ) / 1000000) ≤ ((13 : ℝ) / 4) + (2 : ℝ) * (𝒮) + ((9 : ℝ) / 2) * (𝒞) + (12 : ℝ) * (𝒞) * (𝒮) := by linarith
  have k1h : ((13 : ℝ) / 4) + (2 : ℝ) * (𝒮) + ((9 : ℝ) / 2) * (𝒞) + (12 : ℝ) * (𝒞) * (𝒮) ≤ ((1377259 : ℝ) / 100000) := by linarith
  have k2l : ((2181319 : ℝ) / 1000000) ≤ ((-1 : ℝ) / 2) + (1 : ℝ) * (𝒮) + (2 : ℝ) * (𝒞) + (1 : ℝ) * (𝒞) * (𝒮) := by linarith
  have k2h : ((-1 : ℝ) / 2) + (1 : ℝ) * (𝒮) + (2 : ℝ) * (𝒞) + (1 : ℝ) * (𝒞) * (𝒮) ≤ ((436273 : ℝ) / 200000) := by linarith
  nlinarith [mul_nonneg (sub_nonneg.2 k1l) (sub_nonneg.2 hcl), mul_nonneg (sub_nonneg.2 k1h) (sub_nonneg.2 hch), mul_nonneg (sub_nonneg.2 k1l) (sub_nonneg.2 hch), mul_nonneg (sub_nonneg.2 k1h) (sub_nonneg.2 hcl), mul_nonneg (sub_nonneg.2 k2l) (sub_nonneg.2 hsl), mul_nonneg (sub_nonneg.2 k2h) (sub_nonneg.2 hsh), mul_nonneg (sub_nonneg.2 k2l) (sub_nonneg.2 hsh), mul_nonneg (sub_nonneg.2 k2h) (sub_nonneg.2 hsl)]

lemma L_nonpos (ψ : ℝ) (hlo : 0 ≤ ψ) (hhi : ψ ≤ π / 10) : (-1 : ℝ) + (1 : ℝ) * (cos ψ) + (-1 : ℝ) * (sin ψ) + (2 : ℝ) * (𝒞) ^ 2 + (-2 : ℝ) * (cos ψ) * (𝒞) ^ 2 + (2 : ℝ) * (𝒞) * (𝒮) * (sin ψ) ≤ 0 := by
  have hsl : 0 ≤ sin ψ := sin_nonneg_of_nonneg_of_le_pi hlo (by linarith [pi_gt_three])
  have hch : cos ψ ≤ 1 := cos_le_one ψ
  have e1 := sin_add (π / 10 - ψ) ψ
  rw [show π / 10 - ψ + ψ = π / 10 by ring, sin_sub, cos_sub, tab_s_18, tab_c_18] at e1
  have q1 : 0 ≤ sin (π / 10 - ψ) := sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith [pi_gt_three])
  rw [sin_sub, tab_s_18, tab_c_18] at q1
  have q2 : cos (π / 10 - ψ) ≤ 1 := cos_le_one _
  rw [cos_sub, tab_s_18, tab_c_18] at q2
  nlinarith [mul_nonneg q1 (sub_nonneg.2 hch), mul_nonneg hsl (sub_nonneg.2 q2)]

lemma pos_R3_pA1 (c s : ℝ) (hcl : ((111 : ℝ) / 125) ≤ c) (hch : c ≤ (1 : ℝ)) (hsl : (0 : ℝ) ≤ s) (hsh : s ≤ ((189 : ℝ) / 400)) :
    (0:ℝ) < (-1 : ℝ) * (𝒞) ^ 2 + (-3 : ℝ) * (𝒞) + (2 : ℝ) * (𝒞) ^ 3 + (4 : ℝ) * (𝒞) * (c) * (𝒮) ^ 2 + (4 : ℝ) * (𝒮) * (c) * (𝒞) ^ 2 := by
  have hSC := hSC'; have hC2 := hC2'
  obtain ⟨hCl, hCh⟩ := C_bnd; obtain ⟨hSl, hSh⟩ := S_bnd; obtain ⟨hPl, hPh⟩ := P_bnd
  have e : (-1 : ℝ) * (𝒞) ^ 2 + (-3 : ℝ) * (𝒞) + (2 : ℝ) * (𝒞) ^ 3 + (4 : ℝ) * (𝒞) * (c) * (𝒮) ^ 2 + (4 : ℝ) * (𝒮) * (c) * (𝒞) ^ 2 = ((-5 : ℝ) / 2) * (𝒞) + ((-1 : ℝ) / 2) * (c) + (1 : ℝ) * (𝒮) * (c) + (2 : ℝ) * (𝒞) * (c) + (2 : ℝ) * (𝒞) * (𝒮) * (c) := by
    linear_combination ((4 : ℝ) * (𝒞) * (c)) * hSC + (((1 : ℝ) / 2) * (𝒞) + ((-1 : ℝ) / 2) * (c) + (1 : ℝ) * (𝒮) * (c) + (-1 : ℝ) * (𝒞) * (c)) * hC2
  rw [e]
  have k0 : ((-40451 : ℝ) / 20000) ≤ ((-5 : ℝ) / 2) * (𝒞) := by linarith
  have k1l : ((1328419 : ℝ) / 500000) ≤ ((-1 : ℝ) / 2) + (1 : ℝ) * (𝒮) + (2 : ℝ) * (𝒞) + (2 : ℝ) * (𝒞) * (𝒮) := by linarith
  have k1h : ((-1 : ℝ) / 2) + (1 : ℝ) * (𝒮) + (2 : ℝ) * (𝒞) + (2 : ℝ) * (𝒞) * (𝒮) ≤ ((26569 : ℝ) / 10000) := by linarith
  have k2l : (0 : ℝ) ≤ (0 : ℝ) := by linarith
  have k2h : (0 : ℝ) ≤ (0 : ℝ) := by linarith
  nlinarith [mul_nonneg (sub_nonneg.2 k1l) (sub_nonneg.2 hcl), mul_nonneg (sub_nonneg.2 k1h) (sub_nonneg.2 hch), mul_nonneg (sub_nonneg.2 k1l) (sub_nonneg.2 hch), mul_nonneg (sub_nonneg.2 k1h) (sub_nonneg.2 hcl), mul_nonneg (sub_nonneg.2 k2l) (sub_nonneg.2 hsl), mul_nonneg (sub_nonneg.2 k2h) (sub_nonneg.2 hsh), mul_nonneg (sub_nonneg.2 k2l) (sub_nonneg.2 hsh), mul_nonneg (sub_nonneg.2 k2h) (sub_nonneg.2 hsl)]

lemma pos_R3_pB2 (c s : ℝ) (hcl : ((111 : ℝ) / 125) ≤ c) (hch : c ≤ (1 : ℝ)) (hsl : (0 : ℝ) ≤ s) (hsh : s ≤ ((189 : ℝ) / 400)) :
    (0:ℝ) ≤ (-1 : ℝ) * (𝒞) ^ 2 + (-3 : ℝ) * (𝒞) + (2 : ℝ) * (𝒞) ^ 3 + (1 : ℝ) * (𝒞) * (c) + (1 : ℝ) * (𝒮) * (c) + (1 : ℝ) * (c) * (𝒞) ^ 2 + (1 : ℝ) * (s) * (𝒮) ^ 2 + (1 : ℝ) * (𝒞) * (𝒮) * (c) + (1 : ℝ) * (𝒞) * (𝒮) * (s) := by
  have hSC := hSC'; have hC2 := hC2'
  obtain ⟨hCl, hCh⟩ := C_bnd; obtain ⟨hSl, hSh⟩ := S_bnd; obtain ⟨hPl, hPh⟩ := P_bnd
  have e : (-1 : ℝ) * (𝒞) ^ 2 + (-3 : ℝ) * (𝒞) + (2 : ℝ) * (𝒞) ^ 3 + (1 : ℝ) * (𝒞) * (c) + (1 : ℝ) * (𝒮) * (c) + (1 : ℝ) * (c) * (𝒞) ^ 2 + (1 : ℝ) * (s) * (𝒮) ^ 2 + (1 : ℝ) * (𝒞) * (𝒮) * (c) + (1 : ℝ) * (𝒞) * (𝒮) * (s) = ((-5 : ℝ) / 2) * (𝒞) + ((1 : ℝ) / 4) * (c) + ((3 : ℝ) / 4) * (s) + (1 : ℝ) * (𝒮) * (c) + ((-1 : ℝ) / 2) * (𝒞) * (s) + ((3 : ℝ) / 2) * (𝒞) * (c) + (1 : ℝ) * (𝒞) * (𝒮) * (c) + (1 : ℝ) * (𝒞) * (𝒮) * (s) := by
    linear_combination ((1 : ℝ) * (s)) * hSC + (((1 : ℝ) / 2) * (𝒞) + ((-1 : ℝ) / 4) * (s) + ((1 : ℝ) / 4) * (c)) * hC2
  rw [e]
  have k0 : ((-40451 : ℝ) / 20000) ≤ ((-5 : ℝ) / 2) * (𝒞) := by linarith
  have k1l : ((1263407 : ℝ) / 500000) ≤ ((1 : ℝ) / 4) + (1 : ℝ) * (𝒮) + ((3 : ℝ) / 2) * (𝒞) + (1 : ℝ) * (𝒞) * (𝒮) := by linarith
  have k1h : ((1 : ℝ) / 4) + (1 : ℝ) * (𝒮) + ((3 : ℝ) / 2) * (𝒞) + (1 : ℝ) * (𝒞) * (𝒮) ≤ ((505371 : ℝ) / 200000) := by linarith
  have k2l : ((821009 : ℝ) / 1000000) ≤ ((3 : ℝ) / 4) + ((-1 : ℝ) / 2) * (𝒞) + (1 : ℝ) * (𝒞) * (𝒮) := by linarith
  have k2h : ((3 : ℝ) / 4) + ((-1 : ℝ) / 2) * (𝒞) + (1 : ℝ) * (𝒞) * (𝒮) ≤ ((82103 : ℝ) / 100000) := by linarith
  nlinarith [mul_nonneg (sub_nonneg.2 k1l) (sub_nonneg.2 hcl), mul_nonneg (sub_nonneg.2 k1h) (sub_nonneg.2 hch), mul_nonneg (sub_nonneg.2 k1l) (sub_nonneg.2 hch), mul_nonneg (sub_nonneg.2 k1h) (sub_nonneg.2 hcl), mul_nonneg (sub_nonneg.2 k2l) (sub_nonneg.2 hsl), mul_nonneg (sub_nonneg.2 k2h) (sub_nonneg.2 hsh), mul_nonneg (sub_nonneg.2 k2l) (sub_nonneg.2 hsh), mul_nonneg (sub_nonneg.2 k2h) (sub_nonneg.2 hsl)]

lemma pos_R3_pM1 (c s : ℝ) (hcl : ((111 : ℝ) / 125) ≤ c) (hch : c ≤ (1 : ℝ)) (hsl : (0 : ℝ) ≤ s) (hsh : s ≤ ((189 : ℝ) / 400)) :
    (0:ℝ) ≤ (-2 : ℝ) * (c) + ((-5 : ℝ) / 4) * (s) + ((5 : ℝ) / 4) * (𝒮) + (1 : ℝ) * (𝒮) * (s) + (3 : ℝ) * (𝒞) * (c) + ((3 : ℝ) / 2) * (𝒮) * (c) + (-1 : ℝ) * (𝒞) * (𝒮) * (c) + (-4 : ℝ) * (𝒞) * (𝒮) * (s) := by
  have hSC := hSC'; have hC2 := hC2'
  obtain ⟨hCl, hCh⟩ := C_bnd; obtain ⟨hSl, hSh⟩ := S_bnd; obtain ⟨hPl, hPh⟩ := P_bnd
  have e : (-2 : ℝ) * (c) + ((-5 : ℝ) / 4) * (s) + ((5 : ℝ) / 4) * (𝒮) + (1 : ℝ) * (𝒮) * (s) + (3 : ℝ) * (𝒞) * (c) + ((3 : ℝ) / 2) * (𝒮) * (c) + (-1 : ℝ) * (𝒞) * (𝒮) * (c) + (-4 : ℝ) * (𝒞) * (𝒮) * (s) = (-2 : ℝ) * (c) + ((-5 : ℝ) / 4) * (s) + ((5 : ℝ) / 4) * (𝒮) + (1 : ℝ) * (𝒮) * (s) + (3 : ℝ) * (𝒞) * (c) + ((3 : ℝ) / 2) * (𝒮) * (c) + (-1 : ℝ) * (𝒞) * (𝒮) * (c) + (-4 : ℝ) * (𝒞) * (𝒮) * (s) := by
    linear_combination ((0 : ℝ)) * hSC + ((0 : ℝ)) * hC2
  rw [e]
  have k0 : ((29389 : ℝ) / 40000) ≤ ((5 : ℝ) / 4) * (𝒮) := by linarith
  have k1l : ((166633 : ℝ) / 200000) ≤ (-2 : ℝ) + (3 : ℝ) * (𝒞) + ((3 : ℝ) / 2) * (𝒮) + (-1 : ℝ) * (𝒞) * (𝒮) := by linarith
  have k1h : (-2 : ℝ) + (3 : ℝ) * (𝒞) + ((3 : ℝ) / 2) * (𝒮) + (-1 : ℝ) * (𝒞) * (𝒮) ≤ ((416613 : ℝ) / 500000) := by linarith
  have k2l : ((-64109 : ℝ) / 25000) ≤ ((-5 : ℝ) / 4) + (1 : ℝ) * (𝒮) + (-4 : ℝ) * (𝒞) * (𝒮) := by linarith
  have k2h : ((-5 : ℝ) / 4) + (1 : ℝ) * (𝒮) + (-4 : ℝ) * (𝒞) * (𝒮) ≤ ((-1282143 : ℝ) / 500000) := by linarith
  nlinarith [mul_nonneg (sub_nonneg.2 k1l) (sub_nonneg.2 hcl), mul_nonneg (sub_nonneg.2 k1h) (sub_nonneg.2 hch), mul_nonneg (sub_nonneg.2 k1l) (sub_nonneg.2 hch), mul_nonneg (sub_nonneg.2 k1h) (sub_nonneg.2 hcl), mul_nonneg (sub_nonneg.2 k2l) (sub_nonneg.2 hsl), mul_nonneg (sub_nonneg.2 k2h) (sub_nonneg.2 hsh), mul_nonneg (sub_nonneg.2 k2l) (sub_nonneg.2 hsh), mul_nonneg (sub_nonneg.2 k2h) (sub_nonneg.2 hsl)]

lemma pos_R3_pM2 (c s : ℝ) (hcl : ((111 : ℝ) / 125) ≤ c) (hch : c ≤ (1 : ℝ)) (hsl : (0 : ℝ) ≤ s) (hsh : s ≤ ((189 : ℝ) / 400)) :
    (0:ℝ) ≤ ((5 : ℝ) / 4) + ((5 : ℝ) / 4) * (𝒞) + (5 : ℝ) * (𝒞) * (𝒮) := by
  have hSC := hSC'; have hC2 := hC2'
  obtain ⟨hCl, hCh⟩ := C_bnd; obtain ⟨hSl, hSh⟩ := S_bnd; obtain ⟨hPl, hPh⟩ := P_bnd
  have e : ((5 : ℝ) / 4) + ((5 : ℝ) / 4) * (𝒞) + (5 : ℝ) * (𝒞) * (𝒮) = ((5 : ℝ) / 4) + ((5 : ℝ) / 4) * (𝒞) + (5 : ℝ) * (𝒞) * (𝒮) := by
    linear_combination ((0 : ℝ)) * hSC + ((0 : ℝ)) * hC2
  rw [e]
  have k0 : ((1855543 : ℝ) / 400000) ≤ ((5 : ℝ) / 4) + ((5 : ℝ) / 4) * (𝒞) + (5 : ℝ) * (𝒞) * (𝒮) := by linarith
  have k1l : (0 : ℝ) ≤ (0 : ℝ) := by linarith
  have k1h : (0 : ℝ) ≤ (0 : ℝ) := by linarith
  have k2l : (0 : ℝ) ≤ (0 : ℝ) := by linarith
  have k2h : (0 : ℝ) ≤ (0 : ℝ) := by linarith
  nlinarith [mul_nonneg (sub_nonneg.2 k1l) (sub_nonneg.2 hcl), mul_nonneg (sub_nonneg.2 k1h) (sub_nonneg.2 hch), mul_nonneg (sub_nonneg.2 k1l) (sub_nonneg.2 hch), mul_nonneg (sub_nonneg.2 k1h) (sub_nonneg.2 hcl), mul_nonneg (sub_nonneg.2 k2l) (sub_nonneg.2 hsl), mul_nonneg (sub_nonneg.2 k2h) (sub_nonneg.2 hsh), mul_nonneg (sub_nonneg.2 k2l) (sub_nonneg.2 hsh), mul_nonneg (sub_nonneg.2 k2h) (sub_nonneg.2 hsl)]

lemma region_R1 (a b ψ : ℝ) (hlo : -(3 * π / 20) ≤ ψ) (hhi : ψ ≤ 0)
    (Q : Set (ℝ × ℝ)) (hQ : Convex ℝ Q)
    (h0 : (a + circumradius * cos (ψ + 0), b + circumradius * sin (ψ + 0)) ∈ Q)
    (h1 : (a + circumradius * cos (ψ + 2 * π / 5), b + circumradius * sin (ψ + 2 * π / 5)) ∈ Q)
    (hx : 0 ≤ a + circumradius * cos (ψ + 6 * π / 5))
    (hy : 0 ≤ b + circumradius * sin (ψ + 8 * π / 5)) :
    ∃ p ∈ Q, sStar / 2 ≤ p.1 ∧ sStar / 2 ≤ p.2 := by
  have hS := S_pos; have hC := C_pos; have hSC := hSC'; have hC2 := hC2'
  obtain ⟨hCl, hCh⟩ := C_bnd; obtain ⟨hSl, hSh⟩ := S_bnd; obtain ⟨hPl, hPh⟩ := P_bnd
  have hcs : cos ψ ^ 2 + sin ψ ^ 2 = 1 := cos_sq_add_sin_sq ψ
  have hcl : (888/1000 : ℝ) ≤ cos ψ := by nlinarith [one_sub_sq_div_two_le_cos (x := ψ), pi_lt_d2, pi_gt_three]
  have hch : cos ψ ≤ 1 := cos_le_one ψ
  have hsl : (-4725/10000 : ℝ) ≤ sin ψ := by have := sin_le (x := -ψ) (by linarith); rw [sin_neg] at this; nlinarith [pi_lt_d2]
  have hsh : sin ψ ≤ 0 := by have := sin_nonneg_of_nonneg_of_le_pi (x := -ψ) (by linarith) (by linarith [pi_gt_three]); rw [sin_neg] at this; linarith
  have ec0 : circumradius * cos (ψ + 0) = (cos ψ * ((1 : ℝ)) - sin ψ * ((0 : ℝ))) / (2 * 𝒮) := by
    rw [cos_add, tab_c_0, tab_s_0]; unfold circumradius; ring
  have es0 : circumradius * sin (ψ + 0) = (sin ψ * ((1 : ℝ)) + cos ψ * ((0 : ℝ))) / (2 * 𝒮) := by
    rw [sin_add, tab_c_0, tab_s_0]; unfold circumradius; ring
  have ec1 : circumradius * cos (ψ + 2 * π / 5) = (cos ψ * ((-1 : ℝ) + (2 : ℝ) * (𝒞) ^ 2) - sin ψ * ((2 : ℝ) * (𝒞) * (𝒮))) / (2 * 𝒮) := by
    rw [cos_add, tab_c_72, tab_s_72]; unfold circumradius; ring
  have es1 : circumradius * sin (ψ + 2 * π / 5) = (sin ψ * ((-1 : ℝ) + (2 : ℝ) * (𝒞) ^ 2) + cos ψ * ((2 : ℝ) * (𝒞) * (𝒮))) / (2 * 𝒮) := by
    rw [sin_add, tab_c_72, tab_s_72]; unfold circumradius; ring
  have ec3 : circumradius * cos (ψ + 6 * π / 5) = (cos ψ * ((-1 : ℝ) * (𝒞)) - sin ψ * ((-1 : ℝ) * (𝒮))) / (2 * 𝒮) := by
    rw [cos_add, tab_c_216, tab_s_216]; unfold circumradius; ring
  have es3 : circumradius * sin (ψ + 6 * π / 5) = (sin ψ * ((-1 : ℝ) * (𝒞)) + cos ψ * ((-1 : ℝ) * (𝒮))) / (2 * 𝒮) := by
    rw [sin_add, tab_c_216, tab_s_216]; unfold circumradius; ring
  have ec4 : circumradius * cos (ψ + 8 * π / 5) = (cos ψ * ((-1 : ℝ) + (2 : ℝ) * (𝒞) ^ 2) - sin ψ * ((-2 : ℝ) * (𝒞) * (𝒮))) / (2 * 𝒮) := by
    rw [cos_add, tab_c_288, tab_s_288]; unfold circumradius; ring
  have es4 : circumradius * sin (ψ + 8 * π / 5) = (sin ψ * ((-1 : ℝ) + (2 : ℝ) * (𝒞) ^ 2) + cos ψ * ((-2 : ℝ) * (𝒞) * (𝒮))) / (2 * 𝒮) := by
    rw [sin_add, tab_c_288, tab_s_288]; unfold circumradius; ring
  have hcl' : ((111 : ℝ) / 125) ≤ cos ψ := by linarith
  have hch' : cos ψ ≤ (1 : ℝ) := by linarith
  have hsl' : ((-189 : ℝ) / 400) ≤ sin ψ := by linarith
  have hsh' : sin ψ ≤ (0 : ℝ) := by linarith
  rw [ec0, es0] at h0; rw [ec1, es1] at h1
  rw [ec3] at hx; rw [es4] at hy
  have hw : 0 < 2 * 𝒮 * (𝒮 + 𝒞) := by positivity
  have hT : sStar / 2 = (𝒞 * (3 + 𝒞 - 2 * 𝒞 ^ 2)) / (2 * 𝒮 * (𝒮 + 𝒞)) := by unfold sStar; field_simp; try ring
  obtain ⟨A1n, hA1n⟩ : ∃ X : ℝ, X = (-1 : ℝ) * (𝒞) ^ 2 + (-3 : ℝ) * (𝒞) + (2 : ℝ) * (𝒞) ^ 3 + (1 : ℝ) * (𝒞) * (cos ψ) + (1 : ℝ) * (𝒮) * (cos ψ) + (1 : ℝ) * (cos ψ) * (𝒞) ^ 2 + (-1 : ℝ) * (sin ψ) * (𝒮) ^ 2 + (1 : ℝ) * (𝒞) * (𝒮) * (cos ψ) + (-1 : ℝ) * (𝒞) * (𝒮) * (sin ψ) := ⟨_, rfl⟩
  obtain ⟨A2n, hA2n⟩ : ∃ X : ℝ, X = (-1 : ℝ) * (𝒞) ^ 2 + (-3 : ℝ) * (𝒞) + (2 : ℝ) * (𝒞) ^ 3 + (1 : ℝ) * (cos ψ) * (𝒞) ^ 2 + (-1 : ℝ) * (𝒞) * (cos ψ) + (-1 : ℝ) * (𝒮) * (cos ψ) + (-1 : ℝ) * (sin ψ) * (𝒮) ^ 2 + (2 : ℝ) * (cos ψ) * (𝒞) ^ 3 + (1 : ℝ) * (𝒞) * (𝒮) * (cos ψ) + (-1 : ℝ) * (𝒞) * (𝒮) * (sin ψ) + (-2 : ℝ) * (𝒞) * (sin ψ) * (𝒮) ^ 2 + (-2 : ℝ) * (𝒮) * (sin ψ) * (𝒞) ^ 2 + (2 : ℝ) * (𝒮) * (cos ψ) * (𝒞) ^ 2 := ⟨_, rfl⟩
  obtain ⟨B1n, hB1n⟩ : ∃ X : ℝ, X = (-1 : ℝ) * (𝒞) ^ 2 + (-3 : ℝ) * (𝒞) + (2 : ℝ) * (𝒞) ^ 3 + (-2 : ℝ) * (sin ψ) * (𝒞) ^ 3 + (2 : ℝ) * (𝒞) * (sin ψ) + (2 : ℝ) * (𝒮) * (sin ψ) + (-2 : ℝ) * (𝒮) * (sin ψ) * (𝒞) ^ 2 + (2 : ℝ) * (𝒞) * (cos ψ) * (𝒮) ^ 2 + (2 : ℝ) * (𝒮) * (cos ψ) * (𝒞) ^ 2 := ⟨_, rfl⟩
  obtain ⟨B2n, hB2n⟩ : ∃ X : ℝ, X = (-1 : ℝ) * (𝒞) ^ 2 + (-3 : ℝ) * (𝒞) + (2 : ℝ) * (𝒞) ^ 3 + (4 : ℝ) * (𝒞) * (cos ψ) * (𝒮) ^ 2 + (4 : ℝ) * (𝒮) * (cos ψ) * (𝒞) ^ 2 := ⟨_, rfl⟩
  have iA1n : ((cos ψ * ((1 : ℝ)) - sin ψ * ((0 : ℝ))) / (2 * 𝒮)) - ((cos ψ * ((-1 : ℝ) * (𝒞)) - sin ψ * ((-1 : ℝ) * (𝒮))) / (2 * 𝒮)) - sStar / 2 = A1n / (2 * 𝒮 * (𝒮 + 𝒞)) := by
    rw [hT, hA1n]; field_simp; ring
  have iA2n : ((cos ψ * ((-1 : ℝ) + (2 : ℝ) * (𝒞) ^ 2) - sin ψ * ((2 : ℝ) * (𝒞) * (𝒮))) / (2 * 𝒮)) - ((cos ψ * ((-1 : ℝ) * (𝒞)) - sin ψ * ((-1 : ℝ) * (𝒮))) / (2 * 𝒮)) - sStar / 2 = A2n / (2 * 𝒮 * (𝒮 + 𝒞)) := by
    rw [hT, hA2n]; field_simp; ring
  have iB1n : ((sin ψ * ((1 : ℝ)) + cos ψ * ((0 : ℝ))) / (2 * 𝒮)) - ((sin ψ * ((-1 : ℝ) + (2 : ℝ) * (𝒞) ^ 2) + cos ψ * ((-2 : ℝ) * (𝒞) * (𝒮))) / (2 * 𝒮)) - sStar / 2 = B1n / (2 * 𝒮 * (𝒮 + 𝒞)) := by
    rw [hT, hB1n]; field_simp; ring
  have iB2n : ((sin ψ * ((-1 : ℝ) + (2 : ℝ) * (𝒞) ^ 2) + cos ψ * ((2 : ℝ) * (𝒞) * (𝒮))) / (2 * 𝒮)) - ((sin ψ * ((-1 : ℝ) + (2 : ℝ) * (𝒞) ^ 2) + cos ψ * ((-2 : ℝ) * (𝒞) * (𝒮))) / (2 * 𝒮)) - sStar / 2 = B2n / (2 * 𝒮 * (𝒮 + 𝒞)) := by
    rw [hT, hB2n]; field_simp; ring
  have pA1 := pos_R1_pA1 (cos ψ) (sin ψ) hcl' hch' hsl' hsh'
  have pB2 := pos_R1_pB2 (cos ψ) (sin ψ) hcl' hch' hsl' hsh'
  rw [← hA1n] at pA1; rw [← hB2n] at pB2
  have pM1 := pos_R1_pM1 (cos ψ) (sin ψ) hcl' hch' hsl' hsh'
  have pM2 := pos_R1_pM2 (cos ψ) (sin ψ) hcl' hch' hsl' hsh'
  have hD : A1n * B2n - A2n * B1n = (-sin ψ) * ((-2 : ℝ) * (cos ψ) + ((5 : ℝ) / 4) * (𝒮) + ((5 : ℝ) / 4) * (sin ψ) + (-1 : ℝ) * (𝒮) * (sin ψ) + (3 : ℝ) * (𝒞) * (cos ψ) + ((3 : ℝ) / 2) * (𝒮) * (cos ψ) + (-1 : ℝ) * (𝒞) * (𝒮) * (cos ψ) + (4 : ℝ) * (𝒞) * (𝒮) * (sin ψ)) + (1 - cos ψ) * (((5 : ℝ) / 4) + ((5 : ℝ) / 4) * (𝒞) + (5 : ℝ) * (𝒞) * (𝒮)) := by
    rw [hA1n, hA2n, hB1n, hB2n]
    linear_combination (((5 : ℝ) / 4) + ((5 : ℝ) / 4) * (𝒞) + (5 : ℝ) * (𝒞) * (𝒮)) * hcs + ((-8 : ℝ) * (𝒞) ^ 4 * (cos ψ) ^ 2 + (-8 : ℝ) * (𝒞) ^ 4 * (sin ψ) ^ 2 + (-6 : ℝ) * (cos ψ) * (𝒞) ^ 2 + (-6 : ℝ) * (sin ψ) * (𝒞) ^ 2 + (-4 : ℝ) * (𝒞) ^ 3 * (sin ψ) ^ 2 + (-2 : ℝ) * (cos ψ) * (𝒞) ^ 3 + (-2 : ℝ) * (sin ψ) * (𝒞) ^ 3 + (2 : ℝ) * (𝒮) * (sin ψ) ^ 2 + (2 : ℝ) * (cos ψ) * (sin ψ) + (4 : ℝ) * (𝒞) * (sin ψ) ^ 2 + (4 : ℝ) * (cos ψ) * (𝒞) ^ 4 + (4 : ℝ) * (sin ψ) * (𝒞) ^ 4 + (4 : ℝ) * (𝒞) ^ 3 * (cos ψ) ^ 2 + (8 : ℝ) * (𝒞) ^ 2 * (sin ψ) ^ 2 + (12 : ℝ) * (𝒞) ^ 2 * (cos ψ) ^ 2 + (-4 : ℝ) * (𝒮) * (𝒞) ^ 3 * (cos ψ) ^ 2 + (-4 : ℝ) * (𝒮) * (𝒞) ^ 3 * (sin ψ) ^ 2 + (-2 : ℝ) * (𝒮) * (𝒞) ^ 2 * (sin ψ) ^ 2 + (-2 : ℝ) * (cos ψ) * (sin ψ) * (𝒞) ^ 2 + (-2 : ℝ) * (cos ψ) * (sin ψ) * (𝒞) ^ 3 + (2 : ℝ) * (𝒮) * (𝒞) ^ 2 * (cos ψ) ^ 2 + (4 : ℝ) * (𝒞) * (𝒮) * (sin ψ) ^ 2 + (6 : ℝ) * (𝒞) * (𝒮) * (cos ψ) ^ 2 + (8 : ℝ) * (cos ψ) * (sin ψ) * (𝒞) ^ 4 + ((-7 : ℝ) / 2) * (𝒞) * (cos ψ) * (sin ψ) + (-4 : ℝ) * (𝒮) * (cos ψ) * (sin ψ) * (𝒞) ^ 2 + (-2 : ℝ) * (𝒞) * (cos ψ) * (sin ψ) * (𝒮) ^ 2 + (4 : ℝ) * (cos ψ) * (sin ψ) * (𝒞) ^ 2 * (𝒮) ^ 2 + (8 : ℝ) * (𝒮) * (cos ψ) * (sin ψ) * (𝒞) ^ 3) * hSC + (((-5 : ℝ) / 4) * (cos ψ) + ((5 : ℝ) / 4) * (cos ψ) ^ 2 + (-1 : ℝ) * (𝒮) * (sin ψ) ^ 2 + (-2 : ℝ) * (cos ψ) * (𝒞) ^ 4 + (2 : ℝ) * (𝒞) ^ 3 * (sin ψ) ^ 2 + (2 : ℝ) * (𝒞) ^ 4 * (cos ψ) ^ 2 + (2 : ℝ) * (𝒞) ^ 4 * (sin ψ) ^ 2 + ((-11 : ℝ) / 4) * (𝒞) * (sin ψ) ^ 2 + ((-9 : ℝ) / 2) * (𝒞) ^ 2 * (cos ψ) ^ 2 + ((-5 : ℝ) / 2) * (𝒞) ^ 2 * (sin ψ) ^ 2 + ((-5 : ℝ) / 4) * (𝒞) * (cos ψ) ^ 2 + ((-5 : ℝ) / 4) * (𝒮) * (sin ψ) + ((5 : ℝ) / 4) * (𝒞) * (cos ψ) + ((9 : ℝ) / 2) * (cos ψ) * (𝒞) ^ 2 + (1 : ℝ) * (𝒞) * (𝒮) * (cos ψ) + (1 : ℝ) * (cos ψ) * (sin ψ) * (𝒞) ^ 2 + ((1 : ℝ) / 2) * (𝒞) * (cos ψ) * (sin ψ) + ((1 : ℝ) / 2) * (cos ψ) * (sin ψ) * (𝒞) ^ 3 + (-1 : ℝ) * (𝒞) * (𝒮) * (cos ψ) ^ 2 + (-1 : ℝ) * (𝒞) * (𝒮) * (sin ψ) ^ 2 + (-1 : ℝ) * (cos ψ) * (sin ψ) * (𝒞) ^ 4 + (2 : ℝ) * (𝒮) * (sin ψ) * (𝒞) ^ 3 + ((-7 : ℝ) / 2) * (𝒞) * (𝒮) * (sin ψ) + ((-3 : ℝ) / 2) * (𝒮) * (cos ψ) * (sin ψ) + ((1 : ℝ) / 2) * (𝒞) * (cos ψ) * (sin ψ) * (𝒮) ^ 2 + (-1 : ℝ) * (cos ψ) * (sin ψ) * (𝒞) ^ 2 * (𝒮) ^ 2 + (2 : ℝ) * (𝒮) * (cos ψ) * (sin ψ) * (𝒞) ^ 2) * hC2
  have pD : 0 ≤ A1n * B2n - A2n * B1n := by rw [hD]; exact add_nonneg (mul_nonneg (neg_nonneg.2 hsh) pM1) (mul_nonneg (sub_nonneg.2 hch) pM2)
  rcases le_or_gt 0 A2n with hA2 | hA2
  · refine ⟨_, h1, ?_, ?_⟩
    · have := iA2n; have : 0 ≤ A2n / (2 * 𝒮 * (𝒮 + 𝒞)) := div_nonneg hA2 hw.le
      simp only; linarith
    · have := iB2n; have : 0 ≤ B2n / (2 * 𝒮 * (𝒮 + 𝒞)) := div_nonneg pB2 hw.le
      simp only; linarith
  · have hd : 0 < A1n - A2n := by linarith
    set lam := -A2n / (A1n - A2n) with hlam
    have hl0 : 0 ≤ lam := div_nonneg (by linarith) hd.le
    have hl1 : 0 ≤ 1 - lam := by rw [hlam, one_sub_div hd.ne']; exact div_nonneg (by linarith) hd.le
    refine ⟨lam • _ + (1 - lam) • _, hQ h0 h1 hl0 hl1 (by ring), ?_, ?_⟩
    · simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul]
      have e : lam * A1n + (1 - lam) * A2n = 0 := by rw [hlam]; field_simp; ring
      have key : lam * ((cos ψ * ((1 : ℝ)) - sin ψ * ((0 : ℝ))) / (2 * 𝒮)) + (1 - lam) * ((cos ψ * ((-1 : ℝ) + (2 : ℝ) * (𝒞) ^ 2) - sin ψ * ((2 : ℝ) * (𝒞) * (𝒮))) / (2 * 𝒮)) - ((cos ψ * ((-1 : ℝ) * (𝒞)) - sin ψ * ((-1 : ℝ) * (𝒮))) / (2 * 𝒮)) - sStar / 2 = (lam * A1n + (1 - lam) * A2n) / (2 * 𝒮 * (𝒮 + 𝒞)) := by
        rw [show lam * ((cos ψ * ((1 : ℝ)) - sin ψ * ((0 : ℝ))) / (2 * 𝒮)) + (1 - lam) * ((cos ψ * ((-1 : ℝ) + (2 : ℝ) * (𝒞) ^ 2) - sin ψ * ((2 : ℝ) * (𝒞) * (𝒮))) / (2 * 𝒮)) - ((cos ψ * ((-1 : ℝ) * (𝒞)) - sin ψ * ((-1 : ℝ) * (𝒮))) / (2 * 𝒮)) - sStar / 2 = lam * (((cos ψ * ((1 : ℝ)) - sin ψ * ((0 : ℝ))) / (2 * 𝒮)) - ((cos ψ * ((-1 : ℝ) * (𝒞)) - sin ψ * ((-1 : ℝ) * (𝒮))) / (2 * 𝒮)) - sStar / 2) + (1 - lam) * (((cos ψ * ((-1 : ℝ) + (2 : ℝ) * (𝒞) ^ 2) - sin ψ * ((2 : ℝ) * (𝒞) * (𝒮))) / (2 * 𝒮)) - ((cos ψ * ((-1 : ℝ) * (𝒞)) - sin ψ * ((-1 : ℝ) * (𝒮))) / (2 * 𝒮)) - sStar / 2) by ring, iA1n, iA2n]; ring
      rw [e, zero_div] at key
      have : lam * (a + ((cos ψ * ((1 : ℝ)) - sin ψ * ((0 : ℝ))) / (2 * 𝒮))) + (1 - lam) * (a + ((cos ψ * ((-1 : ℝ) + (2 : ℝ) * (𝒞) ^ 2) - sin ψ * ((2 : ℝ) * (𝒞) * (𝒮))) / (2 * 𝒮))) = a + (lam * ((cos ψ * ((1 : ℝ)) - sin ψ * ((0 : ℝ))) / (2 * 𝒮)) + (1 - lam) * ((cos ψ * ((-1 : ℝ) + (2 : ℝ) * (𝒞) ^ 2) - sin ψ * ((2 : ℝ) * (𝒞) * (𝒮))) / (2 * 𝒮))) := by ring
      linarith
    · simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul]
      have e : lam * B1n + (1 - lam) * B2n = (A1n * B2n - A2n * B1n) / (A1n - A2n) := by rw [hlam]; field_simp; ring
      have pe : 0 ≤ lam * B1n + (1 - lam) * B2n := by rw [e]; exact div_nonneg pD hd.le
      have key : lam * ((sin ψ * ((1 : ℝ)) + cos ψ * ((0 : ℝ))) / (2 * 𝒮)) + (1 - lam) * ((sin ψ * ((-1 : ℝ) + (2 : ℝ) * (𝒞) ^ 2) + cos ψ * ((2 : ℝ) * (𝒞) * (𝒮))) / (2 * 𝒮)) - ((sin ψ * ((-1 : ℝ) + (2 : ℝ) * (𝒞) ^ 2) + cos ψ * ((-2 : ℝ) * (𝒞) * (𝒮))) / (2 * 𝒮)) - sStar / 2 = (lam * B1n + (1 - lam) * B2n) / (2 * 𝒮 * (𝒮 + 𝒞)) := by
        rw [show lam * ((sin ψ * ((1 : ℝ)) + cos ψ * ((0 : ℝ))) / (2 * 𝒮)) + (1 - lam) * ((sin ψ * ((-1 : ℝ) + (2 : ℝ) * (𝒞) ^ 2) + cos ψ * ((2 : ℝ) * (𝒞) * (𝒮))) / (2 * 𝒮)) - ((sin ψ * ((-1 : ℝ) + (2 : ℝ) * (𝒞) ^ 2) + cos ψ * ((-2 : ℝ) * (𝒞) * (𝒮))) / (2 * 𝒮)) - sStar / 2 = lam * (((sin ψ * ((1 : ℝ)) + cos ψ * ((0 : ℝ))) / (2 * 𝒮)) - ((sin ψ * ((-1 : ℝ) + (2 : ℝ) * (𝒞) ^ 2) + cos ψ * ((-2 : ℝ) * (𝒞) * (𝒮))) / (2 * 𝒮)) - sStar / 2) + (1 - lam) * (((sin ψ * ((-1 : ℝ) + (2 : ℝ) * (𝒞) ^ 2) + cos ψ * ((2 : ℝ) * (𝒞) * (𝒮))) / (2 * 𝒮)) - ((sin ψ * ((-1 : ℝ) + (2 : ℝ) * (𝒞) ^ 2) + cos ψ * ((-2 : ℝ) * (𝒞) * (𝒮))) / (2 * 𝒮)) - sStar / 2) by ring, iB1n, iB2n]; ring
      have : 0 ≤ (lam * B1n + (1 - lam) * B2n) / (2 * 𝒮 * (𝒮 + 𝒞)) := div_nonneg pe hw.le
      have : lam * (b + ((sin ψ * ((1 : ℝ)) + cos ψ * ((0 : ℝ))) / (2 * 𝒮))) + (1 - lam) * (b + ((sin ψ * ((-1 : ℝ) + (2 : ℝ) * (𝒞) ^ 2) + cos ψ * ((2 : ℝ) * (𝒞) * (𝒮))) / (2 * 𝒮))) = b + (lam * ((sin ψ * ((1 : ℝ)) + cos ψ * ((0 : ℝ))) / (2 * 𝒮)) + (1 - lam) * ((sin ψ * ((-1 : ℝ) + (2 : ℝ) * (𝒞) ^ 2) + cos ψ * ((2 : ℝ) * (𝒞) * (𝒮))) / (2 * 𝒮))) := by ring
      linarith

lemma region_R2 (a b ψ : ℝ) (hlo : 0 ≤ ψ) (hhi : ψ ≤ π / 10)
    (Q : Set (ℝ × ℝ)) (hQ : Convex ℝ Q)
    (h0 : (a + circumradius * cos (ψ + 0), b + circumradius * sin (ψ + 0)) ∈ Q)
    (h1 : (a + circumradius * cos (ψ + 2 * π / 5), b + circumradius * sin (ψ + 2 * π / 5)) ∈ Q)
    (hx : 0 ≤ a + circumradius * cos (ψ + 4 * π / 5))
    (hy : 0 ≤ b + circumradius * sin (ψ + 8 * π / 5)) :
    ∃ p ∈ Q, sStar / 2 ≤ p.1 ∧ sStar / 2 ≤ p.2 := by
  have hS := S_pos; have hC := C_pos; have hSC := hSC'; have hC2 := hC2'
  obtain ⟨hCl, hCh⟩ := C_bnd; obtain ⟨hSl, hSh⟩ := S_bnd; obtain ⟨hPl, hPh⟩ := P_bnd
  have hcs : cos ψ ^ 2 + sin ψ ^ 2 = 1 := cos_sq_add_sin_sq ψ
  have hcl : (95/100 : ℝ) ≤ cos ψ := by nlinarith [one_sub_sq_div_two_le_cos (x := ψ), pi_lt_d2, pi_gt_three]
  have hch : cos ψ ≤ 1 := cos_le_one ψ
  have hsl : (0 : ℝ) ≤ sin ψ := sin_nonneg_of_nonneg_of_le_pi hlo (by linarith [pi_gt_three])
  have hsh : sin ψ ≤ 3142/10000 := by have := sin_le hlo; nlinarith [pi_lt_d4]
  have ec0 : circumradius * cos (ψ + 0) = (cos ψ * ((1 : ℝ)) - sin ψ * ((0 : ℝ))) / (2 * 𝒮) := by
    rw [cos_add, tab_c_0, tab_s_0]; unfold circumradius; ring
  have es0 : circumradius * sin (ψ + 0) = (sin ψ * ((1 : ℝ)) + cos ψ * ((0 : ℝ))) / (2 * 𝒮) := by
    rw [sin_add, tab_c_0, tab_s_0]; unfold circumradius; ring
  have ec1 : circumradius * cos (ψ + 2 * π / 5) = (cos ψ * ((-1 : ℝ) + (2 : ℝ) * (𝒞) ^ 2) - sin ψ * ((2 : ℝ) * (𝒞) * (𝒮))) / (2 * 𝒮) := by
    rw [cos_add, tab_c_72, tab_s_72]; unfold circumradius; ring
  have es1 : circumradius * sin (ψ + 2 * π / 5) = (sin ψ * ((-1 : ℝ) + (2 : ℝ) * (𝒞) ^ 2) + cos ψ * ((2 : ℝ) * (𝒞) * (𝒮))) / (2 * 𝒮) := by
    rw [sin_add, tab_c_72, tab_s_72]; unfold circumradius; ring
  have ec2 : circumradius * cos (ψ + 4 * π / 5) = (cos ψ * ((-1 : ℝ) * (𝒞)) - sin ψ * ((1 : ℝ) * (𝒮))) / (2 * 𝒮) := by
    rw [cos_add, tab_c_144, tab_s_144]; unfold circumradius; ring
  have es2 : circumradius * sin (ψ + 4 * π / 5) = (sin ψ * ((-1 : ℝ) * (𝒞)) + cos ψ * ((1 : ℝ) * (𝒮))) / (2 * 𝒮) := by
    rw [sin_add, tab_c_144, tab_s_144]; unfold circumradius; ring
  have ec4 : circumradius * cos (ψ + 8 * π / 5) = (cos ψ * ((-1 : ℝ) + (2 : ℝ) * (𝒞) ^ 2) - sin ψ * ((-2 : ℝ) * (𝒞) * (𝒮))) / (2 * 𝒮) := by
    rw [cos_add, tab_c_288, tab_s_288]; unfold circumradius; ring
  have es4 : circumradius * sin (ψ + 8 * π / 5) = (sin ψ * ((-1 : ℝ) + (2 : ℝ) * (𝒞) ^ 2) + cos ψ * ((-2 : ℝ) * (𝒞) * (𝒮))) / (2 * 𝒮) := by
    rw [sin_add, tab_c_288, tab_s_288]; unfold circumradius; ring
  have hcl' : ((19 : ℝ) / 20) ≤ cos ψ := by linarith
  have hch' : cos ψ ≤ (1 : ℝ) := by linarith
  have hsl' : (0 : ℝ) ≤ sin ψ := by linarith
  have hsh' : sin ψ ≤ ((1571 : ℝ) / 5000) := by linarith
  rw [ec0, es0] at h0; rw [ec1, es1] at h1
  rw [ec2] at hx; rw [es4] at hy
  have hw : 0 < 2 * 𝒮 * (𝒮 + 𝒞) := by positivity
  have hT : sStar / 2 = (𝒞 * (3 + 𝒞 - 2 * 𝒞 ^ 2)) / (2 * 𝒮 * (𝒮 + 𝒞)) := by unfold sStar; field_simp; try ring
  obtain ⟨A1n, hA1n⟩ : ∃ X : ℝ, X = (-1 : ℝ) * (𝒞) ^ 2 + (-3 : ℝ) * (𝒞) + (2 : ℝ) * (𝒞) ^ 3 + (1 : ℝ) * (𝒞) * (cos ψ) + (1 : ℝ) * (𝒮) * (cos ψ) + (1 : ℝ) * (cos ψ) * (𝒞) ^ 2 + (1 : ℝ) * (sin ψ) * (𝒮) ^ 2 + (1 : ℝ) * (𝒞) * (𝒮) * (cos ψ) + (1 : ℝ) * (𝒞) * (𝒮) * (sin ψ) := ⟨_, rfl⟩
  obtain ⟨A2n, hA2n⟩ : ∃ X : ℝ, X = (-1 : ℝ) * (𝒞) ^ 2 + (-3 : ℝ) * (𝒞) + (2 : ℝ) * (𝒞) ^ 3 + (1 : ℝ) * (cos ψ) * (𝒞) ^ 2 + (1 : ℝ) * (sin ψ) * (𝒮) ^ 2 + (-1 : ℝ) * (𝒞) * (cos ψ) + (-1 : ℝ) * (𝒮) * (cos ψ) + (2 : ℝ) * (cos ψ) * (𝒞) ^ 3 + (1 : ℝ) * (𝒞) * (𝒮) * (cos ψ) + (1 : ℝ) * (𝒞) * (𝒮) * (sin ψ) + (-2 : ℝ) * (𝒞) * (sin ψ) * (𝒮) ^ 2 + (-2 : ℝ) * (𝒮) * (sin ψ) * (𝒞) ^ 2 + (2 : ℝ) * (𝒮) * (cos ψ) * (𝒞) ^ 2 := ⟨_, rfl⟩
  obtain ⟨B1n, hB1n⟩ : ∃ X : ℝ, X = (-1 : ℝ) * (𝒞) ^ 2 + (-3 : ℝ) * (𝒞) + (2 : ℝ) * (𝒞) ^ 3 + (-2 : ℝ) * (sin ψ) * (𝒞) ^ 3 + (2 : ℝ) * (𝒞) * (sin ψ) + (2 : ℝ) * (𝒮) * (sin ψ) + (-2 : ℝ) * (𝒮) * (sin ψ) * (𝒞) ^ 2 + (2 : ℝ) * (𝒞) * (cos ψ) * (𝒮) ^ 2 + (2 : ℝ) * (𝒮) * (cos ψ) * (𝒞) ^ 2 := ⟨_, rfl⟩
  obtain ⟨B2n, hB2n⟩ : ∃ X : ℝ, X = (-1 : ℝ) * (𝒞) ^ 2 + (-3 : ℝ) * (𝒞) + (2 : ℝ) * (𝒞) ^ 3 + (4 : ℝ) * (𝒞) * (cos ψ) * (𝒮) ^ 2 + (4 : ℝ) * (𝒮) * (cos ψ) * (𝒞) ^ 2 := ⟨_, rfl⟩
  have iA1n : ((cos ψ * ((1 : ℝ)) - sin ψ * ((0 : ℝ))) / (2 * 𝒮)) - ((cos ψ * ((-1 : ℝ) * (𝒞)) - sin ψ * ((1 : ℝ) * (𝒮))) / (2 * 𝒮)) - sStar / 2 = A1n / (2 * 𝒮 * (𝒮 + 𝒞)) := by
    rw [hT, hA1n]; field_simp; ring
  have iA2n : ((cos ψ * ((-1 : ℝ) + (2 : ℝ) * (𝒞) ^ 2) - sin ψ * ((2 : ℝ) * (𝒞) * (𝒮))) / (2 * 𝒮)) - ((cos ψ * ((-1 : ℝ) * (𝒞)) - sin ψ * ((1 : ℝ) * (𝒮))) / (2 * 𝒮)) - sStar / 2 = A2n / (2 * 𝒮 * (𝒮 + 𝒞)) := by
    rw [hT, hA2n]; field_simp; ring
  have iB1n : ((sin ψ * ((1 : ℝ)) + cos ψ * ((0 : ℝ))) / (2 * 𝒮)) - ((sin ψ * ((-1 : ℝ) + (2 : ℝ) * (𝒞) ^ 2) + cos ψ * ((-2 : ℝ) * (𝒞) * (𝒮))) / (2 * 𝒮)) - sStar / 2 = B1n / (2 * 𝒮 * (𝒮 + 𝒞)) := by
    rw [hT, hB1n]; field_simp; ring
  have iB2n : ((sin ψ * ((-1 : ℝ) + (2 : ℝ) * (𝒞) ^ 2) + cos ψ * ((2 : ℝ) * (𝒞) * (𝒮))) / (2 * 𝒮)) - ((sin ψ * ((-1 : ℝ) + (2 : ℝ) * (𝒞) ^ 2) + cos ψ * ((-2 : ℝ) * (𝒞) * (𝒮))) / (2 * 𝒮)) - sStar / 2 = B2n / (2 * 𝒮 * (𝒮 + 𝒞)) := by
    rw [hT, hB2n]; field_simp; ring
  have pA1 := pos_R2_pA1 (cos ψ) (sin ψ) hcl' hch' hsl' hsh'
  have pB2 := pos_R2_pB2 (cos ψ) (sin ψ) hcl' hch' hsl' hsh'
  rw [← hA1n] at pA1; rw [← hB2n] at pB2
  have pM1 := pos_R2_pM1 (cos ψ) (sin ψ) hcl' hch' hsl' hsh'
  have hD : A1n * B2n - A2n * B1n = (-((-1 : ℝ) + (1 : ℝ) * (cos ψ) + (-1 : ℝ) * (sin ψ) + (2 : ℝ) * (𝒞) ^ 2 + (-2 : ℝ) * (cos ψ) * (𝒞) ^ 2 + (2 : ℝ) * (𝒞) * (𝒮) * (sin ψ))) * ((2 : ℝ) + (-3 : ℝ) * (𝒞) + (-3 : ℝ) * (𝒮) + ((-1 : ℝ) / 2) * (sin ψ) + ((13 : ℝ) / 4) * (cos ψ) + (1 : ℝ) * (𝒮) * (sin ψ) + (2 : ℝ) * (𝒞) * (𝒮) + (2 : ℝ) * (𝒞) * (sin ψ) + (2 : ℝ) * (𝒮) * (cos ψ) + ((9 : ℝ) / 2) * (𝒞) * (cos ψ) + (1 : ℝ) * (𝒞) * (𝒮) * (sin ψ) + (12 : ℝ) * (𝒞) * (𝒮) * (cos ψ)) := by
    rw [hA1n, hA2n, hB1n, hB2n]
    linear_combination (((7 : ℝ) / 4) + (-2 : ℝ) * (𝒞) + (-2 : ℝ) * (𝒮) + (3 : ℝ) * (𝒞) * (𝒮)) * hcs + ((-8 : ℝ) * (𝒞) ^ 4 * (cos ψ) ^ 2 + (-8 : ℝ) * (𝒞) ^ 4 * (sin ψ) ^ 2 + (-6 : ℝ) * (𝒞) * (sin ψ) + (-6 : ℝ) * (cos ψ) * (𝒞) ^ 2 + (-2 : ℝ) * (𝒞) * (sin ψ) ^ 2 + (-2 : ℝ) * (𝒮) * (sin ψ) ^ 2 + (-2 : ℝ) * (cos ψ) * (𝒞) ^ 3 + (-2 : ℝ) * (sin ψ) * (𝒞) ^ 2 + (-2 : ℝ) * (sin ψ) * (𝒞) ^ 3 + (2 : ℝ) * (cos ψ) * (sin ψ) + (4 : ℝ) * (cos ψ) * (𝒞) ^ 4 + (4 : ℝ) * (sin ψ) * (𝒞) ^ 4 + (4 : ℝ) * (𝒞) ^ 3 * (cos ψ) ^ 2 + (4 : ℝ) * (𝒞) ^ 3 * (sin ψ) ^ 2 + (10 : ℝ) * (𝒞) ^ 2 * (sin ψ) ^ 2 + (12 : ℝ) * (𝒞) ^ 2 * (cos ψ) ^ 2 + (-4 : ℝ) * (𝒮) * (𝒞) ^ 3 * (cos ψ) ^ 2 + (-4 : ℝ) * (𝒮) * (𝒞) ^ 3 * (sin ψ) ^ 2 + (2 : ℝ) * (𝒮) * (𝒞) ^ 2 * (cos ψ) ^ 2 + (2 : ℝ) * (𝒮) * (𝒞) ^ 2 * (sin ψ) ^ 2 + (2 : ℝ) * (cos ψ) * (sin ψ) * (𝒞) ^ 3 + (4 : ℝ) * (𝒞) * (𝒮) * (sin ψ) ^ 2 + (6 : ℝ) * (𝒞) * (𝒮) * (cos ψ) ^ 2 + (8 : ℝ) * (cos ψ) * (sin ψ) * (𝒞) ^ 4 + (20 : ℝ) * (cos ψ) * (sin ψ) * (𝒞) ^ 2 + ((7 : ℝ) / 2) * (𝒞) * (cos ψ) * (sin ψ) + (2 : ℝ) * (𝒞) * (cos ψ) * (sin ψ) * (𝒮) ^ 2 + (4 : ℝ) * (𝒮) * (cos ψ) * (sin ψ) * (𝒞) ^ 2 + (4 : ℝ) * (cos ψ) * (sin ψ) * (𝒞) ^ 2 * (𝒮) ^ 2 + (8 : ℝ) * (𝒮) * (cos ψ) * (sin ψ) * (𝒞) ^ 3) * hSC + (((1 : ℝ) / 4) + (-1 : ℝ) * (𝒮) + ((-3 : ℝ) / 2) * (𝒞) + ((-3 : ℝ) / 2) * (cos ψ) ^ 2 + ((3 : ℝ) / 2) * (sin ψ) + ((5 : ℝ) / 4) * (cos ψ) + ((5 : ℝ) / 4) * (sin ψ) ^ 2 + (1 : ℝ) * (𝒞) * (𝒮) + (1 : ℝ) * (𝒮) * (sin ψ) ^ 2 + (-1 : ℝ) * (sin ψ) * (𝒞) ^ 2 + (-4 : ℝ) * (𝒮) * (cos ψ) ^ 2 + (-4 : ℝ) * (𝒞) ^ 2 * (sin ψ) ^ 2 + (-2 : ℝ) * (𝒮) * (sin ψ) + (-2 : ℝ) * (cos ψ) * (𝒞) ^ 4 + (2 : ℝ) * (𝒞) * (sin ψ) + (2 : ℝ) * (𝒞) ^ 4 * (cos ψ) ^ 2 + (2 : ℝ) * (𝒞) ^ 4 * (sin ψ) ^ 2 + (5 : ℝ) * (𝒞) * (cos ψ) + (5 : ℝ) * (𝒮) * (cos ψ) + ((-9 : ℝ) / 2) * (𝒞) ^ 2 * (cos ψ) ^ 2 + ((-7 : ℝ) / 2) * (𝒞) * (cos ψ) ^ 2 + ((-1 : ℝ) / 2) * (𝒞) * (sin ψ) ^ 2 + ((7 : ℝ) / 4) * (cos ψ) * (sin ψ) + ((9 : ℝ) / 2) * (cos ψ) * (𝒞) ^ 2 + (1 : ℝ) * (𝒮) * (cos ψ) * (sin ψ) + (-1 : ℝ) * (𝒞) * (𝒮) * (sin ψ) ^ 2 + (-1 : ℝ) * (cos ψ) * (sin ψ) * (𝒞) ^ 4 + (-7 : ℝ) * (𝒞) * (𝒮) * (cos ψ) ^ 2 + (-5 : ℝ) * (cos ψ) * (sin ψ) * (𝒞) ^ 2 + (-3 : ℝ) * (𝒞) * (𝒮) * (sin ψ) + (2 : ℝ) * (𝒮) * (sin ψ) * (𝒞) ^ 3 + (6 : ℝ) * (𝒞) * (𝒮) * (cos ψ) + ((-9 : ℝ) / 2) * (𝒞) * (cos ψ) * (sin ψ) + ((-1 : ℝ) / 2) * (cos ψ) * (sin ψ) * (𝒞) ^ 3 + (-1 : ℝ) * (cos ψ) * (sin ψ) * (𝒞) ^ 2 * (𝒮) ^ 2 + ((-3 : ℝ) / 2) * (𝒞) * (𝒮) * (cos ψ) * (sin ψ) + ((-1 : ℝ) / 2) * (𝒞) * (cos ψ) * (sin ψ) * (𝒮) ^ 2) * hC2
  have hL := L_nonpos ψ hlo hhi
  have pD : 0 ≤ A1n * B2n - A2n * B1n := by rw [hD]; exact mul_nonneg (neg_nonneg.2 hL) pM1
  rcases le_or_gt 0 A2n with hA2 | hA2
  · refine ⟨_, h1, ?_, ?_⟩
    · have := iA2n; have : 0 ≤ A2n / (2 * 𝒮 * (𝒮 + 𝒞)) := div_nonneg hA2 hw.le
      simp only; linarith
    · have := iB2n; have : 0 ≤ B2n / (2 * 𝒮 * (𝒮 + 𝒞)) := div_nonneg pB2 hw.le
      simp only; linarith
  · have hd : 0 < A1n - A2n := by linarith
    set lam := -A2n / (A1n - A2n) with hlam
    have hl0 : 0 ≤ lam := div_nonneg (by linarith) hd.le
    have hl1 : 0 ≤ 1 - lam := by rw [hlam, one_sub_div hd.ne']; exact div_nonneg (by linarith) hd.le
    refine ⟨lam • _ + (1 - lam) • _, hQ h0 h1 hl0 hl1 (by ring), ?_, ?_⟩
    · simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul]
      have e : lam * A1n + (1 - lam) * A2n = 0 := by rw [hlam]; field_simp; ring
      have key : lam * ((cos ψ * ((1 : ℝ)) - sin ψ * ((0 : ℝ))) / (2 * 𝒮)) + (1 - lam) * ((cos ψ * ((-1 : ℝ) + (2 : ℝ) * (𝒞) ^ 2) - sin ψ * ((2 : ℝ) * (𝒞) * (𝒮))) / (2 * 𝒮)) - ((cos ψ * ((-1 : ℝ) * (𝒞)) - sin ψ * ((1 : ℝ) * (𝒮))) / (2 * 𝒮)) - sStar / 2 = (lam * A1n + (1 - lam) * A2n) / (2 * 𝒮 * (𝒮 + 𝒞)) := by
        rw [show lam * ((cos ψ * ((1 : ℝ)) - sin ψ * ((0 : ℝ))) / (2 * 𝒮)) + (1 - lam) * ((cos ψ * ((-1 : ℝ) + (2 : ℝ) * (𝒞) ^ 2) - sin ψ * ((2 : ℝ) * (𝒞) * (𝒮))) / (2 * 𝒮)) - ((cos ψ * ((-1 : ℝ) * (𝒞)) - sin ψ * ((1 : ℝ) * (𝒮))) / (2 * 𝒮)) - sStar / 2 = lam * (((cos ψ * ((1 : ℝ)) - sin ψ * ((0 : ℝ))) / (2 * 𝒮)) - ((cos ψ * ((-1 : ℝ) * (𝒞)) - sin ψ * ((1 : ℝ) * (𝒮))) / (2 * 𝒮)) - sStar / 2) + (1 - lam) * (((cos ψ * ((-1 : ℝ) + (2 : ℝ) * (𝒞) ^ 2) - sin ψ * ((2 : ℝ) * (𝒞) * (𝒮))) / (2 * 𝒮)) - ((cos ψ * ((-1 : ℝ) * (𝒞)) - sin ψ * ((1 : ℝ) * (𝒮))) / (2 * 𝒮)) - sStar / 2) by ring, iA1n, iA2n]; ring
      rw [e, zero_div] at key
      have : lam * (a + ((cos ψ * ((1 : ℝ)) - sin ψ * ((0 : ℝ))) / (2 * 𝒮))) + (1 - lam) * (a + ((cos ψ * ((-1 : ℝ) + (2 : ℝ) * (𝒞) ^ 2) - sin ψ * ((2 : ℝ) * (𝒞) * (𝒮))) / (2 * 𝒮))) = a + (lam * ((cos ψ * ((1 : ℝ)) - sin ψ * ((0 : ℝ))) / (2 * 𝒮)) + (1 - lam) * ((cos ψ * ((-1 : ℝ) + (2 : ℝ) * (𝒞) ^ 2) - sin ψ * ((2 : ℝ) * (𝒞) * (𝒮))) / (2 * 𝒮))) := by ring
      linarith
    · simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul]
      have e : lam * B1n + (1 - lam) * B2n = (A1n * B2n - A2n * B1n) / (A1n - A2n) := by rw [hlam]; field_simp; ring
      have pe : 0 ≤ lam * B1n + (1 - lam) * B2n := by rw [e]; exact div_nonneg pD hd.le
      have key : lam * ((sin ψ * ((1 : ℝ)) + cos ψ * ((0 : ℝ))) / (2 * 𝒮)) + (1 - lam) * ((sin ψ * ((-1 : ℝ) + (2 : ℝ) * (𝒞) ^ 2) + cos ψ * ((2 : ℝ) * (𝒞) * (𝒮))) / (2 * 𝒮)) - ((sin ψ * ((-1 : ℝ) + (2 : ℝ) * (𝒞) ^ 2) + cos ψ * ((-2 : ℝ) * (𝒞) * (𝒮))) / (2 * 𝒮)) - sStar / 2 = (lam * B1n + (1 - lam) * B2n) / (2 * 𝒮 * (𝒮 + 𝒞)) := by
        rw [show lam * ((sin ψ * ((1 : ℝ)) + cos ψ * ((0 : ℝ))) / (2 * 𝒮)) + (1 - lam) * ((sin ψ * ((-1 : ℝ) + (2 : ℝ) * (𝒞) ^ 2) + cos ψ * ((2 : ℝ) * (𝒞) * (𝒮))) / (2 * 𝒮)) - ((sin ψ * ((-1 : ℝ) + (2 : ℝ) * (𝒞) ^ 2) + cos ψ * ((-2 : ℝ) * (𝒞) * (𝒮))) / (2 * 𝒮)) - sStar / 2 = lam * (((sin ψ * ((1 : ℝ)) + cos ψ * ((0 : ℝ))) / (2 * 𝒮)) - ((sin ψ * ((-1 : ℝ) + (2 : ℝ) * (𝒞) ^ 2) + cos ψ * ((-2 : ℝ) * (𝒞) * (𝒮))) / (2 * 𝒮)) - sStar / 2) + (1 - lam) * (((sin ψ * ((-1 : ℝ) + (2 : ℝ) * (𝒞) ^ 2) + cos ψ * ((2 : ℝ) * (𝒞) * (𝒮))) / (2 * 𝒮)) - ((sin ψ * ((-1 : ℝ) + (2 : ℝ) * (𝒞) ^ 2) + cos ψ * ((-2 : ℝ) * (𝒞) * (𝒮))) / (2 * 𝒮)) - sStar / 2) by ring, iB1n, iB2n]; ring
      have : 0 ≤ (lam * B1n + (1 - lam) * B2n) / (2 * 𝒮 * (𝒮 + 𝒞)) := div_nonneg pe hw.le
      have : lam * (b + ((sin ψ * ((1 : ℝ)) + cos ψ * ((0 : ℝ))) / (2 * 𝒮))) + (1 - lam) * (b + ((sin ψ * ((-1 : ℝ) + (2 : ℝ) * (𝒞) ^ 2) + cos ψ * ((2 : ℝ) * (𝒞) * (𝒮))) / (2 * 𝒮))) = b + (lam * ((sin ψ * ((1 : ℝ)) + cos ψ * ((0 : ℝ))) / (2 * 𝒮)) + (1 - lam) * ((sin ψ * ((-1 : ℝ) + (2 : ℝ) * (𝒞) ^ 2) + cos ψ * ((2 : ℝ) * (𝒞) * (𝒮))) / (2 * 𝒮))) := by ring
      linarith

lemma region_R3 (a b ψ : ℝ) (hlo : 0 ≤ ψ) (hhi : ψ ≤ 3 * π / 20)
    (Q : Set (ℝ × ℝ)) (hQ : Convex ℝ Q)
    (h0 : (a + circumradius * cos (ψ + π / 10), b + circumradius * sin (ψ + π / 10)) ∈ Q)
    (h1 : (a + circumradius * cos (ψ + π / 2), b + circumradius * sin (ψ + π / 2)) ∈ Q)
    (hx : 0 ≤ a + circumradius * cos (ψ + 9 * π / 10))
    (hy : 0 ≤ b + circumradius * sin (ψ + 13 * π / 10)) :
    ∃ p ∈ Q, sStar / 2 ≤ p.1 ∧ sStar / 2 ≤ p.2 := by
  have hS := S_pos; have hC := C_pos; have hSC := hSC'; have hC2 := hC2'
  obtain ⟨hCl, hCh⟩ := C_bnd; obtain ⟨hSl, hSh⟩ := S_bnd; obtain ⟨hPl, hPh⟩ := P_bnd
  have hcs : cos ψ ^ 2 + sin ψ ^ 2 = 1 := cos_sq_add_sin_sq ψ
  have hcl : (888/1000 : ℝ) ≤ cos ψ := by nlinarith [one_sub_sq_div_two_le_cos (x := ψ), pi_lt_d2, pi_gt_three]
  have hch : cos ψ ≤ 1 := cos_le_one ψ
  have hsl : (0 : ℝ) ≤ sin ψ := sin_nonneg_of_nonneg_of_le_pi hlo (by linarith [pi_gt_three])
  have hsh : sin ψ ≤ 4725/10000 := by have := sin_le hlo; nlinarith [pi_lt_d2]
  have ec0 : circumradius * cos (ψ + π / 10) = (cos ψ * ((2 : ℝ) * (𝒞) * (𝒮)) - sin ψ * ((-1 : ℝ) + (2 : ℝ) * (𝒞) ^ 2)) / (2 * 𝒮) := by
    rw [cos_add, tab_c_18, tab_s_18]; unfold circumradius; ring
  have es0 : circumradius * sin (ψ + π / 10) = (sin ψ * ((2 : ℝ) * (𝒞) * (𝒮)) + cos ψ * ((-1 : ℝ) + (2 : ℝ) * (𝒞) ^ 2)) / (2 * 𝒮) := by
    rw [sin_add, tab_c_18, tab_s_18]; unfold circumradius; ring
  have ec1 : circumradius * cos (ψ + π / 2) = (cos ψ * ((0 : ℝ)) - sin ψ * ((1 : ℝ))) / (2 * 𝒮) := by
    rw [cos_add, tab_c_90, tab_s_90]; unfold circumradius; ring
  have es1 : circumradius * sin (ψ + π / 2) = (sin ψ * ((0 : ℝ)) + cos ψ * ((1 : ℝ))) / (2 * 𝒮) := by
    rw [sin_add, tab_c_90, tab_s_90]; unfold circumradius; ring
  have ec2 : circumradius * cos (ψ + 9 * π / 10) = (cos ψ * ((-2 : ℝ) * (𝒞) * (𝒮)) - sin ψ * ((-1 : ℝ) + (2 : ℝ) * (𝒞) ^ 2)) / (2 * 𝒮) := by
    rw [cos_add, tab_c_162, tab_s_162]; unfold circumradius; ring
  have es2 : circumradius * sin (ψ + 9 * π / 10) = (sin ψ * ((-2 : ℝ) * (𝒞) * (𝒮)) + cos ψ * ((-1 : ℝ) + (2 : ℝ) * (𝒞) ^ 2)) / (2 * 𝒮) := by
    rw [sin_add, tab_c_162, tab_s_162]; unfold circumradius; ring
  have ec3 : circumradius * cos (ψ + 13 * π / 10) = (cos ψ * ((-1 : ℝ) * (𝒮)) - sin ψ * ((-1 : ℝ) * (𝒞))) / (2 * 𝒮) := by
    rw [cos_add, tab_c_234, tab_s_234]; unfold circumradius; ring
  have es3 : circumradius * sin (ψ + 13 * π / 10) = (sin ψ * ((-1 : ℝ) * (𝒮)) + cos ψ * ((-1 : ℝ) * (𝒞))) / (2 * 𝒮) := by
    rw [sin_add, tab_c_234, tab_s_234]; unfold circumradius; ring
  have hcl' : ((111 : ℝ) / 125) ≤ cos ψ := by linarith
  have hch' : cos ψ ≤ (1 : ℝ) := by linarith
  have hsl' : (0 : ℝ) ≤ sin ψ := by linarith
  have hsh' : sin ψ ≤ ((189 : ℝ) / 400) := by linarith
  rw [ec0, es0] at h0; rw [ec1, es1] at h1
  rw [ec2] at hx; rw [es3] at hy
  have hw : 0 < 2 * 𝒮 * (𝒮 + 𝒞) := by positivity
  have hT : sStar / 2 = (𝒞 * (3 + 𝒞 - 2 * 𝒞 ^ 2)) / (2 * 𝒮 * (𝒮 + 𝒞)) := by unfold sStar; field_simp; try ring
  obtain ⟨A1n, hA1n⟩ : ∃ X : ℝ, X = (-1 : ℝ) * (𝒞) ^ 2 + (-3 : ℝ) * (𝒞) + (2 : ℝ) * (𝒞) ^ 3 + (4 : ℝ) * (𝒞) * (cos ψ) * (𝒮) ^ 2 + (4 : ℝ) * (𝒮) * (cos ψ) * (𝒞) ^ 2 := ⟨_, rfl⟩
  obtain ⟨A2n, hA2n⟩ : ∃ X : ℝ, X = (-1 : ℝ) * (𝒞) ^ 2 + (-3 : ℝ) * (𝒞) + (2 : ℝ) * (𝒞) ^ 3 + (-2 : ℝ) * (𝒞) * (sin ψ) + (-2 : ℝ) * (𝒮) * (sin ψ) + (2 : ℝ) * (sin ψ) * (𝒞) ^ 3 + (2 : ℝ) * (𝒞) * (cos ψ) * (𝒮) ^ 2 + (2 : ℝ) * (𝒮) * (cos ψ) * (𝒞) ^ 2 + (2 : ℝ) * (𝒮) * (sin ψ) * (𝒞) ^ 2 := ⟨_, rfl⟩
  obtain ⟨B1n, hB1n⟩ : ∃ X : ℝ, X = (-1 : ℝ) * (𝒞) ^ 2 + (-3 : ℝ) * (𝒞) + (2 : ℝ) * (𝒞) ^ 3 + (1 : ℝ) * (cos ψ) * (𝒞) ^ 2 + (1 : ℝ) * (sin ψ) * (𝒮) ^ 2 + (-1 : ℝ) * (𝒞) * (cos ψ) + (-1 : ℝ) * (𝒮) * (cos ψ) + (2 : ℝ) * (cos ψ) * (𝒞) ^ 3 + (1 : ℝ) * (𝒞) * (𝒮) * (cos ψ) + (1 : ℝ) * (𝒞) * (𝒮) * (sin ψ) + (2 : ℝ) * (𝒞) * (sin ψ) * (𝒮) ^ 2 + (2 : ℝ) * (𝒮) * (cos ψ) * (𝒞) ^ 2 + (2 : ℝ) * (𝒮) * (sin ψ) * (𝒞) ^ 2 := ⟨_, rfl⟩
  obtain ⟨B2n, hB2n⟩ : ∃ X : ℝ, X = (-1 : ℝ) * (𝒞) ^ 2 + (-3 : ℝ) * (𝒞) + (2 : ℝ) * (𝒞) ^ 3 + (1 : ℝ) * (𝒞) * (cos ψ) + (1 : ℝ) * (𝒮) * (cos ψ) + (1 : ℝ) * (cos ψ) * (𝒞) ^ 2 + (1 : ℝ) * (sin ψ) * (𝒮) ^ 2 + (1 : ℝ) * (𝒞) * (𝒮) * (cos ψ) + (1 : ℝ) * (𝒞) * (𝒮) * (sin ψ) := ⟨_, rfl⟩
  have iA1n : ((cos ψ * ((2 : ℝ) * (𝒞) * (𝒮)) - sin ψ * ((-1 : ℝ) + (2 : ℝ) * (𝒞) ^ 2)) / (2 * 𝒮)) - ((cos ψ * ((-2 : ℝ) * (𝒞) * (𝒮)) - sin ψ * ((-1 : ℝ) + (2 : ℝ) * (𝒞) ^ 2)) / (2 * 𝒮)) - sStar / 2 = A1n / (2 * 𝒮 * (𝒮 + 𝒞)) := by
    rw [hT, hA1n]; field_simp; ring
  have iA2n : ((cos ψ * ((0 : ℝ)) - sin ψ * ((1 : ℝ))) / (2 * 𝒮)) - ((cos ψ * ((-2 : ℝ) * (𝒞) * (𝒮)) - sin ψ * ((-1 : ℝ) + (2 : ℝ) * (𝒞) ^ 2)) / (2 * 𝒮)) - sStar / 2 = A2n / (2 * 𝒮 * (𝒮 + 𝒞)) := by
    rw [hT, hA2n]; field_simp; ring
  have iB1n : ((sin ψ * ((2 : ℝ) * (𝒞) * (𝒮)) + cos ψ * ((-1 : ℝ) + (2 : ℝ) * (𝒞) ^ 2)) / (2 * 𝒮)) - ((sin ψ * ((-1 : ℝ) * (𝒮)) + cos ψ * ((-1 : ℝ) * (𝒞))) / (2 * 𝒮)) - sStar / 2 = B1n / (2 * 𝒮 * (𝒮 + 𝒞)) := by
    rw [hT, hB1n]; field_simp; ring
  have iB2n : ((sin ψ * ((0 : ℝ)) + cos ψ * ((1 : ℝ))) / (2 * 𝒮)) - ((sin ψ * ((-1 : ℝ) * (𝒮)) + cos ψ * ((-1 : ℝ) * (𝒞))) / (2 * 𝒮)) - sStar / 2 = B2n / (2 * 𝒮 * (𝒮 + 𝒞)) := by
    rw [hT, hB2n]; field_simp; ring
  have pA1 := pos_R3_pA1 (cos ψ) (sin ψ) hcl' hch' hsl' hsh'
  have pB2 := pos_R3_pB2 (cos ψ) (sin ψ) hcl' hch' hsl' hsh'
  rw [← hA1n] at pA1; rw [← hB2n] at pB2
  have pM1 := pos_R3_pM1 (cos ψ) (sin ψ) hcl' hch' hsl' hsh'
  have pM2 := pos_R3_pM2 (cos ψ) (sin ψ) hcl' hch' hsl' hsh'
  have hD : A1n * B2n - A2n * B1n = sin ψ * ((-2 : ℝ) * (cos ψ) + ((-5 : ℝ) / 4) * (sin ψ) + ((5 : ℝ) / 4) * (𝒮) + (1 : ℝ) * (𝒮) * (sin ψ) + (3 : ℝ) * (𝒞) * (cos ψ) + ((3 : ℝ) / 2) * (𝒮) * (cos ψ) + (-1 : ℝ) * (𝒞) * (𝒮) * (cos ψ) + (-4 : ℝ) * (𝒞) * (𝒮) * (sin ψ)) + (1 - cos ψ) * (((5 : ℝ) / 4) + ((5 : ℝ) / 4) * (𝒞) + (5 : ℝ) * (𝒞) * (𝒮)) := by
    rw [hA1n, hA2n, hB1n, hB2n]
    linear_combination (((5 : ℝ) / 4) + ((5 : ℝ) / 4) * (𝒞) + (5 : ℝ) * (𝒞) * (𝒮)) * hcs + ((-8 : ℝ) * (𝒞) ^ 4 * (cos ψ) ^ 2 + (-8 : ℝ) * (𝒞) ^ 4 * (sin ψ) ^ 2 + (-6 : ℝ) * (cos ψ) * (𝒞) ^ 2 + (-4 : ℝ) * (sin ψ) * (𝒞) ^ 4 + (-4 : ℝ) * (𝒞) ^ 3 * (sin ψ) ^ 2 + (-2 : ℝ) * (cos ψ) * (sin ψ) + (-2 : ℝ) * (cos ψ) * (𝒞) ^ 3 + (2 : ℝ) * (𝒮) * (sin ψ) ^ 2 + (2 : ℝ) * (sin ψ) * (𝒞) ^ 3 + (4 : ℝ) * (𝒞) * (sin ψ) ^ 2 + (4 : ℝ) * (cos ψ) * (𝒞) ^ 4 + (4 : ℝ) * (𝒞) ^ 3 * (cos ψ) ^ 2 + (6 : ℝ) * (sin ψ) * (𝒞) ^ 2 + (8 : ℝ) * (𝒞) ^ 2 * (sin ψ) ^ 2 + (12 : ℝ) * (𝒞) ^ 2 * (cos ψ) ^ 2 + (-8 : ℝ) * (cos ψ) * (sin ψ) * (𝒞) ^ 4 + (-4 : ℝ) * (𝒮) * (𝒞) ^ 3 * (cos ψ) ^ 2 + (-4 : ℝ) * (𝒮) * (𝒞) ^ 3 * (sin ψ) ^ 2 + (-2 : ℝ) * (𝒮) * (𝒞) ^ 2 * (sin ψ) ^ 2 + (2 : ℝ) * (𝒮) * (𝒞) ^ 2 * (cos ψ) ^ 2 + (2 : ℝ) * (cos ψ) * (sin ψ) * (𝒞) ^ 2 + (2 : ℝ) * (cos ψ) * (sin ψ) * (𝒞) ^ 3 + (4 : ℝ) * (𝒞) * (𝒮) * (sin ψ) ^ 2 + (6 : ℝ) * (𝒞) * (𝒮) * (cos ψ) ^ 2 + ((7 : ℝ) / 2) * (𝒞) * (cos ψ) * (sin ψ) + (-8 : ℝ) * (𝒮) * (cos ψ) * (sin ψ) * (𝒞) ^ 3 + (-4 : ℝ) * (cos ψ) * (sin ψ) * (𝒞) ^ 2 * (𝒮) ^ 2 + (2 : ℝ) * (𝒞) * (cos ψ) * (sin ψ) * (𝒮) ^ 2 + (4 : ℝ) * (𝒮) * (cos ψ) * (sin ψ) * (𝒞) ^ 2) * hSC + (((-5 : ℝ) / 4) * (cos ψ) + ((5 : ℝ) / 4) * (cos ψ) ^ 2 + (-1 : ℝ) * (𝒮) * (sin ψ) ^ 2 + (-2 : ℝ) * (cos ψ) * (𝒞) ^ 4 + (2 : ℝ) * (𝒞) ^ 3 * (sin ψ) ^ 2 + (2 : ℝ) * (𝒞) ^ 4 * (cos ψ) ^ 2 + (2 : ℝ) * (𝒞) ^ 4 * (sin ψ) ^ 2 + ((-11 : ℝ) / 4) * (𝒞) * (sin ψ) ^ 2 + ((-9 : ℝ) / 2) * (𝒞) ^ 2 * (cos ψ) ^ 2 + ((-5 : ℝ) / 2) * (𝒞) ^ 2 * (sin ψ) ^ 2 + ((-5 : ℝ) / 4) * (𝒞) * (cos ψ) ^ 2 + ((5 : ℝ) / 4) * (𝒞) * (cos ψ) + ((5 : ℝ) / 4) * (𝒮) * (sin ψ) + ((9 : ℝ) / 2) * (cos ψ) * (𝒞) ^ 2 + (1 : ℝ) * (𝒞) * (𝒮) * (cos ψ) + (1 : ℝ) * (cos ψ) * (sin ψ) * (𝒞) ^ 4 + (-1 : ℝ) * (𝒞) * (𝒮) * (cos ψ) ^ 2 + (-1 : ℝ) * (𝒞) * (𝒮) * (sin ψ) ^ 2 + (-1 : ℝ) * (cos ψ) * (sin ψ) * (𝒞) ^ 2 + (-2 : ℝ) * (𝒮) * (sin ψ) * (𝒞) ^ 3 + ((-1 : ℝ) / 2) * (𝒞) * (cos ψ) * (sin ψ) + ((-1 : ℝ) / 2) * (cos ψ) * (sin ψ) * (𝒞) ^ 3 + ((3 : ℝ) / 2) * (𝒮) * (cos ψ) * (sin ψ) + ((7 : ℝ) / 2) * (𝒞) * (𝒮) * (sin ψ) + (1 : ℝ) * (cos ψ) * (sin ψ) * (𝒞) ^ 2 * (𝒮) ^ 2 + (-2 : ℝ) * (𝒮) * (cos ψ) * (sin ψ) * (𝒞) ^ 2 + ((-1 : ℝ) / 2) * (𝒞) * (cos ψ) * (sin ψ) * (𝒮) ^ 2) * hC2
  have pD : 0 ≤ A1n * B2n - A2n * B1n := by rw [hD]; exact add_nonneg (mul_nonneg hsl pM1) (mul_nonneg (sub_nonneg.2 hch) pM2)
  rcases le_or_gt 0 A2n with hA2 | hA2
  · refine ⟨_, h1, ?_, ?_⟩
    · have := iA2n; have : 0 ≤ A2n / (2 * 𝒮 * (𝒮 + 𝒞)) := div_nonneg hA2 hw.le
      simp only; linarith
    · have := iB2n; have : 0 ≤ B2n / (2 * 𝒮 * (𝒮 + 𝒞)) := div_nonneg pB2 hw.le
      simp only; linarith
  · have hd : 0 < A1n - A2n := by linarith
    set lam := -A2n / (A1n - A2n) with hlam
    have hl0 : 0 ≤ lam := div_nonneg (by linarith) hd.le
    have hl1 : 0 ≤ 1 - lam := by rw [hlam, one_sub_div hd.ne']; exact div_nonneg (by linarith) hd.le
    refine ⟨lam • _ + (1 - lam) • _, hQ h0 h1 hl0 hl1 (by ring), ?_, ?_⟩
    · simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul]
      have e : lam * A1n + (1 - lam) * A2n = 0 := by rw [hlam]; field_simp; ring
      have key : lam * ((cos ψ * ((2 : ℝ) * (𝒞) * (𝒮)) - sin ψ * ((-1 : ℝ) + (2 : ℝ) * (𝒞) ^ 2)) / (2 * 𝒮)) + (1 - lam) * ((cos ψ * ((0 : ℝ)) - sin ψ * ((1 : ℝ))) / (2 * 𝒮)) - ((cos ψ * ((-2 : ℝ) * (𝒞) * (𝒮)) - sin ψ * ((-1 : ℝ) + (2 : ℝ) * (𝒞) ^ 2)) / (2 * 𝒮)) - sStar / 2 = (lam * A1n + (1 - lam) * A2n) / (2 * 𝒮 * (𝒮 + 𝒞)) := by
        rw [show lam * ((cos ψ * ((2 : ℝ) * (𝒞) * (𝒮)) - sin ψ * ((-1 : ℝ) + (2 : ℝ) * (𝒞) ^ 2)) / (2 * 𝒮)) + (1 - lam) * ((cos ψ * ((0 : ℝ)) - sin ψ * ((1 : ℝ))) / (2 * 𝒮)) - ((cos ψ * ((-2 : ℝ) * (𝒞) * (𝒮)) - sin ψ * ((-1 : ℝ) + (2 : ℝ) * (𝒞) ^ 2)) / (2 * 𝒮)) - sStar / 2 = lam * (((cos ψ * ((2 : ℝ) * (𝒞) * (𝒮)) - sin ψ * ((-1 : ℝ) + (2 : ℝ) * (𝒞) ^ 2)) / (2 * 𝒮)) - ((cos ψ * ((-2 : ℝ) * (𝒞) * (𝒮)) - sin ψ * ((-1 : ℝ) + (2 : ℝ) * (𝒞) ^ 2)) / (2 * 𝒮)) - sStar / 2) + (1 - lam) * (((cos ψ * ((0 : ℝ)) - sin ψ * ((1 : ℝ))) / (2 * 𝒮)) - ((cos ψ * ((-2 : ℝ) * (𝒞) * (𝒮)) - sin ψ * ((-1 : ℝ) + (2 : ℝ) * (𝒞) ^ 2)) / (2 * 𝒮)) - sStar / 2) by ring, iA1n, iA2n]; ring
      rw [e, zero_div] at key
      have : lam * (a + ((cos ψ * ((2 : ℝ) * (𝒞) * (𝒮)) - sin ψ * ((-1 : ℝ) + (2 : ℝ) * (𝒞) ^ 2)) / (2 * 𝒮))) + (1 - lam) * (a + ((cos ψ * ((0 : ℝ)) - sin ψ * ((1 : ℝ))) / (2 * 𝒮))) = a + (lam * ((cos ψ * ((2 : ℝ) * (𝒞) * (𝒮)) - sin ψ * ((-1 : ℝ) + (2 : ℝ) * (𝒞) ^ 2)) / (2 * 𝒮)) + (1 - lam) * ((cos ψ * ((0 : ℝ)) - sin ψ * ((1 : ℝ))) / (2 * 𝒮))) := by ring
      linarith
    · simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul]
      have e : lam * B1n + (1 - lam) * B2n = (A1n * B2n - A2n * B1n) / (A1n - A2n) := by rw [hlam]; field_simp; ring
      have pe : 0 ≤ lam * B1n + (1 - lam) * B2n := by rw [e]; exact div_nonneg pD hd.le
      have key : lam * ((sin ψ * ((2 : ℝ) * (𝒞) * (𝒮)) + cos ψ * ((-1 : ℝ) + (2 : ℝ) * (𝒞) ^ 2)) / (2 * 𝒮)) + (1 - lam) * ((sin ψ * ((0 : ℝ)) + cos ψ * ((1 : ℝ))) / (2 * 𝒮)) - ((sin ψ * ((-1 : ℝ) * (𝒮)) + cos ψ * ((-1 : ℝ) * (𝒞))) / (2 * 𝒮)) - sStar / 2 = (lam * B1n + (1 - lam) * B2n) / (2 * 𝒮 * (𝒮 + 𝒞)) := by
        rw [show lam * ((sin ψ * ((2 : ℝ) * (𝒞) * (𝒮)) + cos ψ * ((-1 : ℝ) + (2 : ℝ) * (𝒞) ^ 2)) / (2 * 𝒮)) + (1 - lam) * ((sin ψ * ((0 : ℝ)) + cos ψ * ((1 : ℝ))) / (2 * 𝒮)) - ((sin ψ * ((-1 : ℝ) * (𝒮)) + cos ψ * ((-1 : ℝ) * (𝒞))) / (2 * 𝒮)) - sStar / 2 = lam * (((sin ψ * ((2 : ℝ) * (𝒞) * (𝒮)) + cos ψ * ((-1 : ℝ) + (2 : ℝ) * (𝒞) ^ 2)) / (2 * 𝒮)) - ((sin ψ * ((-1 : ℝ) * (𝒮)) + cos ψ * ((-1 : ℝ) * (𝒞))) / (2 * 𝒮)) - sStar / 2) + (1 - lam) * (((sin ψ * ((0 : ℝ)) + cos ψ * ((1 : ℝ))) / (2 * 𝒮)) - ((sin ψ * ((-1 : ℝ) * (𝒮)) + cos ψ * ((-1 : ℝ) * (𝒞))) / (2 * 𝒮)) - sStar / 2) by ring, iB1n, iB2n]; ring
      have : 0 ≤ (lam * B1n + (1 - lam) * B2n) / (2 * 𝒮 * (𝒮 + 𝒞)) := div_nonneg pe hw.le
      have : lam * (b + ((sin ψ * ((2 : ℝ) * (𝒞) * (𝒮)) + cos ψ * ((-1 : ℝ) + (2 : ℝ) * (𝒞) ^ 2)) / (2 * 𝒮))) + (1 - lam) * (b + ((sin ψ * ((0 : ℝ)) + cos ψ * ((1 : ℝ))) / (2 * 𝒮))) = b + (lam * ((sin ψ * ((2 : ℝ) * (𝒞) * (𝒮)) + cos ψ * ((-1 : ℝ) + (2 : ℝ) * (𝒞) ^ 2)) / (2 * 𝒮)) + (1 - lam) * ((sin ψ * ((0 : ℝ)) + cos ψ * ((1 : ℝ))) / (2 * 𝒮))) := by ring
      linarith

theorem proof : ∀ a b θ : ℝ, pentagon a b θ ⊆ Set.Ici 0 ×ˢ Set.Ici 0 →
    ∃ p ∈ pentagon a b θ, sStar / 2 ≤ p.1 ∧ sStar / 2 ≤ p.2 := by
  intro a b θ hq
  have hp5 : 0 < 2 * π / 5 := by positivity
  obtain ⟨n, hn1, hn2⟩ : ∃ n : ℤ, (n : ℝ) ≤ (θ + 3 * π / 20) / (2 * π / 5) ∧
      (θ + 3 * π / 20) / (2 * π / 5) < n + 1 :=
    ⟨⌊(θ + 3 * π / 20) / (2 * π / 5)⌋, Int.floor_le _, Int.lt_floor_add_one _⟩
  rw [le_div_iff₀ hp5] at hn1
  rw [div_lt_iff₀ hp5] at hn2
  set φ := θ - n * (2 * π / 5) with hφ
  have hφlo : -(3 * π / 20) ≤ φ := by rw [hφ]; linarith
  have hφhi : φ ≤ π / 4 := by rw [hφ]; nlinarith [pi_pos]
  have hconv : Convex ℝ (pentagon a b θ) := convex_convexHull ℝ _
  have V : ∀ (k : ℤ) (t : ℝ), t = θ + 2 * π * (k : ℝ) / 5 →
      (a + circumradius * cos t, b + circumradius * sin t) ∈ pentagon a b θ := by
    rintro k t rfl; exact vert_mem a b θ k
  have Vx : ∀ (k : ℤ) (t : ℝ), t = θ + 2 * π * (k : ℝ) / 5 → 0 ≤ a + circumradius * cos t :=
    fun k t ht => (hq (V k t ht)).1
  have Vy : ∀ (k : ℤ) (t : ℝ), t = θ + 2 * π * (k : ℝ) / 5 → 0 ≤ b + circumradius * sin t :=
    fun k t ht => (hq (V k t ht)).2
  rcases le_or_gt φ 0 with h1 | h1
  · exact region_R1 a b φ hφlo h1 _ hconv
      (V (0 - n) _ (by rw [hφ]; push_cast; ring)) (V (1 - n) _ (by rw [hφ]; push_cast; ring))
      (Vx (3 - n) _ (by rw [hφ]; push_cast; ring)) (Vy (4 - n) _ (by rw [hφ]; push_cast; ring))
  rcases le_or_gt φ (π / 10) with h2 | h2
  · exact region_R2 a b φ h1.le h2 _ hconv
      (V (0 - n) _ (by rw [hφ]; push_cast; ring)) (V (1 - n) _ (by rw [hφ]; push_cast; ring))
      (Vx (2 - n) _ (by rw [hφ]; push_cast; ring)) (Vy (4 - n) _ (by rw [hφ]; push_cast; ring))
  · have hlo : 0 ≤ φ - π / 10 := by linarith
    have hhi : φ - π / 10 ≤ 3 * π / 20 := by linarith
    exact region_R3 a b (φ - π / 10) hlo hhi _ hconv
      (V (0 - n) _ (by rw [hφ]; push_cast; ring)) (V (1 - n) _ (by rw [hφ]; push_cast; ring))
      (Vx (2 - n) _ (by rw [hφ]; push_cast; ring)) (Vy (3 - n) _ (by rw [hφ]; push_cast; ring))



end Cor

theorem proof : IsLeast {s : ℝ | PacksInSquare 2 s} sStar :=
  ⟨Att.proof, fun s hs => Red.proof Cor.proof s hs⟩

end Submissions.PentagonsTwoOptimal.Full
