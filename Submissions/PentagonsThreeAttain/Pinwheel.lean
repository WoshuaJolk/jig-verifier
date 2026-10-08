import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic

namespace Submissions.PentagonsThreeAttain.Pinwheel

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

/-- Side of the smallest known square for three unit pentagons (Viquerat, April 2026):
`C (C² + 2CS² + CS + C + 3S² + S) / (S (C + S)²)` with `C = cos (π/5)`, `S = sin (π/5)` (≈ 2.90812). -/
noncomputable def s3 : ℝ :=
  Real.cos (Real.pi / 5) * (Real.cos (Real.pi / 5) ^ 2 + 2 * Real.cos (Real.pi / 5) * Real.sin (Real.pi / 5) ^ 2 +
    Real.cos (Real.pi / 5) * Real.sin (Real.pi / 5) + Real.cos (Real.pi / 5) + 3 * Real.sin (Real.pi / 5) ^ 2 +
    Real.sin (Real.pi / 5)) /
  (Real.sin (Real.pi / 5) * (Real.cos (Real.pi / 5) + Real.sin (Real.pi / 5)) ^ 2)


local notation "𝒞" => Real.cos (Real.pi / 5)
local notation "𝒮" => Real.sin (Real.pi / 5)

lemma S_pos : 0 < 𝒮 := sin_pos_of_pos_of_lt_pi (by positivity) (by linarith [pi_pos])
lemma C_eq : 𝒞 = (1 + √5) / 4 := cos_pi_div_five
lemma C_pos : 0 < 𝒞 := by rw [C_eq]; positivity
lemma hSC' : 𝒮 ^ 2 + 𝒞 ^ 2 = 1 := sin_sq_add_cos_sq _
lemma hC2' : 4 * 𝒞 ^ 2 - 2 * 𝒞 - 1 = 0 := by
  rw [C_eq]; have := Real.sq_sqrt (show (0:ℝ) ≤ 5 by norm_num); nlinarith
lemma hRS' : 2 * circumradius * 𝒮 = 1 := by
  have := S_pos; unfold circumradius; field_simp
lemma R_pos : 0 < circumradius := by unfold circumradius; have := S_pos; positivity
lemma C_bnd : (8090169943 / 10000000000 : ℝ) ≤ 𝒞 ∧ 𝒞 ≤ 8090169944 / 10000000000 := by
  rw [C_eq]
  have h1 : (22360679772 / 10000000000 : ℝ) < √5 := by rw [Real.lt_sqrt (by norm_num)]; norm_num
  have h2 : √5 < 22360679776 / 10000000000 := by rw [Real.sqrt_lt' (by norm_num)]; norm_num
  constructor <;> linarith
lemma S_bnd : (5877852522 / 10000000000 : ℝ) ≤ 𝒮 ∧ 𝒮 ≤ 5877852524 / 10000000000 := by
  obtain ⟨h1, h2⟩ := C_bnd; have h3 := hSC'; have h4 := S_pos
  constructor
  · by_contra h; have h' := (not_le.mp h); nlinarith
  · by_contra h; have h' := (not_le.mp h); nlinarith
lemma P_bnd : (237764129 / 500000000 : ℝ) ≤ 𝒞 * 𝒮 ∧ 𝒞 * 𝒮 ≤ 4755282583 / 10000000000 := by
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
lemma tab_c_144 : cos (4 * π / 5) = -𝒞 := by rw [show 4 * π / 5 = π - π / 5 by ring, cos_pi_sub]
lemma tab_s_144 : sin (4 * π / 5) = 𝒮 := by rw [show 4 * π / 5 = π - π / 5 by ring, sin_pi_sub]
lemma tab_c_216 : cos (6 * π / 5) = -𝒞 := by rw [show 6 * π / 5 = π / 5 + π by ring, cos_add_pi]
lemma tab_s_216 : sin (6 * π / 5) = -𝒮 := by rw [show 6 * π / 5 = π / 5 + π by ring, sin_add_pi]
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
lemma tab_c_36 : cos (π / 5) = 𝒞 := rfl
lemma tab_s_36 : sin (π / 5) = 𝒮 := rfl
lemma tab_c_108 : cos (3 * π / 5) = -(2 * 𝒞 ^ 2 - 1) := by
  rw [show 3 * π / 5 = π - 2 * (π / 5) by ring, cos_pi_sub, cos_two_mul]
lemma tab_s_108 : sin (3 * π / 5) = 2 * 𝒮 * 𝒞 := by
  rw [show 3 * π / 5 = π - 2 * (π / 5) by ring, sin_pi_sub, sin_two_mul]
lemma tab_c_180 : cos π = -1 := cos_pi
lemma tab_s_180 : sin π = 0 := sin_pi
lemma tab_c_252 : cos (7 * π / 5) = -(2 * 𝒞 ^ 2 - 1) := by
  rw [show 7 * π / 5 = 2 * (π / 5) + π by ring, cos_add_pi, cos_two_mul]
lemma tab_s_252 : sin (7 * π / 5) = -(2 * 𝒮 * 𝒞) := by
  rw [show 7 * π / 5 = 2 * (π / 5) + π by ring, sin_add_pi, sin_two_mul]
lemma tab_c_324 : cos (9 * π / 5) = 𝒞 := by
  rw [show 9 * π / 5 = -(π / 5) + 2 * π by ring, cos_add_two_pi, cos_neg]
lemma tab_s_324 : sin (9 * π / 5) = -𝒮 := by
  rw [show 9 * π / 5 = -(π / 5) + 2 * π by ring, sin_add_two_pi, sin_neg]

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


noncomputable def x0 : ℝ := s3 - circumradius * 𝒞 +
  2 * circumradius * (𝒞 * (s3 - 𝒞 - circumradius * 𝒞) - circumradius * 𝒞 - 𝒞)
noncomputable def y2 : ℝ := s3 - 𝒞 +
  2 * circumradius * (𝒞 * (s3 - 2 * (circumradius * 𝒞)) - 2 * (circumradius * 𝒞))


lemma cf1 : (0:ℝ) < ((1 : ℝ) * 𝒞 ^ 2 + (1 : ℝ) * 𝒞 ^ 3 + ((-7270293 : ℝ) / 2500000) * 𝒮 ^ 3 + (1 : ℝ) * 𝒞 * 𝒮 + (2 : ℝ) * 𝒞 ^ 2 * 𝒮 ^ 2 + ((-4770293 : ℝ) / 2500000) * 𝒮 * 𝒞 ^ 2 + ((-3520293 : ℝ) / 1250000) * 𝒞 * 𝒮 ^ 2) := by
  have hRS := hRS'; have hSC := hSC'; have hC2 := hC2'; have hS := S_pos
  obtain ⟨hCl, hCh⟩ := C_bnd; obtain ⟨hSl, hSh⟩ := S_bnd; obtain ⟨hPl, hPh⟩ := P_bnd
  have e : (2 * 𝒮) ^ 0 * ((1 : ℝ) * 𝒞 ^ 2 + (1 : ℝ) * 𝒞 ^ 3 + ((-7270293 : ℝ) / 2500000) * 𝒮 ^ 3 + (1 : ℝ) * 𝒞 * 𝒮 + (2 : ℝ) * 𝒞 ^ 2 * 𝒮 ^ 2 + ((-4770293 : ℝ) / 2500000) * 𝒮 * 𝒞 ^ 2 + ((-3520293 : ℝ) / 1250000) * 𝒞 * 𝒮 ^ 2) = (((9770293 : ℝ) / 10000000) + ((-6645293 : ℝ) / 2500000) * 𝒮 + ((-395293 : ℝ) / 2500000) * 𝒞 + ((3 : ℝ) / 2) * 𝒞 * 𝒮) := by
    linear_combination ((0:ℝ)) * hRS + (((2 : ℝ) * 𝒞 ^ 2 + ((-7270293 : ℝ) / 2500000) * 𝒮 + ((-3520293 : ℝ) / 1250000) * 𝒞)) * hSC + ((((9770293 : ℝ) / 10000000) + ((-1 : ℝ) / 2) * 𝒞 ^ 2 + ((1 : ℝ) / 4) * 𝒮 + ((3520293 : ℝ) / 5000000) * 𝒞)) * hC2
  have hp : (0:ℝ) < (2 * 𝒮) ^ 0 := by positivity
  have h2 : (0:ℝ) < (((9770293 : ℝ) / 10000000) + ((-6645293 : ℝ) / 2500000) * 𝒮 + ((-395293 : ℝ) / 2500000) * 𝒞 + ((3 : ℝ) / 2) * 𝒞 * 𝒮) := by linarith
  rw [← e] at h2
  exact pos_of_mul_pos_right h2 hp.le

lemma cf2 : (0:ℝ) < ((-1 : ℝ) * 𝒞 ^ 2 + (-1 : ℝ) * 𝒞 ^ 3 + ((29081173 : ℝ) / 10000000) * 𝒮 ^ 3 + (-1 : ℝ) * 𝒞 * 𝒮 + (-2 : ℝ) * 𝒞 ^ 2 * 𝒮 ^ 2 + ((14081173 : ℝ) / 5000000) * 𝒞 * 𝒮 ^ 2 + ((19081173 : ℝ) / 10000000) * 𝒮 * 𝒞 ^ 2) := by
  have hRS := hRS'; have hSC := hSC'; have hC2 := hC2'; have hS := S_pos
  obtain ⟨hCl, hCh⟩ := C_bnd; obtain ⟨hSl, hSh⟩ := S_bnd; obtain ⟨hPl, hPh⟩ := P_bnd
  have e : (2 * 𝒮) ^ 0 * ((-1 : ℝ) * 𝒞 ^ 2 + (-1 : ℝ) * 𝒞 ^ 3 + ((29081173 : ℝ) / 10000000) * 𝒮 ^ 3 + (-1 : ℝ) * 𝒞 * 𝒮 + (-2 : ℝ) * 𝒞 ^ 2 * 𝒮 ^ 2 + ((14081173 : ℝ) / 5000000) * 𝒞 * 𝒮 ^ 2 + ((19081173 : ℝ) / 10000000) * 𝒮 * 𝒞 ^ 2) = (((-39081173 : ℝ) / 40000000) + ((1581173 : ℝ) / 10000000) * 𝒞 + ((26581173 : ℝ) / 10000000) * 𝒮 + ((-3 : ℝ) / 2) * 𝒞 * 𝒮) := by
    linear_combination ((0:ℝ)) * hRS + (((-2 : ℝ) * 𝒞 ^ 2 + ((14081173 : ℝ) / 5000000) * 𝒞 + ((29081173 : ℝ) / 10000000) * 𝒮)) * hSC + ((((-39081173 : ℝ) / 40000000) + ((1 : ℝ) / 2) * 𝒞 ^ 2 + ((-14081173 : ℝ) / 20000000) * 𝒞 + ((-1 : ℝ) / 4) * 𝒮)) * hC2
  have hp : (0:ℝ) < (2 * 𝒮) ^ 0 := by positivity
  have h2 : (0:ℝ) < (((-39081173 : ℝ) / 40000000) + ((1581173 : ℝ) / 10000000) * 𝒞 + ((26581173 : ℝ) / 10000000) * 𝒮 + ((-3 : ℝ) / 2) * 𝒞 * 𝒮) := by linarith
  rw [← e] at h2
  exact pos_of_mul_pos_right h2 hp.le

lemma cf3 : (0:ℝ) < ((1 : ℝ) + (2 : ℝ) * 𝒞 * circumradius) := by
  have hRS := hRS'; have hSC := hSC'; have hC2 := hC2'; have hS := S_pos
  obtain ⟨hCl, hCh⟩ := C_bnd; obtain ⟨hSl, hSh⟩ := S_bnd; obtain ⟨hPl, hPh⟩ := P_bnd
  have e : (2 * 𝒮) ^ 1 * ((1 : ℝ) + (2 : ℝ) * 𝒞 * circumradius) = ((2 : ℝ) * 𝒞 + (2 : ℝ) * 𝒮) := by
    linear_combination (((2 : ℝ) * 𝒞)) * hRS + ((0:ℝ)) * hSC + ((0:ℝ)) * hC2
  have hp : (0:ℝ) < (2 * 𝒮) ^ 1 := by positivity
  have h2 : (0:ℝ) < ((2 : ℝ) * 𝒞 + (2 : ℝ) * 𝒮) := by linarith
  rw [← e] at h2
  exact pos_of_mul_pos_right h2 hp.le

lemma cf4 : (0:ℝ) < (((6467221 : ℝ) / 5000000) + (-2 : ℝ) * 𝒞 * circumradius ^ 2 + (-2 : ℝ) * circumradius * 𝒞 ^ 2 + (-2 : ℝ) * 𝒞 ^ 2 * circumradius ^ 2 + ((3520293 : ℝ) / 1250000) * 𝒞 * circumradius) := by
  have hRS := hRS'; have hSC := hSC'; have hC2 := hC2'; have hS := S_pos
  obtain ⟨hCl, hCh⟩ := C_bnd; obtain ⟨hSl, hSh⟩ := S_bnd; obtain ⟨hPl, hPh⟩ := P_bnd
  have e : (2 * 𝒮) ^ 2 * (((6467221 : ℝ) / 5000000) + (-2 : ℝ) * 𝒞 * circumradius ^ 2 + (-2 : ℝ) * circumradius * 𝒞 ^ 2 + (-2 : ℝ) * 𝒞 ^ 2 * circumradius ^ 2 + ((3520293 : ℝ) / 1250000) * 𝒞 * circumradius) = (((16901663 : ℝ) / 5000000) + (-1 : ℝ) * 𝒮 + ((-13967221 : ℝ) / 2500000) * 𝒞 + ((2270293 : ℝ) / 625000) * 𝒞 * 𝒮) := by
    linear_combination (((-2 : ℝ) * 𝒞 + (-2 : ℝ) * 𝒞 ^ 2 + (-4 : ℝ) * 𝒮 * 𝒞 ^ 2 + ((3520293 : ℝ) / 625000) * 𝒞 * 𝒮 + (-4 : ℝ) * 𝒞 * circumradius * 𝒮 + (-4 : ℝ) * circumradius * 𝒮 * 𝒞 ^ 2)) * hRS + ((((6467221 : ℝ) / 1250000))) * hSC + ((((-8967221 : ℝ) / 5000000) + (-1 : ℝ) * 𝒮)) * hC2
  have hp : (0:ℝ) < (2 * 𝒮) ^ 2 := by positivity
  have h2 : (0:ℝ) < (((16901663 : ℝ) / 5000000) + (-1 : ℝ) * 𝒮 + ((-13967221 : ℝ) / 2500000) * 𝒞 + ((2270293 : ℝ) / 625000) * 𝒞 * 𝒮) := by linarith
  rw [← e] at h2
  exact pos_of_mul_pos_right h2 hp.le

lemma cf5 : (0:ℝ) < (((-12934423 : ℝ) / 10000000) + (2 : ℝ) * 𝒞 * circumradius ^ 2 + (2 : ℝ) * circumradius * 𝒞 ^ 2 + (2 : ℝ) * 𝒞 ^ 2 * circumradius ^ 2 + ((-14081173 : ℝ) / 5000000) * 𝒞 * circumradius) := by
  have hRS := hRS'; have hSC := hSC'; have hC2 := hC2'; have hS := S_pos
  obtain ⟨hCl, hCh⟩ := C_bnd; obtain ⟨hSl, hSh⟩ := S_bnd; obtain ⟨hPl, hPh⟩ := P_bnd
  have e : (2 * 𝒮) ^ 2 * (((-12934423 : ℝ) / 10000000) + (2 : ℝ) * 𝒞 * circumradius ^ 2 + (2 : ℝ) * circumradius * 𝒞 ^ 2 + (2 : ℝ) * 𝒞 ^ 2 * circumradius ^ 2 + ((-14081173 : ℝ) / 5000000) * 𝒞 * circumradius) = (((-33803269 : ℝ) / 10000000) + (1 : ℝ) * 𝒮 + ((27934423 : ℝ) / 5000000) * 𝒞 + ((-9081173 : ℝ) / 2500000) * 𝒞 * 𝒮) := by
    linear_combination (((2 : ℝ) * 𝒞 + (2 : ℝ) * 𝒞 ^ 2 + (4 : ℝ) * 𝒮 * 𝒞 ^ 2 + ((-14081173 : ℝ) / 2500000) * 𝒞 * 𝒮 + (4 : ℝ) * 𝒞 * circumradius * 𝒮 + (4 : ℝ) * circumradius * 𝒮 * 𝒞 ^ 2)) * hRS + ((((-12934423 : ℝ) / 2500000))) * hSC + ((((17934423 : ℝ) / 10000000) + (1 : ℝ) * 𝒮)) * hC2
  have hp : (0:ℝ) < (2 * 𝒮) ^ 2 := by positivity
  have h2 : (0:ℝ) < (((-33803269 : ℝ) / 10000000) + (1 : ℝ) * 𝒮 + ((27934423 : ℝ) / 5000000) * 𝒞 + ((-9081173 : ℝ) / 2500000) * 𝒞 * 𝒮) := by linarith
  rw [← e] at h2
  exact pos_of_mul_pos_right h2 hp.le

lemma cf6 : (0:ℝ) < ((1 : ℝ) + (2 : ℝ) * 𝒞 * circumradius) := by
  have hRS := hRS'; have hSC := hSC'; have hC2 := hC2'; have hS := S_pos
  obtain ⟨hCl, hCh⟩ := C_bnd; obtain ⟨hSl, hSh⟩ := S_bnd; obtain ⟨hPl, hPh⟩ := P_bnd
  have e : (2 * 𝒮) ^ 1 * ((1 : ℝ) + (2 : ℝ) * 𝒞 * circumradius) = ((2 : ℝ) * 𝒞 + (2 : ℝ) * 𝒮) := by
    linear_combination (((2 : ℝ) * 𝒞)) * hRS + ((0:ℝ)) * hSC + ((0:ℝ)) * hC2
  have hp : (0:ℝ) < (2 * 𝒮) ^ 1 := by positivity
  have h2 : (0:ℝ) < ((2 : ℝ) * 𝒞 + (2 : ℝ) * 𝒮) := by linarith
  rw [← e] at h2
  exact pos_of_mul_pos_right h2 hp.le

lemma cf7 : (0:ℝ) < (((5212031 : ℝ) / 5000000) + (-1 : ℝ) * 𝒞 + (-4 : ℝ) * 𝒞 * circumradius ^ 2 + (-4 : ℝ) * 𝒞 ^ 2 * circumradius ^ 2 + ((7270293 : ℝ) / 1250000) * 𝒞 * circumradius) := by
  have hRS := hRS'; have hSC := hSC'; have hC2 := hC2'; have hS := S_pos
  obtain ⟨hCl, hCh⟩ := C_bnd; obtain ⟨hSl, hSh⟩ := S_bnd; obtain ⟨hPl, hPh⟩ := P_bnd
  have e : (2 * 𝒮) ^ 2 * (((5212031 : ℝ) / 5000000) + (-1 : ℝ) * 𝒞 + (-4 : ℝ) * 𝒞 * circumradius ^ 2 + (-4 : ℝ) * 𝒞 ^ 2 * circumradius ^ 2 + ((7270293 : ℝ) / 1250000) * 𝒞 * circumradius) = (((13136093 : ℝ) / 5000000) + ((-25212031 : ℝ) / 2500000) * 𝒞 + ((7270293 : ℝ) / 625000) * 𝒞 * 𝒮) := by
    linear_combination (((-4 : ℝ) * 𝒞 + (-4 : ℝ) * 𝒞 ^ 2 + ((7270293 : ℝ) / 625000) * 𝒞 * 𝒮 + (-8 : ℝ) * 𝒞 * circumradius * 𝒮 + (-8 : ℝ) * circumradius * 𝒮 * 𝒞 ^ 2)) * hRS + ((((5212031 : ℝ) / 1250000) + (-4 : ℝ) * 𝒞)) * hSC + ((((-7712031 : ℝ) / 5000000) + (1 : ℝ) * 𝒞)) * hC2
  have hp : (0:ℝ) < (2 * 𝒮) ^ 2 := by positivity
  have h2 : (0:ℝ) < (((13136093 : ℝ) / 5000000) + ((-25212031 : ℝ) / 2500000) * 𝒞 + ((7270293 : ℝ) / 625000) * 𝒞 * 𝒮) := by linarith
  rw [← e] at h2
  exact pos_of_mul_pos_right h2 hp.le

lemma cf8 : (0:ℝ) < (((-10424033 : ℝ) / 10000000) + (1 : ℝ) * 𝒞 + (4 : ℝ) * 𝒞 * circumradius ^ 2 + (4 : ℝ) * 𝒞 ^ 2 * circumradius ^ 2 + ((-29081173 : ℝ) / 5000000) * 𝒞 * circumradius) := by
  have hRS := hRS'; have hSC := hSC'; have hC2 := hC2'; have hS := S_pos
  obtain ⟨hCl, hCh⟩ := C_bnd; obtain ⟨hSl, hSh⟩ := S_bnd; obtain ⟨hPl, hPh⟩ := P_bnd
  have e : (2 * 𝒮) ^ 2 * (((-10424033 : ℝ) / 10000000) + (1 : ℝ) * 𝒞 + (4 : ℝ) * 𝒞 * circumradius ^ 2 + (4 : ℝ) * 𝒞 ^ 2 * circumradius ^ 2 + ((-29081173 : ℝ) / 5000000) * 𝒞 * circumradius) = (((-26272099 : ℝ) / 10000000) + ((50424033 : ℝ) / 5000000) * 𝒞 + ((-29081173 : ℝ) / 2500000) * 𝒞 * 𝒮) := by
    linear_combination (((4 : ℝ) * 𝒞 + (4 : ℝ) * 𝒞 ^ 2 + ((-29081173 : ℝ) / 2500000) * 𝒞 * 𝒮 + (8 : ℝ) * 𝒞 * circumradius * 𝒮 + (8 : ℝ) * circumradius * 𝒮 * 𝒞 ^ 2)) * hRS + ((((-10424033 : ℝ) / 2500000) + (4 : ℝ) * 𝒞)) * hSC + ((((15424033 : ℝ) / 10000000) + (-1 : ℝ) * 𝒞)) * hC2
  have hp : (0:ℝ) < (2 * 𝒮) ^ 2 := by positivity
  have h2 : (0:ℝ) < (((-26272099 : ℝ) / 10000000) + ((50424033 : ℝ) / 5000000) * 𝒞 + ((-29081173 : ℝ) / 2500000) * 𝒞 * 𝒮) := by linarith
  rw [← e] at h2
  exact pos_of_mul_pos_right h2 hp.le

lemma cf9 : ((-1 : ℝ) * 𝒞 + (-1 : ℝ) * 𝒞 ^ 2 + (1 : ℝ) * 𝒞 * s3 + (-1 : ℝ) * 𝒞 * circumradius + (-1 : ℝ) * circumradius * 𝒞 ^ 2 + (2 : ℝ) * 𝒞 * circumradius * 𝒮 + (2 : ℝ) * 𝒞 * 𝒮 * circumradius ^ 2 + (2 : ℝ) * circumradius * 𝒮 * 𝒞 ^ 2 + (2 : ℝ) * 𝒮 * 𝒞 ^ 2 * circumradius ^ 2 + (-2 : ℝ) * 𝒞 * circumradius * 𝒮 * s3) = 0 := by
  have hRS := hRS'; have hSC := hSC'; have hC2 := hC2'; have hS := S_pos
  have e : (2 * 𝒮) ^ 2 * ((-1 : ℝ) * 𝒞 + (-1 : ℝ) * 𝒞 ^ 2 + (1 : ℝ) * 𝒞 * s3 + (-1 : ℝ) * 𝒞 * circumradius + (-1 : ℝ) * circumradius * 𝒞 ^ 2 + (2 : ℝ) * 𝒞 * circumradius * 𝒮 + (2 : ℝ) * 𝒞 * 𝒮 * circumradius ^ 2 + (2 : ℝ) * circumradius * 𝒮 * 𝒞 ^ 2 + (2 : ℝ) * 𝒮 * 𝒞 ^ 2 * circumradius ^ 2 + (-2 : ℝ) * 𝒞 * circumradius * 𝒮 * s3) = 0 := by
    linear_combination (((4 : ℝ) * 𝒞 * 𝒮 ^ 2 + (4 : ℝ) * 𝒞 ^ 2 * 𝒮 ^ 2 + (-4 : ℝ) * 𝒞 * s3 * 𝒮 ^ 2 + (4 : ℝ) * 𝒞 * circumradius * 𝒮 ^ 2 + (4 : ℝ) * circumradius * 𝒞 ^ 2 * 𝒮 ^ 2)) * hRS + ((0:ℝ)) * hSC + ((0:ℝ)) * hC2
  have hp : (2 * 𝒮) ^ 2 ≠ 0 := by positivity
  exact (mul_eq_zero.mp e).resolve_left hp

lemma cf10 : ((1 : ℝ) * 𝒞 * s3 + (-2 : ℝ) * 𝒞 * circumradius + (-2 : ℝ) * circumradius * 𝒞 ^ 2 + (4 : ℝ) * 𝒞 * 𝒮 * circumradius ^ 2 + (4 : ℝ) * 𝒮 * 𝒞 ^ 2 * circumradius ^ 2 + (-2 : ℝ) * 𝒞 * circumradius * 𝒮 * s3) = 0 := by
  have hRS := hRS'; have hSC := hSC'; have hC2 := hC2'; have hS := S_pos
  have e : (2 * 𝒮) ^ 2 * ((1 : ℝ) * 𝒞 * s3 + (-2 : ℝ) * 𝒞 * circumradius + (-2 : ℝ) * circumradius * 𝒞 ^ 2 + (4 : ℝ) * 𝒞 * 𝒮 * circumradius ^ 2 + (4 : ℝ) * 𝒮 * 𝒞 ^ 2 * circumradius ^ 2 + (-2 : ℝ) * 𝒞 * circumradius * 𝒮 * s3) = 0 := by
    linear_combination (((-4 : ℝ) * 𝒞 * s3 * 𝒮 ^ 2 + (8 : ℝ) * 𝒞 * circumradius * 𝒮 ^ 2 + (8 : ℝ) * circumradius * 𝒞 ^ 2 * 𝒮 ^ 2)) * hRS + ((0:ℝ)) * hSC + ((0:ℝ)) * hC2
  have hp : (2 * 𝒮) ^ 2 ≠ 0 := by positivity
  exact (mul_eq_zero.mp e).resolve_left hp

lemma cf11 : ((1 : ℝ) * 𝒞 ^ 3 + (1 : ℝ) * 𝒞 ^ 4 + (1 : ℝ) * 𝒞 * 𝒮 ^ 2 + (1 : ℝ) * 𝒮 * 𝒞 ^ 3 + (1 : ℝ) * 𝒞 ^ 2 * 𝒮 ^ 3 + (-1 : ℝ) * 𝒮 * 𝒞 ^ 4 + (2 : ℝ) * 𝒞 * 𝒮 ^ 3 + (2 : ℝ) * circumradius * 𝒞 ^ 4 + (2 : ℝ) * circumradius * 𝒞 ^ 5 + (2 : ℝ) * 𝒮 * 𝒞 ^ 2 + (2 : ℝ) * 𝒞 ^ 2 * 𝒮 ^ 2 + (-1 : ℝ) * 𝒞 * circumradius * 𝒮 ^ 3 + (-10 : ℝ) * 𝒞 ^ 3 * circumradius ^ 2 * 𝒮 ^ 2 + (-10 : ℝ) * 𝒞 ^ 4 * circumradius ^ 2 * 𝒮 ^ 2 + (-8 : ℝ) * 𝒞 ^ 2 * circumradius ^ 2 * 𝒮 ^ 3 + (-8 : ℝ) * 𝒞 ^ 3 * circumradius ^ 2 * 𝒮 ^ 3 + (-4 : ℝ) * 𝒞 * circumradius * 𝒮 ^ 4 + (-4 : ℝ) * 𝒮 * 𝒞 ^ 4 * circumradius ^ 2 + (-4 : ℝ) * 𝒮 * 𝒞 ^ 5 * circumradius ^ 2 + (-3 : ℝ) * circumradius * 𝒞 ^ 2 * 𝒮 ^ 3 + (-2 : ℝ) * 𝒞 * circumradius ^ 2 * 𝒮 ^ 4 + (-2 : ℝ) * circumradius * 𝒞 ^ 2 * 𝒮 ^ 4 + (-2 : ℝ) * 𝒞 ^ 2 * circumradius ^ 2 * 𝒮 ^ 4 + (2 : ℝ) * circumradius * 𝒞 ^ 3 * 𝒮 ^ 2 + (2 : ℝ) * circumradius * 𝒞 ^ 4 * 𝒮 ^ 2 + (3 : ℝ) * circumradius * 𝒮 * 𝒞 ^ 3 + (3 : ℝ) * circumradius * 𝒮 * 𝒞 ^ 4) = 0 := by
  have hRS := hRS'; have hSC := hSC'; have hC2 := hC2'; have hS := S_pos
  have e : (2 * 𝒮) ^ 2 * ((1 : ℝ) * 𝒞 ^ 3 + (1 : ℝ) * 𝒞 ^ 4 + (1 : ℝ) * 𝒞 * 𝒮 ^ 2 + (1 : ℝ) * 𝒮 * 𝒞 ^ 3 + (1 : ℝ) * 𝒞 ^ 2 * 𝒮 ^ 3 + (-1 : ℝ) * 𝒮 * 𝒞 ^ 4 + (2 : ℝ) * 𝒞 * 𝒮 ^ 3 + (2 : ℝ) * circumradius * 𝒞 ^ 4 + (2 : ℝ) * circumradius * 𝒞 ^ 5 + (2 : ℝ) * 𝒮 * 𝒞 ^ 2 + (2 : ℝ) * 𝒞 ^ 2 * 𝒮 ^ 2 + (-1 : ℝ) * 𝒞 * circumradius * 𝒮 ^ 3 + (-10 : ℝ) * 𝒞 ^ 3 * circumradius ^ 2 * 𝒮 ^ 2 + (-10 : ℝ) * 𝒞 ^ 4 * circumradius ^ 2 * 𝒮 ^ 2 + (-8 : ℝ) * 𝒞 ^ 2 * circumradius ^ 2 * 𝒮 ^ 3 + (-8 : ℝ) * 𝒞 ^ 3 * circumradius ^ 2 * 𝒮 ^ 3 + (-4 : ℝ) * 𝒞 * circumradius * 𝒮 ^ 4 + (-4 : ℝ) * 𝒮 * 𝒞 ^ 4 * circumradius ^ 2 + (-4 : ℝ) * 𝒮 * 𝒞 ^ 5 * circumradius ^ 2 + (-3 : ℝ) * circumradius * 𝒞 ^ 2 * 𝒮 ^ 3 + (-2 : ℝ) * 𝒞 * circumradius ^ 2 * 𝒮 ^ 4 + (-2 : ℝ) * circumradius * 𝒞 ^ 2 * 𝒮 ^ 4 + (-2 : ℝ) * 𝒞 ^ 2 * circumradius ^ 2 * 𝒮 ^ 4 + (2 : ℝ) * circumradius * 𝒞 ^ 3 * 𝒮 ^ 2 + (2 : ℝ) * circumradius * 𝒞 ^ 4 * 𝒮 ^ 2 + (3 : ℝ) * circumradius * 𝒮 * 𝒞 ^ 3 + (3 : ℝ) * circumradius * 𝒮 * 𝒞 ^ 4) = 0 := by
    linear_combination (((-8 : ℝ) * 𝒞 * 𝒮 ^ 5 + (-8 : ℝ) * 𝒞 ^ 2 * 𝒮 ^ 3 + (-8 : ℝ) * 𝒞 ^ 2 * 𝒮 ^ 4 + (-4 : ℝ) * 𝒞 * 𝒮 ^ 4 + (-4 : ℝ) * 𝒞 ^ 2 * 𝒮 ^ 5 + (-4 : ℝ) * 𝒞 ^ 3 * 𝒮 ^ 2 + (-4 : ℝ) * 𝒞 ^ 3 * 𝒮 ^ 3 + (-4 : ℝ) * 𝒞 ^ 4 * 𝒮 ^ 2 + (4 : ℝ) * 𝒞 ^ 4 * 𝒮 ^ 3 + (-20 : ℝ) * circumradius * 𝒞 ^ 3 * 𝒮 ^ 3 + (-20 : ℝ) * circumradius * 𝒞 ^ 4 * 𝒮 ^ 3 + (-16 : ℝ) * circumradius * 𝒞 ^ 2 * 𝒮 ^ 4 + (-16 : ℝ) * circumradius * 𝒞 ^ 3 * 𝒮 ^ 4 + (-8 : ℝ) * circumradius * 𝒞 ^ 4 * 𝒮 ^ 2 + (-8 : ℝ) * circumradius * 𝒞 ^ 5 * 𝒮 ^ 2 + (-4 : ℝ) * 𝒞 * circumradius * 𝒮 ^ 5 + (-4 : ℝ) * circumradius * 𝒞 ^ 2 * 𝒮 ^ 5)) * hRS + ((0:ℝ)) * hSC + ((0:ℝ)) * hC2
  have hp : (2 * 𝒮) ^ 2 ≠ 0 := by positivity
  exact (mul_eq_zero.mp e).resolve_left hp

lemma cf12 : (0:ℝ) < (((1614673 : ℝ) / 1000000) + (2 : ℝ) * 𝒞 * circumradius * 𝒮) := by
  have hRS := hRS'; have hSC := hSC'; have hC2 := hC2'; have hS := S_pos
  obtain ⟨hCl, hCh⟩ := C_bnd; obtain ⟨hSl, hSh⟩ := S_bnd; obtain ⟨hPl, hPh⟩ := P_bnd
  have e : (2 * 𝒮) ^ 1 * (((1614673 : ℝ) / 1000000) + (2 : ℝ) * 𝒞 * circumradius * 𝒮) = (((1614673 : ℝ) / 500000) * 𝒮 + (2 : ℝ) * 𝒞 * 𝒮) := by
    linear_combination (((2 : ℝ) * 𝒞 * 𝒮)) * hRS + ((0:ℝ)) * hSC + ((0:ℝ)) * hC2
  have hp : (0:ℝ) < (2 * 𝒮) ^ 1 := by positivity
  have h2 : (0:ℝ) < (((1614673 : ℝ) / 500000) * 𝒮 + (2 : ℝ) * 𝒞 * 𝒮) := by linarith
  rw [← e] at h2
  exact pos_of_mul_pos_right h2 hp.le

lemma cf13 : (0:ℝ) < (((6467211 : ℝ) / 5000000) + (-2 : ℝ) * 𝒞 * circumradius * 𝒮) := by
  have hRS := hRS'; have hSC := hSC'; have hC2 := hC2'; have hS := S_pos
  obtain ⟨hCl, hCh⟩ := C_bnd; obtain ⟨hSl, hSh⟩ := S_bnd; obtain ⟨hPl, hPh⟩ := P_bnd
  have e : (2 * 𝒮) ^ 1 * (((6467211 : ℝ) / 5000000) + (-2 : ℝ) * 𝒞 * circumradius * 𝒮) = (((6467211 : ℝ) / 2500000) * 𝒮 + (-2 : ℝ) * 𝒞 * 𝒮) := by
    linear_combination (((-2 : ℝ) * 𝒞 * 𝒮)) * hRS + ((0:ℝ)) * hSC + ((0:ℝ)) * hC2
  have hp : (0:ℝ) < (2 * 𝒮) ^ 1 := by positivity
  have h2 : (0:ℝ) < (((6467211 : ℝ) / 2500000) * 𝒮 + (-2 : ℝ) * 𝒞 * 𝒮) := by linarith
  rw [← e] at h2
  exact pos_of_mul_pos_right h2 hp.le

lemma cf14 : (0:ℝ) ≤ ((-1 : ℝ) * circumradius + (1 : ℝ) * 𝒞 * circumradius + (2 : ℝ) * circumradius * 𝒞 ^ 2) := by
  have hRS := hRS'; have hSC := hSC'; have hC2 := hC2'; have hS := S_pos
  obtain ⟨hCl, hCh⟩ := C_bnd; obtain ⟨hSl, hSh⟩ := S_bnd; obtain ⟨hPl, hPh⟩ := P_bnd
  have e : (2 * 𝒮) ^ 1 * ((-1 : ℝ) * circumradius + (1 : ℝ) * 𝒞 * circumradius + (2 : ℝ) * circumradius * 𝒞 ^ 2) = (((-1 : ℝ) / 2) + (2 : ℝ) * 𝒞) := by
    linear_combination (((-1 : ℝ) + (1 : ℝ) * 𝒞 + (2 : ℝ) * 𝒞 ^ 2)) * hRS + ((0:ℝ)) * hSC + ((((1 : ℝ) / 2))) * hC2
  have hp : (0:ℝ) < (2 * 𝒮) ^ 1 := by positivity
  have h2 : (0:ℝ) < (((-1 : ℝ) / 2) + (2 : ℝ) * 𝒞) := by linarith
  rw [← e] at h2
  exact (pos_of_mul_pos_right h2 hp.le).le

lemma cf15 : (0:ℝ) < (((7270293 : ℝ) / 2500000) + (1 : ℝ) * circumradius + (-1 : ℝ) * 𝒞 * circumradius + (-2 : ℝ) * circumradius * 𝒞 ^ 2) := by
  have hRS := hRS'; have hSC := hSC'; have hC2 := hC2'; have hS := S_pos
  obtain ⟨hCl, hCh⟩ := C_bnd; obtain ⟨hSl, hSh⟩ := S_bnd; obtain ⟨hPl, hPh⟩ := P_bnd
  have e : (2 * 𝒮) ^ 1 * (((7270293 : ℝ) / 2500000) + (1 : ℝ) * circumradius + (-1 : ℝ) * 𝒞 * circumradius + (-2 : ℝ) * circumradius * 𝒞 ^ 2) = (((1 : ℝ) / 2) + (-2 : ℝ) * 𝒞 + ((7270293 : ℝ) / 1250000) * 𝒮) := by
    linear_combination (((1 : ℝ) + (-1 : ℝ) * 𝒞 + (-2 : ℝ) * 𝒞 ^ 2)) * hRS + ((0:ℝ)) * hSC + ((((-1 : ℝ) / 2))) * hC2
  have hp : (0:ℝ) < (2 * 𝒮) ^ 1 := by positivity
  have h2 : (0:ℝ) < (((1 : ℝ) / 2) + (-2 : ℝ) * 𝒞 + ((7270293 : ℝ) / 1250000) * 𝒮) := by linarith
  rw [← e] at h2
  exact pos_of_mul_pos_right h2 hp.le

lemma cf16 : (0:ℝ) < (((1614673 : ℝ) / 1000000)) := by
  have hRS := hRS'; have hSC := hSC'; have hC2 := hC2'; have hS := S_pos
  obtain ⟨hCl, hCh⟩ := C_bnd; obtain ⟨hSl, hSh⟩ := S_bnd; obtain ⟨hPl, hPh⟩ := P_bnd
  have e : (2 * 𝒮) ^ 0 * (((1614673 : ℝ) / 1000000)) = (((1614673 : ℝ) / 1000000)) := by
    linear_combination ((0:ℝ)) * hRS + ((0:ℝ)) * hSC + ((0:ℝ)) * hC2
  have hp : (0:ℝ) < (2 * 𝒮) ^ 0 := by positivity
  have h2 : (0:ℝ) < (((1614673 : ℝ) / 1000000)) := by linarith
  rw [← e] at h2
  exact pos_of_mul_pos_right h2 hp.le

lemma cf17 : (0:ℝ) < (((6467211 : ℝ) / 5000000)) := by
  have hRS := hRS'; have hSC := hSC'; have hC2 := hC2'; have hS := S_pos
  obtain ⟨hCl, hCh⟩ := C_bnd; obtain ⟨hSl, hSh⟩ := S_bnd; obtain ⟨hPl, hPh⟩ := P_bnd
  have e : (2 * 𝒮) ^ 0 * (((6467211 : ℝ) / 5000000)) = (((6467211 : ℝ) / 5000000)) := by
    linear_combination ((0:ℝ)) * hRS + ((0:ℝ)) * hSC + ((0:ℝ)) * hC2
  have hp : (0:ℝ) < (2 * 𝒮) ^ 0 := by positivity
  have h2 : (0:ℝ) < (((6467211 : ℝ) / 5000000)) := by linarith
  rw [← e] at h2
  exact pos_of_mul_pos_right h2 hp.le

lemma cf18 : (0:ℝ) ≤ ((1 : ℝ) * circumradius + (1 : ℝ) * 𝒞 * circumradius) := by
  have hRS := hRS'; have hSC := hSC'; have hC2 := hC2'; have hS := S_pos
  obtain ⟨hCl, hCh⟩ := C_bnd; obtain ⟨hSl, hSh⟩ := S_bnd; obtain ⟨hPl, hPh⟩ := P_bnd
  have e : (2 * 𝒮) ^ 1 * ((1 : ℝ) * circumradius + (1 : ℝ) * 𝒞 * circumradius) = ((1 : ℝ) + (1 : ℝ) * 𝒞) := by
    linear_combination (((1 : ℝ) + (1 : ℝ) * 𝒞)) * hRS + ((0:ℝ)) * hSC + ((0:ℝ)) * hC2
  have hp : (0:ℝ) < (2 * 𝒮) ^ 1 := by positivity
  have h2 : (0:ℝ) < ((1 : ℝ) + (1 : ℝ) * 𝒞) := by linarith
  rw [← e] at h2
  exact (pos_of_mul_pos_right h2 hp.le).le

lemma cf19 : (0:ℝ) < (((7270293 : ℝ) / 2500000) + (-1 : ℝ) * circumradius + (-1 : ℝ) * 𝒞 * circumradius) := by
  have hRS := hRS'; have hSC := hSC'; have hC2 := hC2'; have hS := S_pos
  obtain ⟨hCl, hCh⟩ := C_bnd; obtain ⟨hSl, hSh⟩ := S_bnd; obtain ⟨hPl, hPh⟩ := P_bnd
  have e : (2 * 𝒮) ^ 1 * (((7270293 : ℝ) / 2500000) + (-1 : ℝ) * circumradius + (-1 : ℝ) * 𝒞 * circumradius) = ((-1 : ℝ) + (-1 : ℝ) * 𝒞 + ((7270293 : ℝ) / 1250000) * 𝒮) := by
    linear_combination (((-1 : ℝ) + (-1 : ℝ) * 𝒞)) * hRS + ((0:ℝ)) * hSC + ((0:ℝ)) * hC2
  have hp : (0:ℝ) < (2 * 𝒮) ^ 1 := by positivity
  have h2 : (0:ℝ) < ((-1 : ℝ) + (-1 : ℝ) * 𝒞 + ((7270293 : ℝ) / 1250000) * 𝒮) := by linarith
  rw [← e] at h2
  exact pos_of_mul_pos_right h2 hp.le

lemma cf20 : (0:ℝ) < (((1614673 : ℝ) / 1000000) + (-2 : ℝ) * 𝒞 * circumradius * 𝒮) := by
  have hRS := hRS'; have hSC := hSC'; have hC2 := hC2'; have hS := S_pos
  obtain ⟨hCl, hCh⟩ := C_bnd; obtain ⟨hSl, hSh⟩ := S_bnd; obtain ⟨hPl, hPh⟩ := P_bnd
  have e : (2 * 𝒮) ^ 1 * (((1614673 : ℝ) / 1000000) + (-2 : ℝ) * 𝒞 * circumradius * 𝒮) = (((1614673 : ℝ) / 500000) * 𝒮 + (-2 : ℝ) * 𝒞 * 𝒮) := by
    linear_combination (((-2 : ℝ) * 𝒞 * 𝒮)) * hRS + ((0:ℝ)) * hSC + ((0:ℝ)) * hC2
  have hp : (0:ℝ) < (2 * 𝒮) ^ 1 := by positivity
  have h2 : (0:ℝ) < (((1614673 : ℝ) / 500000) * 𝒮 + (-2 : ℝ) * 𝒞 * 𝒮) := by linarith
  rw [← e] at h2
  exact pos_of_mul_pos_right h2 hp.le

lemma cf21 : (0:ℝ) < (((6467211 : ℝ) / 5000000) + (2 : ℝ) * 𝒞 * circumradius * 𝒮) := by
  have hRS := hRS'; have hSC := hSC'; have hC2 := hC2'; have hS := S_pos
  obtain ⟨hCl, hCh⟩ := C_bnd; obtain ⟨hSl, hSh⟩ := S_bnd; obtain ⟨hPl, hPh⟩ := P_bnd
  have e : (2 * 𝒮) ^ 1 * (((6467211 : ℝ) / 5000000) + (2 : ℝ) * 𝒞 * circumradius * 𝒮) = (((6467211 : ℝ) / 2500000) * 𝒮 + (2 : ℝ) * 𝒞 * 𝒮) := by
    linear_combination (((2 : ℝ) * 𝒞 * 𝒮)) * hRS + ((0:ℝ)) * hSC + ((0:ℝ)) * hC2
  have hp : (0:ℝ) < (2 * 𝒮) ^ 1 := by positivity
  have h2 : (0:ℝ) < (((6467211 : ℝ) / 2500000) * 𝒮 + (2 : ℝ) * 𝒞 * 𝒮) := by linarith
  rw [← e] at h2
  exact pos_of_mul_pos_right h2 hp.le

lemma cf22 : (0:ℝ) ≤ ((-1 : ℝ) * circumradius + (1 : ℝ) * 𝒞 * circumradius + (2 : ℝ) * circumradius * 𝒞 ^ 2) := by
  have hRS := hRS'; have hSC := hSC'; have hC2 := hC2'; have hS := S_pos
  obtain ⟨hCl, hCh⟩ := C_bnd; obtain ⟨hSl, hSh⟩ := S_bnd; obtain ⟨hPl, hPh⟩ := P_bnd
  have e : (2 * 𝒮) ^ 1 * ((-1 : ℝ) * circumradius + (1 : ℝ) * 𝒞 * circumradius + (2 : ℝ) * circumradius * 𝒞 ^ 2) = (((-1 : ℝ) / 2) + (2 : ℝ) * 𝒞) := by
    linear_combination (((-1 : ℝ) + (1 : ℝ) * 𝒞 + (2 : ℝ) * 𝒞 ^ 2)) * hRS + ((0:ℝ)) * hSC + ((((1 : ℝ) / 2))) * hC2
  have hp : (0:ℝ) < (2 * 𝒮) ^ 1 := by positivity
  have h2 : (0:ℝ) < (((-1 : ℝ) / 2) + (2 : ℝ) * 𝒞) := by linarith
  rw [← e] at h2
  exact (pos_of_mul_pos_right h2 hp.le).le

lemma cf23 : (0:ℝ) < (((7270293 : ℝ) / 2500000) + (1 : ℝ) * circumradius + (-1 : ℝ) * 𝒞 * circumradius + (-2 : ℝ) * circumradius * 𝒞 ^ 2) := by
  have hRS := hRS'; have hSC := hSC'; have hC2 := hC2'; have hS := S_pos
  obtain ⟨hCl, hCh⟩ := C_bnd; obtain ⟨hSl, hSh⟩ := S_bnd; obtain ⟨hPl, hPh⟩ := P_bnd
  have e : (2 * 𝒮) ^ 1 * (((7270293 : ℝ) / 2500000) + (1 : ℝ) * circumradius + (-1 : ℝ) * 𝒞 * circumradius + (-2 : ℝ) * circumradius * 𝒞 ^ 2) = (((1 : ℝ) / 2) + (-2 : ℝ) * 𝒞 + ((7270293 : ℝ) / 1250000) * 𝒮) := by
    linear_combination (((1 : ℝ) + (-1 : ℝ) * 𝒞 + (-2 : ℝ) * 𝒞 ^ 2)) * hRS + ((0:ℝ)) * hSC + ((((-1 : ℝ) / 2))) * hC2
  have hp : (0:ℝ) < (2 * 𝒮) ^ 1 := by positivity
  have h2 : (0:ℝ) < (((1 : ℝ) / 2) + (-2 : ℝ) * 𝒞 + ((7270293 : ℝ) / 1250000) * 𝒮) := by linarith
  rw [← e] at h2
  exact pos_of_mul_pos_right h2 hp.le

lemma cf24 : (0:ℝ) < (((1614673 : ℝ) / 1000000) + (-1 : ℝ) * circumradius * 𝒮) := by
  have hRS := hRS'; have hSC := hSC'; have hC2 := hC2'; have hS := S_pos
  obtain ⟨hCl, hCh⟩ := C_bnd; obtain ⟨hSl, hSh⟩ := S_bnd; obtain ⟨hPl, hPh⟩ := P_bnd
  have e : (2 * 𝒮) ^ 1 * (((1614673 : ℝ) / 1000000) + (-1 : ℝ) * circumradius * 𝒮) = (((1114673 : ℝ) / 500000) * 𝒮) := by
    linear_combination (((-1 : ℝ) * 𝒮)) * hRS + ((0:ℝ)) * hSC + ((0:ℝ)) * hC2
  have hp : (0:ℝ) < (2 * 𝒮) ^ 1 := by positivity
  have h2 : (0:ℝ) < (((1114673 : ℝ) / 500000) * 𝒮) := by linarith
  rw [← e] at h2
  exact pos_of_mul_pos_right h2 hp.le

lemma cf25 : (0:ℝ) < (((6467211 : ℝ) / 5000000) + (1 : ℝ) * circumradius * 𝒮) := by
  have hRS := hRS'; have hSC := hSC'; have hC2 := hC2'; have hS := S_pos
  obtain ⟨hCl, hCh⟩ := C_bnd; obtain ⟨hSl, hSh⟩ := S_bnd; obtain ⟨hPl, hPh⟩ := P_bnd
  have e : (2 * 𝒮) ^ 1 * (((6467211 : ℝ) / 5000000) + (1 : ℝ) * circumradius * 𝒮) = (((8967211 : ℝ) / 2500000) * 𝒮) := by
    linear_combination (((1 : ℝ) * 𝒮)) * hRS + ((0:ℝ)) * hSC + ((0:ℝ)) * hC2
  have hp : (0:ℝ) < (2 * 𝒮) ^ 1 := by positivity
  have h2 : (0:ℝ) < (((8967211 : ℝ) / 2500000) * 𝒮) := by linarith
  rw [← e] at h2
  exact pos_of_mul_pos_right h2 hp.le

lemma cf26 : (0:ℝ) ≤ (0:ℝ) := by
  have hRS := hRS'; have hSC := hSC'; have hC2 := hC2'; have hS := S_pos
  obtain ⟨hCl, hCh⟩ := C_bnd; obtain ⟨hSl, hSh⟩ := S_bnd; obtain ⟨hPl, hPh⟩ := P_bnd
  have e : (2 * 𝒮) ^ 0 * (0:ℝ) = (0:ℝ) := by
    linear_combination ((0:ℝ)) * hRS + ((0:ℝ)) * hSC + ((0:ℝ)) * hC2
  have hp : (0:ℝ) < (2 * 𝒮) ^ 0 := by positivity
  have : (2 * 𝒮) ^ 0 * (0:ℝ) = 0 := by rw [e]
  exact le_of_eq ((mul_eq_zero.mp this).resolve_left hp.ne').symm

lemma cf27 : (0:ℝ) < (((7270293 : ℝ) / 2500000)) := by
  have hRS := hRS'; have hSC := hSC'; have hC2 := hC2'; have hS := S_pos
  obtain ⟨hCl, hCh⟩ := C_bnd; obtain ⟨hSl, hSh⟩ := S_bnd; obtain ⟨hPl, hPh⟩ := P_bnd
  have e : (2 * 𝒮) ^ 0 * (((7270293 : ℝ) / 2500000)) = (((7270293 : ℝ) / 2500000)) := by
    linear_combination ((0:ℝ)) * hRS + ((0:ℝ)) * hSC + ((0:ℝ)) * hC2
  have hp : (0:ℝ) < (2 * 𝒮) ^ 0 := by positivity
  have h2 : (0:ℝ) < (((7270293 : ℝ) / 2500000)) := by linarith
  rw [← e] at h2
  exact pos_of_mul_pos_right h2 hp.le

lemma cf28 : (0:ℝ) < (((1614673 : ℝ) / 1000000) + (1 : ℝ) * circumradius * 𝒮) := by
  have hRS := hRS'; have hSC := hSC'; have hC2 := hC2'; have hS := S_pos
  obtain ⟨hCl, hCh⟩ := C_bnd; obtain ⟨hSl, hSh⟩ := S_bnd; obtain ⟨hPl, hPh⟩ := P_bnd
  have e : (2 * 𝒮) ^ 1 * (((1614673 : ℝ) / 1000000) + (1 : ℝ) * circumradius * 𝒮) = (((2114673 : ℝ) / 500000) * 𝒮) := by
    linear_combination (((1 : ℝ) * 𝒮)) * hRS + ((0:ℝ)) * hSC + ((0:ℝ)) * hC2
  have hp : (0:ℝ) < (2 * 𝒮) ^ 1 := by positivity
  have h2 : (0:ℝ) < (((2114673 : ℝ) / 500000) * 𝒮) := by linarith
  rw [← e] at h2
  exact pos_of_mul_pos_right h2 hp.le

lemma cf29 : (0:ℝ) < (((6467211 : ℝ) / 5000000) + (-1 : ℝ) * circumradius * 𝒮) := by
  have hRS := hRS'; have hSC := hSC'; have hC2 := hC2'; have hS := S_pos
  obtain ⟨hCl, hCh⟩ := C_bnd; obtain ⟨hSl, hSh⟩ := S_bnd; obtain ⟨hPl, hPh⟩ := P_bnd
  have e : (2 * 𝒮) ^ 1 * (((6467211 : ℝ) / 5000000) + (-1 : ℝ) * circumradius * 𝒮) = (((3967211 : ℝ) / 2500000) * 𝒮) := by
    linear_combination (((-1 : ℝ) * 𝒮)) * hRS + ((0:ℝ)) * hSC + ((0:ℝ)) * hC2
  have hp : (0:ℝ) < (2 * 𝒮) ^ 1 := by positivity
  have h2 : (0:ℝ) < (((3967211 : ℝ) / 2500000) * 𝒮) := by linarith
  rw [← e] at h2
  exact pos_of_mul_pos_right h2 hp.le

lemma cf30 : (0:ℝ) ≤ (0:ℝ) := by
  have hRS := hRS'; have hSC := hSC'; have hC2 := hC2'; have hS := S_pos
  obtain ⟨hCl, hCh⟩ := C_bnd; obtain ⟨hSl, hSh⟩ := S_bnd; obtain ⟨hPl, hPh⟩ := P_bnd
  have e : (2 * 𝒮) ^ 0 * (0:ℝ) = (0:ℝ) := by
    linear_combination ((0:ℝ)) * hRS + ((0:ℝ)) * hSC + ((0:ℝ)) * hC2
  have hp : (0:ℝ) < (2 * 𝒮) ^ 0 := by positivity
  have : (2 * 𝒮) ^ 0 * (0:ℝ) = 0 := by rw [e]
  exact le_of_eq ((mul_eq_zero.mp this).resolve_left hp.ne').symm

lemma cf31 : (0:ℝ) < (((7270293 : ℝ) / 2500000)) := by
  have hRS := hRS'; have hSC := hSC'; have hC2 := hC2'; have hS := S_pos
  obtain ⟨hCl, hCh⟩ := C_bnd; obtain ⟨hSl, hSh⟩ := S_bnd; obtain ⟨hPl, hPh⟩ := P_bnd
  have e : (2 * 𝒮) ^ 0 * (((7270293 : ℝ) / 2500000)) = (((7270293 : ℝ) / 2500000)) := by
    linear_combination ((0:ℝ)) * hRS + ((0:ℝ)) * hSC + ((0:ℝ)) * hC2
  have hp : (0:ℝ) < (2 * 𝒮) ^ 0 := by positivity
  have h2 : (0:ℝ) < (((7270293 : ℝ) / 2500000)) := by linarith
  rw [← e] at h2
  exact pos_of_mul_pos_right h2 hp.le

lemma cf32 : (0:ℝ) < (((7270293 : ℝ) / 2500000)) := by
  have hRS := hRS'; have hSC := hSC'; have hC2 := hC2'; have hS := S_pos
  obtain ⟨hCl, hCh⟩ := C_bnd; obtain ⟨hSl, hSh⟩ := S_bnd; obtain ⟨hPl, hPh⟩ := P_bnd
  have e : (2 * 𝒮) ^ 0 * (((7270293 : ℝ) / 2500000)) = (((7270293 : ℝ) / 2500000)) := by
    linear_combination ((0:ℝ)) * hRS + ((0:ℝ)) * hSC + ((0:ℝ)) * hC2
  have hp : (0:ℝ) < (2 * 𝒮) ^ 0 := by positivity
  have h2 : (0:ℝ) < (((7270293 : ℝ) / 2500000)) := by linarith
  rw [← e] at h2
  exact pos_of_mul_pos_right h2 hp.le

lemma cf33 : (0:ℝ) ≤ (0:ℝ) := by
  have hRS := hRS'; have hSC := hSC'; have hC2 := hC2'; have hS := S_pos
  obtain ⟨hCl, hCh⟩ := C_bnd; obtain ⟨hSl, hSh⟩ := S_bnd; obtain ⟨hPl, hPh⟩ := P_bnd
  have e : (2 * 𝒮) ^ 0 * (0:ℝ) = (0:ℝ) := by
    linear_combination ((0:ℝ)) * hRS + ((0:ℝ)) * hSC + ((0:ℝ)) * hC2
  have hp : (0:ℝ) < (2 * 𝒮) ^ 0 := by positivity
  have : (2 * 𝒮) ^ 0 * (0:ℝ) = 0 := by rw [e]
  exact le_of_eq ((mul_eq_zero.mp this).resolve_left hp.ne').symm

lemma cf34 : (0:ℝ) < (((7270293 : ℝ) / 2500000) + (-1 : ℝ) * 𝒞 + (1 : ℝ) * circumradius * 𝒮) := by
  have hRS := hRS'; have hSC := hSC'; have hC2 := hC2'; have hS := S_pos
  obtain ⟨hCl, hCh⟩ := C_bnd; obtain ⟨hSl, hSh⟩ := S_bnd; obtain ⟨hPl, hPh⟩ := P_bnd
  have e : (2 * 𝒮) ^ 1 * (((7270293 : ℝ) / 2500000) + (-1 : ℝ) * 𝒞 + (1 : ℝ) * circumradius * 𝒮) = (((8520293 : ℝ) / 1250000) * 𝒮 + (-2 : ℝ) * 𝒞 * 𝒮) := by
    linear_combination (((1 : ℝ) * 𝒮)) * hRS + ((0:ℝ)) * hSC + ((0:ℝ)) * hC2
  have hp : (0:ℝ) < (2 * 𝒮) ^ 1 := by positivity
  have h2 : (0:ℝ) < (((8520293 : ℝ) / 1250000) * 𝒮 + (-2 : ℝ) * 𝒞 * 𝒮) := by linarith
  rw [← e] at h2
  exact pos_of_mul_pos_right h2 hp.le

lemma cf35 : (0:ℝ) ≤ ((1 : ℝ) * 𝒞 + (-1 : ℝ) * circumradius * 𝒮) := by
  have hRS := hRS'; have hSC := hSC'; have hC2 := hC2'; have hS := S_pos
  obtain ⟨hCl, hCh⟩ := C_bnd; obtain ⟨hSl, hSh⟩ := S_bnd; obtain ⟨hPl, hPh⟩ := P_bnd
  have e : (2 * 𝒮) ^ 1 * ((1 : ℝ) * 𝒞 + (-1 : ℝ) * circumradius * 𝒮) = ((-1 : ℝ) * 𝒮 + (2 : ℝ) * 𝒞 * 𝒮) := by
    linear_combination (((-1 : ℝ) * 𝒮)) * hRS + ((0:ℝ)) * hSC + ((0:ℝ)) * hC2
  have hp : (0:ℝ) < (2 * 𝒮) ^ 1 := by positivity
  have h2 : (0:ℝ) < ((-1 : ℝ) * 𝒮 + (2 : ℝ) * 𝒞 * 𝒮) := by linarith
  rw [← e] at h2
  exact (pos_of_mul_pos_right h2 hp.le).le

lemma cf36 : (0:ℝ) < (((7270293 : ℝ) / 2500000) + (1 : ℝ) * circumradius + (-1 : ℝ) * 𝒞 * circumradius + (-2 : ℝ) * circumradius * 𝒞 ^ 2) := by
  have hRS := hRS'; have hSC := hSC'; have hC2 := hC2'; have hS := S_pos
  obtain ⟨hCl, hCh⟩ := C_bnd; obtain ⟨hSl, hSh⟩ := S_bnd; obtain ⟨hPl, hPh⟩ := P_bnd
  have e : (2 * 𝒮) ^ 1 * (((7270293 : ℝ) / 2500000) + (1 : ℝ) * circumradius + (-1 : ℝ) * 𝒞 * circumradius + (-2 : ℝ) * circumradius * 𝒞 ^ 2) = (((1 : ℝ) / 2) + (-2 : ℝ) * 𝒞 + ((7270293 : ℝ) / 1250000) * 𝒮) := by
    linear_combination (((1 : ℝ) + (-1 : ℝ) * 𝒞 + (-2 : ℝ) * 𝒞 ^ 2)) * hRS + ((0:ℝ)) * hSC + ((((-1 : ℝ) / 2))) * hC2
  have hp : (0:ℝ) < (2 * 𝒮) ^ 1 := by positivity
  have h2 : (0:ℝ) < (((1 : ℝ) / 2) + (-2 : ℝ) * 𝒞 + ((7270293 : ℝ) / 1250000) * 𝒮) := by linarith
  rw [← e] at h2
  exact pos_of_mul_pos_right h2 hp.le

lemma cf37 : (0:ℝ) ≤ ((-1 : ℝ) * circumradius + (1 : ℝ) * 𝒞 * circumradius + (2 : ℝ) * circumradius * 𝒞 ^ 2) := by
  have hRS := hRS'; have hSC := hSC'; have hC2 := hC2'; have hS := S_pos
  obtain ⟨hCl, hCh⟩ := C_bnd; obtain ⟨hSl, hSh⟩ := S_bnd; obtain ⟨hPl, hPh⟩ := P_bnd
  have e : (2 * 𝒮) ^ 1 * ((-1 : ℝ) * circumradius + (1 : ℝ) * 𝒞 * circumradius + (2 : ℝ) * circumradius * 𝒞 ^ 2) = (((-1 : ℝ) / 2) + (2 : ℝ) * 𝒞) := by
    linear_combination (((-1 : ℝ) + (1 : ℝ) * 𝒞 + (2 : ℝ) * 𝒞 ^ 2)) * hRS + ((0:ℝ)) * hSC + ((((1 : ℝ) / 2))) * hC2
  have hp : (0:ℝ) < (2 * 𝒮) ^ 1 := by positivity
  have h2 : (0:ℝ) < (((-1 : ℝ) / 2) + (2 : ℝ) * 𝒞) := by linarith
  rw [← e] at h2
  exact (pos_of_mul_pos_right h2 hp.le).le

lemma cf38 : (0:ℝ) < (((7270293 : ℝ) / 2500000) + (-1 : ℝ) * 𝒞 + (2 : ℝ) * 𝒞 * circumradius * 𝒮) := by
  have hRS := hRS'; have hSC := hSC'; have hC2 := hC2'; have hS := S_pos
  obtain ⟨hCl, hCh⟩ := C_bnd; obtain ⟨hSl, hSh⟩ := S_bnd; obtain ⟨hPl, hPh⟩ := P_bnd
  have e : (2 * 𝒮) ^ 1 * (((7270293 : ℝ) / 2500000) + (-1 : ℝ) * 𝒞 + (2 : ℝ) * 𝒞 * circumradius * 𝒮) = (((7270293 : ℝ) / 1250000) * 𝒮) := by
    linear_combination (((2 : ℝ) * 𝒞 * 𝒮)) * hRS + ((0:ℝ)) * hSC + ((0:ℝ)) * hC2
  have hp : (0:ℝ) < (2 * 𝒮) ^ 1 := by positivity
  have h2 : (0:ℝ) < (((7270293 : ℝ) / 1250000) * 𝒮) := by linarith
  rw [← e] at h2
  exact pos_of_mul_pos_right h2 hp.le

lemma cf39 : (0:ℝ) ≤ ((1 : ℝ) * 𝒞 + (-2 : ℝ) * 𝒞 * circumradius * 𝒮) := by
  have hRS := hRS'; have hSC := hSC'; have hC2 := hC2'; have hS := S_pos
  obtain ⟨hCl, hCh⟩ := C_bnd; obtain ⟨hSl, hSh⟩ := S_bnd; obtain ⟨hPl, hPh⟩ := P_bnd
  have e : (2 * 𝒮) ^ 1 * ((1 : ℝ) * 𝒞 + (-2 : ℝ) * 𝒞 * circumradius * 𝒮) = (0:ℝ) := by
    linear_combination (((-2 : ℝ) * 𝒞 * 𝒮)) * hRS + ((0:ℝ)) * hSC + ((0:ℝ)) * hC2
  have hp : (0:ℝ) < (2 * 𝒮) ^ 1 := by positivity
  have : (2 * 𝒮) ^ 1 * ((1 : ℝ) * 𝒞 + (-2 : ℝ) * 𝒞 * circumradius * 𝒮) = 0 := by rw [e]
  exact le_of_eq ((mul_eq_zero.mp this).resolve_left hp.ne').symm

lemma cf40 : (0:ℝ) < (((7270293 : ℝ) / 2500000) + (-1 : ℝ) * circumradius + (-1 : ℝ) * 𝒞 * circumradius) := by
  have hRS := hRS'; have hSC := hSC'; have hC2 := hC2'; have hS := S_pos
  obtain ⟨hCl, hCh⟩ := C_bnd; obtain ⟨hSl, hSh⟩ := S_bnd; obtain ⟨hPl, hPh⟩ := P_bnd
  have e : (2 * 𝒮) ^ 1 * (((7270293 : ℝ) / 2500000) + (-1 : ℝ) * circumradius + (-1 : ℝ) * 𝒞 * circumradius) = ((-1 : ℝ) + (-1 : ℝ) * 𝒞 + ((7270293 : ℝ) / 1250000) * 𝒮) := by
    linear_combination (((-1 : ℝ) + (-1 : ℝ) * 𝒞)) * hRS + ((0:ℝ)) * hSC + ((0:ℝ)) * hC2
  have hp : (0:ℝ) < (2 * 𝒮) ^ 1 := by positivity
  have h2 : (0:ℝ) < ((-1 : ℝ) + (-1 : ℝ) * 𝒞 + ((7270293 : ℝ) / 1250000) * 𝒮) := by linarith
  rw [← e] at h2
  exact pos_of_mul_pos_right h2 hp.le

lemma cf41 : (0:ℝ) ≤ ((1 : ℝ) * circumradius + (1 : ℝ) * 𝒞 * circumradius) := by
  have hRS := hRS'; have hSC := hSC'; have hC2 := hC2'; have hS := S_pos
  obtain ⟨hCl, hCh⟩ := C_bnd; obtain ⟨hSl, hSh⟩ := S_bnd; obtain ⟨hPl, hPh⟩ := P_bnd
  have e : (2 * 𝒮) ^ 1 * ((1 : ℝ) * circumradius + (1 : ℝ) * 𝒞 * circumradius) = ((1 : ℝ) + (1 : ℝ) * 𝒞) := by
    linear_combination (((1 : ℝ) + (1 : ℝ) * 𝒞)) * hRS + ((0:ℝ)) * hSC + ((0:ℝ)) * hC2
  have hp : (0:ℝ) < (2 * 𝒮) ^ 1 := by positivity
  have h2 : (0:ℝ) < ((1 : ℝ) + (1 : ℝ) * 𝒞) := by linarith
  rw [← e] at h2
  exact (pos_of_mul_pos_right h2 hp.le).le

lemma cf42 : (0:ℝ) < (((7270293 : ℝ) / 2500000) + (-1 : ℝ) * 𝒞) := by
  have hRS := hRS'; have hSC := hSC'; have hC2 := hC2'; have hS := S_pos
  obtain ⟨hCl, hCh⟩ := C_bnd; obtain ⟨hSl, hSh⟩ := S_bnd; obtain ⟨hPl, hPh⟩ := P_bnd
  have e : (2 * 𝒮) ^ 0 * (((7270293 : ℝ) / 2500000) + (-1 : ℝ) * 𝒞) = (((7270293 : ℝ) / 2500000) + (-1 : ℝ) * 𝒞) := by
    linear_combination ((0:ℝ)) * hRS + ((0:ℝ)) * hSC + ((0:ℝ)) * hC2
  have hp : (0:ℝ) < (2 * 𝒮) ^ 0 := by positivity
  have h2 : (0:ℝ) < (((7270293 : ℝ) / 2500000) + (-1 : ℝ) * 𝒞) := by linarith
  rw [← e] at h2
  exact pos_of_mul_pos_right h2 hp.le

lemma cf43 : (0:ℝ) ≤ ((1 : ℝ) * 𝒞) := by
  have hRS := hRS'; have hSC := hSC'; have hC2 := hC2'; have hS := S_pos
  obtain ⟨hCl, hCh⟩ := C_bnd; obtain ⟨hSl, hSh⟩ := S_bnd; obtain ⟨hPl, hPh⟩ := P_bnd
  have e : (2 * 𝒮) ^ 0 * ((1 : ℝ) * 𝒞) = ((1 : ℝ) * 𝒞) := by
    linear_combination ((0:ℝ)) * hRS + ((0:ℝ)) * hSC + ((0:ℝ)) * hC2
  have hp : (0:ℝ) < (2 * 𝒮) ^ 0 := by positivity
  have h2 : (0:ℝ) < ((1 : ℝ) * 𝒞) := by linarith
  rw [← e] at h2
  exact (pos_of_mul_pos_right h2 hp.le).le

lemma cf44 : (0:ℝ) < (((7270293 : ℝ) / 2500000) + (1 : ℝ) * circumradius + (-1 : ℝ) * 𝒞 * circumradius + (-2 : ℝ) * circumradius * 𝒞 ^ 2) := by
  have hRS := hRS'; have hSC := hSC'; have hC2 := hC2'; have hS := S_pos
  obtain ⟨hCl, hCh⟩ := C_bnd; obtain ⟨hSl, hSh⟩ := S_bnd; obtain ⟨hPl, hPh⟩ := P_bnd
  have e : (2 * 𝒮) ^ 1 * (((7270293 : ℝ) / 2500000) + (1 : ℝ) * circumradius + (-1 : ℝ) * 𝒞 * circumradius + (-2 : ℝ) * circumradius * 𝒞 ^ 2) = (((1 : ℝ) / 2) + (-2 : ℝ) * 𝒞 + ((7270293 : ℝ) / 1250000) * 𝒮) := by
    linear_combination (((1 : ℝ) + (-1 : ℝ) * 𝒞 + (-2 : ℝ) * 𝒞 ^ 2)) * hRS + ((0:ℝ)) * hSC + ((((-1 : ℝ) / 2))) * hC2
  have hp : (0:ℝ) < (2 * 𝒮) ^ 1 := by positivity
  have h2 : (0:ℝ) < (((1 : ℝ) / 2) + (-2 : ℝ) * 𝒞 + ((7270293 : ℝ) / 1250000) * 𝒮) := by linarith
  rw [← e] at h2
  exact pos_of_mul_pos_right h2 hp.le

lemma cf45 : (0:ℝ) ≤ ((-1 : ℝ) * circumradius + (1 : ℝ) * 𝒞 * circumradius + (2 : ℝ) * circumradius * 𝒞 ^ 2) := by
  have hRS := hRS'; have hSC := hSC'; have hC2 := hC2'; have hS := S_pos
  obtain ⟨hCl, hCh⟩ := C_bnd; obtain ⟨hSl, hSh⟩ := S_bnd; obtain ⟨hPl, hPh⟩ := P_bnd
  have e : (2 * 𝒮) ^ 1 * ((-1 : ℝ) * circumradius + (1 : ℝ) * 𝒞 * circumradius + (2 : ℝ) * circumradius * 𝒞 ^ 2) = (((-1 : ℝ) / 2) + (2 : ℝ) * 𝒞) := by
    linear_combination (((-1 : ℝ) + (1 : ℝ) * 𝒞 + (2 : ℝ) * 𝒞 ^ 2)) * hRS + ((0:ℝ)) * hSC + ((((1 : ℝ) / 2))) * hC2
  have hp : (0:ℝ) < (2 * 𝒮) ^ 1 := by positivity
  have h2 : (0:ℝ) < (((-1 : ℝ) / 2) + (2 : ℝ) * 𝒞) := by linarith
  rw [← e] at h2
  exact (pos_of_mul_pos_right h2 hp.le).le

lemma cf46 : (0:ℝ) < (((7270293 : ℝ) / 2500000) + (-1 : ℝ) * 𝒞 + (-2 : ℝ) * 𝒞 * circumradius * 𝒮) := by
  have hRS := hRS'; have hSC := hSC'; have hC2 := hC2'; have hS := S_pos
  obtain ⟨hCl, hCh⟩ := C_bnd; obtain ⟨hSl, hSh⟩ := S_bnd; obtain ⟨hPl, hPh⟩ := P_bnd
  have e : (2 * 𝒮) ^ 1 * (((7270293 : ℝ) / 2500000) + (-1 : ℝ) * 𝒞 + (-2 : ℝ) * 𝒞 * circumradius * 𝒮) = (((7270293 : ℝ) / 1250000) * 𝒮 + (-4 : ℝ) * 𝒞 * 𝒮) := by
    linear_combination (((-2 : ℝ) * 𝒞 * 𝒮)) * hRS + ((0:ℝ)) * hSC + ((0:ℝ)) * hC2
  have hp : (0:ℝ) < (2 * 𝒮) ^ 1 := by positivity
  have h2 : (0:ℝ) < (((7270293 : ℝ) / 1250000) * 𝒮 + (-4 : ℝ) * 𝒞 * 𝒮) := by linarith
  rw [← e] at h2
  exact pos_of_mul_pos_right h2 hp.le

lemma cf47 : (0:ℝ) ≤ ((1 : ℝ) * 𝒞 + (2 : ℝ) * 𝒞 * circumradius * 𝒮) := by
  have hRS := hRS'; have hSC := hSC'; have hC2 := hC2'; have hS := S_pos
  obtain ⟨hCl, hCh⟩ := C_bnd; obtain ⟨hSl, hSh⟩ := S_bnd; obtain ⟨hPl, hPh⟩ := P_bnd
  have e : (2 * 𝒮) ^ 1 * ((1 : ℝ) * 𝒞 + (2 : ℝ) * 𝒞 * circumradius * 𝒮) = ((4 : ℝ) * 𝒞 * 𝒮) := by
    linear_combination (((2 : ℝ) * 𝒞 * 𝒮)) * hRS + ((0:ℝ)) * hSC + ((0:ℝ)) * hC2
  have hp : (0:ℝ) < (2 * 𝒮) ^ 1 := by positivity
  have h2 : (0:ℝ) < ((4 : ℝ) * 𝒞 * 𝒮) := by linarith
  rw [← e] at h2
  exact (pos_of_mul_pos_right h2 hp.le).le

lemma cf48 : (0:ℝ) < (((7270293 : ℝ) / 2500000)) := by
  have hRS := hRS'; have hSC := hSC'; have hC2 := hC2'; have hS := S_pos
  obtain ⟨hCl, hCh⟩ := C_bnd; obtain ⟨hSl, hSh⟩ := S_bnd; obtain ⟨hPl, hPh⟩ := P_bnd
  have e : (2 * 𝒮) ^ 0 * (((7270293 : ℝ) / 2500000)) = (((7270293 : ℝ) / 2500000)) := by
    linear_combination ((0:ℝ)) * hRS + ((0:ℝ)) * hSC + ((0:ℝ)) * hC2
  have hp : (0:ℝ) < (2 * 𝒮) ^ 0 := by positivity
  have h2 : (0:ℝ) < (((7270293 : ℝ) / 2500000)) := by linarith
  rw [← e] at h2
  exact pos_of_mul_pos_right h2 hp.le

lemma cf49 : (0:ℝ) ≤ (0:ℝ) := by
  have hRS := hRS'; have hSC := hSC'; have hC2 := hC2'; have hS := S_pos
  obtain ⟨hCl, hCh⟩ := C_bnd; obtain ⟨hSl, hSh⟩ := S_bnd; obtain ⟨hPl, hPh⟩ := P_bnd
  have e : (2 * 𝒮) ^ 0 * (0:ℝ) = (0:ℝ) := by
    linear_combination ((0:ℝ)) * hRS + ((0:ℝ)) * hSC + ((0:ℝ)) * hC2
  have hp : (0:ℝ) < (2 * 𝒮) ^ 0 := by positivity
  have : (2 * 𝒮) ^ 0 * (0:ℝ) = 0 := by rw [e]
  exact le_of_eq ((mul_eq_zero.mp this).resolve_left hp.ne').symm

lemma cf50 : (0:ℝ) < (((7270293 : ℝ) / 2500000) + (-1 : ℝ) * 𝒞 + (-1 : ℝ) * circumradius * 𝒮) := by
  have hRS := hRS'; have hSC := hSC'; have hC2 := hC2'; have hS := S_pos
  obtain ⟨hCl, hCh⟩ := C_bnd; obtain ⟨hSl, hSh⟩ := S_bnd; obtain ⟨hPl, hPh⟩ := P_bnd
  have e : (2 * 𝒮) ^ 1 * (((7270293 : ℝ) / 2500000) + (-1 : ℝ) * 𝒞 + (-1 : ℝ) * circumradius * 𝒮) = (((6020293 : ℝ) / 1250000) * 𝒮 + (-2 : ℝ) * 𝒞 * 𝒮) := by
    linear_combination (((-1 : ℝ) * 𝒮)) * hRS + ((0:ℝ)) * hSC + ((0:ℝ)) * hC2
  have hp : (0:ℝ) < (2 * 𝒮) ^ 1 := by positivity
  have h2 : (0:ℝ) < (((6020293 : ℝ) / 1250000) * 𝒮 + (-2 : ℝ) * 𝒞 * 𝒮) := by linarith
  rw [← e] at h2
  exact pos_of_mul_pos_right h2 hp.le

lemma cf51 : (0:ℝ) ≤ ((1 : ℝ) * 𝒞 + (1 : ℝ) * circumradius * 𝒮) := by
  have hRS := hRS'; have hSC := hSC'; have hC2 := hC2'; have hS := S_pos
  obtain ⟨hCl, hCh⟩ := C_bnd; obtain ⟨hSl, hSh⟩ := S_bnd; obtain ⟨hPl, hPh⟩ := P_bnd
  have e : (2 * 𝒮) ^ 1 * ((1 : ℝ) * 𝒞 + (1 : ℝ) * circumradius * 𝒮) = ((1 : ℝ) * 𝒮 + (2 : ℝ) * 𝒞 * 𝒮) := by
    linear_combination (((1 : ℝ) * 𝒮)) * hRS + ((0:ℝ)) * hSC + ((0:ℝ)) * hC2
  have hp : (0:ℝ) < (2 * 𝒮) ^ 1 := by positivity
  have h2 : (0:ℝ) < ((1 : ℝ) * 𝒮 + (2 : ℝ) * 𝒞 * 𝒮) := by linarith
  rw [← e] at h2
  exact (pos_of_mul_pos_right h2 hp.le).le

lemma cf52 : (0:ℝ) ≤ ((1 : ℝ) * circumradius + (1 : ℝ) * 𝒞 * circumradius) := by
  have hRS := hRS'; have hSC := hSC'; have hC2 := hC2'; have hS := S_pos
  obtain ⟨hCl, hCh⟩ := C_bnd; obtain ⟨hSl, hSh⟩ := S_bnd; obtain ⟨hPl, hPh⟩ := P_bnd
  have e : (2 * 𝒮) ^ 1 * ((1 : ℝ) * circumradius + (1 : ℝ) * 𝒞 * circumradius) = ((1 : ℝ) + (1 : ℝ) * 𝒞) := by
    linear_combination (((1 : ℝ) + (1 : ℝ) * 𝒞)) * hRS + ((0:ℝ)) * hSC + ((0:ℝ)) * hC2
  have hp : (0:ℝ) < (2 * 𝒮) ^ 1 := by positivity
  have h2 : (0:ℝ) < ((1 : ℝ) + (1 : ℝ) * 𝒞) := by linarith
  rw [← e] at h2
  exact (pos_of_mul_pos_right h2 hp.le).le

lemma cf53 : (0:ℝ) < (((7270293 : ℝ) / 2500000) + (-1 : ℝ) * circumradius + (-1 : ℝ) * 𝒞 * circumradius) := by
  have hRS := hRS'; have hSC := hSC'; have hC2 := hC2'; have hS := S_pos
  obtain ⟨hCl, hCh⟩ := C_bnd; obtain ⟨hSl, hSh⟩ := S_bnd; obtain ⟨hPl, hPh⟩ := P_bnd
  have e : (2 * 𝒮) ^ 1 * (((7270293 : ℝ) / 2500000) + (-1 : ℝ) * circumradius + (-1 : ℝ) * 𝒞 * circumradius) = ((-1 : ℝ) + (-1 : ℝ) * 𝒞 + ((7270293 : ℝ) / 1250000) * 𝒮) := by
    linear_combination (((-1 : ℝ) + (-1 : ℝ) * 𝒞)) * hRS + ((0:ℝ)) * hSC + ((0:ℝ)) * hC2
  have hp : (0:ℝ) < (2 * 𝒮) ^ 1 := by positivity
  have h2 : (0:ℝ) < ((-1 : ℝ) + (-1 : ℝ) * 𝒞 + ((7270293 : ℝ) / 1250000) * 𝒮) := by linarith
  rw [← e] at h2
  exact pos_of_mul_pos_right h2 hp.le

lemma cf54 : (0:ℝ) < (((1865711 : ℝ) / 1000000)) := by
  have hRS := hRS'; have hSC := hSC'; have hC2 := hC2'; have hS := S_pos
  obtain ⟨hCl, hCh⟩ := C_bnd; obtain ⟨hSl, hSh⟩ := S_bnd; obtain ⟨hPl, hPh⟩ := P_bnd
  have e : (2 * 𝒮) ^ 0 * (((1865711 : ℝ) / 1000000)) = (((1865711 : ℝ) / 1000000)) := by
    linear_combination ((0:ℝ)) * hRS + ((0:ℝ)) * hSC + ((0:ℝ)) * hC2
  have hp : (0:ℝ) < (2 * 𝒮) ^ 0 := by positivity
  have h2 : (0:ℝ) < (((1865711 : ℝ) / 1000000)) := by linarith
  rw [← e] at h2
  exact pos_of_mul_pos_right h2 hp.le

lemma cf55 : (0:ℝ) < (((325751 : ℝ) / 312500)) := by
  have hRS := hRS'; have hSC := hSC'; have hC2 := hC2'; have hS := S_pos
  obtain ⟨hCl, hCh⟩ := C_bnd; obtain ⟨hSl, hSh⟩ := S_bnd; obtain ⟨hPl, hPh⟩ := P_bnd
  have e : (2 * 𝒮) ^ 0 * (((325751 : ℝ) / 312500)) = (((325751 : ℝ) / 312500)) := by
    linear_combination ((0:ℝ)) * hRS + ((0:ℝ)) * hSC + ((0:ℝ)) * hC2
  have hp : (0:ℝ) < (2 * 𝒮) ^ 0 := by positivity
  have h2 : (0:ℝ) < (((325751 : ℝ) / 312500)) := by linarith
  rw [← e] at h2
  exact pos_of_mul_pos_right h2 hp.le

lemma cf56 : (0:ℝ) ≤ ((-1 : ℝ) * circumradius + (1 : ℝ) * 𝒞 * circumradius + (2 : ℝ) * circumradius * 𝒞 ^ 2) := by
  have hRS := hRS'; have hSC := hSC'; have hC2 := hC2'; have hS := S_pos
  obtain ⟨hCl, hCh⟩ := C_bnd; obtain ⟨hSl, hSh⟩ := S_bnd; obtain ⟨hPl, hPh⟩ := P_bnd
  have e : (2 * 𝒮) ^ 1 * ((-1 : ℝ) * circumradius + (1 : ℝ) * 𝒞 * circumradius + (2 : ℝ) * circumradius * 𝒞 ^ 2) = (((-1 : ℝ) / 2) + (2 : ℝ) * 𝒞) := by
    linear_combination (((-1 : ℝ) + (1 : ℝ) * 𝒞 + (2 : ℝ) * 𝒞 ^ 2)) * hRS + ((0:ℝ)) * hSC + ((((1 : ℝ) / 2))) * hC2
  have hp : (0:ℝ) < (2 * 𝒮) ^ 1 := by positivity
  have h2 : (0:ℝ) < (((-1 : ℝ) / 2) + (2 : ℝ) * 𝒞) := by linarith
  rw [← e] at h2
  exact (pos_of_mul_pos_right h2 hp.le).le

lemma cf57 : (0:ℝ) < (((7270293 : ℝ) / 2500000) + (1 : ℝ) * circumradius + (-1 : ℝ) * 𝒞 * circumradius + (-2 : ℝ) * circumradius * 𝒞 ^ 2) := by
  have hRS := hRS'; have hSC := hSC'; have hC2 := hC2'; have hS := S_pos
  obtain ⟨hCl, hCh⟩ := C_bnd; obtain ⟨hSl, hSh⟩ := S_bnd; obtain ⟨hPl, hPh⟩ := P_bnd
  have e : (2 * 𝒮) ^ 1 * (((7270293 : ℝ) / 2500000) + (1 : ℝ) * circumradius + (-1 : ℝ) * 𝒞 * circumradius + (-2 : ℝ) * circumradius * 𝒞 ^ 2) = (((1 : ℝ) / 2) + (-2 : ℝ) * 𝒞 + ((7270293 : ℝ) / 1250000) * 𝒮) := by
    linear_combination (((1 : ℝ) + (-1 : ℝ) * 𝒞 + (-2 : ℝ) * 𝒞 ^ 2)) * hRS + ((0:ℝ)) * hSC + ((((-1 : ℝ) / 2))) * hC2
  have hp : (0:ℝ) < (2 * 𝒮) ^ 1 := by positivity
  have h2 : (0:ℝ) < (((1 : ℝ) / 2) + (-2 : ℝ) * 𝒞 + ((7270293 : ℝ) / 1250000) * 𝒮) := by linarith
  rw [← e] at h2
  exact pos_of_mul_pos_right h2 hp.le

lemma cf58 : (0:ℝ) < (((1865711 : ℝ) / 1000000) + (2 : ℝ) * 𝒞 * circumradius * 𝒮) := by
  have hRS := hRS'; have hSC := hSC'; have hC2 := hC2'; have hS := S_pos
  obtain ⟨hCl, hCh⟩ := C_bnd; obtain ⟨hSl, hSh⟩ := S_bnd; obtain ⟨hPl, hPh⟩ := P_bnd
  have e : (2 * 𝒮) ^ 1 * (((1865711 : ℝ) / 1000000) + (2 : ℝ) * 𝒞 * circumradius * 𝒮) = (((1865711 : ℝ) / 500000) * 𝒮 + (2 : ℝ) * 𝒞 * 𝒮) := by
    linear_combination (((2 : ℝ) * 𝒞 * 𝒮)) * hRS + ((0:ℝ)) * hSC + ((0:ℝ)) * hC2
  have hp : (0:ℝ) < (2 * 𝒮) ^ 1 := by positivity
  have h2 : (0:ℝ) < (((1865711 : ℝ) / 500000) * 𝒮 + (2 : ℝ) * 𝒞 * 𝒮) := by linarith
  rw [← e] at h2
  exact pos_of_mul_pos_right h2 hp.le

lemma cf59 : (0:ℝ) < (((325751 : ℝ) / 312500) + (-2 : ℝ) * 𝒞 * circumradius * 𝒮) := by
  have hRS := hRS'; have hSC := hSC'; have hC2 := hC2'; have hS := S_pos
  obtain ⟨hCl, hCh⟩ := C_bnd; obtain ⟨hSl, hSh⟩ := S_bnd; obtain ⟨hPl, hPh⟩ := P_bnd
  have e : (2 * 𝒮) ^ 1 * (((325751 : ℝ) / 312500) + (-2 : ℝ) * 𝒞 * circumradius * 𝒮) = (((325751 : ℝ) / 156250) * 𝒮 + (-2 : ℝ) * 𝒞 * 𝒮) := by
    linear_combination (((-2 : ℝ) * 𝒞 * 𝒮)) * hRS + ((0:ℝ)) * hSC + ((0:ℝ)) * hC2
  have hp : (0:ℝ) < (2 * 𝒮) ^ 1 := by positivity
  have h2 : (0:ℝ) < (((325751 : ℝ) / 156250) * 𝒮 + (-2 : ℝ) * 𝒞 * 𝒮) := by linarith
  rw [← e] at h2
  exact pos_of_mul_pos_right h2 hp.le

lemma cf60 : (0:ℝ) ≤ (0:ℝ) := by
  have hRS := hRS'; have hSC := hSC'; have hC2 := hC2'; have hS := S_pos
  obtain ⟨hCl, hCh⟩ := C_bnd; obtain ⟨hSl, hSh⟩ := S_bnd; obtain ⟨hPl, hPh⟩ := P_bnd
  have e : (2 * 𝒮) ^ 0 * (0:ℝ) = (0:ℝ) := by
    linear_combination ((0:ℝ)) * hRS + ((0:ℝ)) * hSC + ((0:ℝ)) * hC2
  have hp : (0:ℝ) < (2 * 𝒮) ^ 0 := by positivity
  have : (2 * 𝒮) ^ 0 * (0:ℝ) = 0 := by rw [e]
  exact le_of_eq ((mul_eq_zero.mp this).resolve_left hp.ne').symm

lemma cf61 : (0:ℝ) < (((7270293 : ℝ) / 2500000)) := by
  have hRS := hRS'; have hSC := hSC'; have hC2 := hC2'; have hS := S_pos
  obtain ⟨hCl, hCh⟩ := C_bnd; obtain ⟨hSl, hSh⟩ := S_bnd; obtain ⟨hPl, hPh⟩ := P_bnd
  have e : (2 * 𝒮) ^ 0 * (((7270293 : ℝ) / 2500000)) = (((7270293 : ℝ) / 2500000)) := by
    linear_combination ((0:ℝ)) * hRS + ((0:ℝ)) * hSC + ((0:ℝ)) * hC2
  have hp : (0:ℝ) < (2 * 𝒮) ^ 0 := by positivity
  have h2 : (0:ℝ) < (((7270293 : ℝ) / 2500000)) := by linarith
  rw [← e] at h2
  exact pos_of_mul_pos_right h2 hp.le

lemma cf62 : (0:ℝ) < (((1865711 : ℝ) / 1000000) + (1 : ℝ) * circumradius * 𝒮) := by
  have hRS := hRS'; have hSC := hSC'; have hC2 := hC2'; have hS := S_pos
  obtain ⟨hCl, hCh⟩ := C_bnd; obtain ⟨hSl, hSh⟩ := S_bnd; obtain ⟨hPl, hPh⟩ := P_bnd
  have e : (2 * 𝒮) ^ 1 * (((1865711 : ℝ) / 1000000) + (1 : ℝ) * circumradius * 𝒮) = (((2365711 : ℝ) / 500000) * 𝒮) := by
    linear_combination (((1 : ℝ) * 𝒮)) * hRS + ((0:ℝ)) * hSC + ((0:ℝ)) * hC2
  have hp : (0:ℝ) < (2 * 𝒮) ^ 1 := by positivity
  have h2 : (0:ℝ) < (((2365711 : ℝ) / 500000) * 𝒮) := by linarith
  rw [← e] at h2
  exact pos_of_mul_pos_right h2 hp.le

lemma cf63 : (0:ℝ) < (((325751 : ℝ) / 312500) + (-1 : ℝ) * circumradius * 𝒮) := by
  have hRS := hRS'; have hSC := hSC'; have hC2 := hC2'; have hS := S_pos
  obtain ⟨hCl, hCh⟩ := C_bnd; obtain ⟨hSl, hSh⟩ := S_bnd; obtain ⟨hPl, hPh⟩ := P_bnd
  have e : (2 * 𝒮) ^ 1 * (((325751 : ℝ) / 312500) + (-1 : ℝ) * circumradius * 𝒮) = (((169501 : ℝ) / 156250) * 𝒮) := by
    linear_combination (((-1 : ℝ) * 𝒮)) * hRS + ((0:ℝ)) * hSC + ((0:ℝ)) * hC2
  have hp : (0:ℝ) < (2 * 𝒮) ^ 1 := by positivity
  have h2 : (0:ℝ) < (((169501 : ℝ) / 156250) * 𝒮) := by linarith
  rw [← e] at h2
  exact pos_of_mul_pos_right h2 hp.le

lemma cf64 : (0:ℝ) ≤ (0:ℝ) := by
  have hRS := hRS'; have hSC := hSC'; have hC2 := hC2'; have hS := S_pos
  obtain ⟨hCl, hCh⟩ := C_bnd; obtain ⟨hSl, hSh⟩ := S_bnd; obtain ⟨hPl, hPh⟩ := P_bnd
  have e : (2 * 𝒮) ^ 0 * (0:ℝ) = (0:ℝ) := by
    linear_combination ((0:ℝ)) * hRS + ((0:ℝ)) * hSC + ((0:ℝ)) * hC2
  have hp : (0:ℝ) < (2 * 𝒮) ^ 0 := by positivity
  have : (2 * 𝒮) ^ 0 * (0:ℝ) = 0 := by rw [e]
  exact le_of_eq ((mul_eq_zero.mp this).resolve_left hp.ne').symm

lemma cf65 : (0:ℝ) < (((7270293 : ℝ) / 2500000)) := by
  have hRS := hRS'; have hSC := hSC'; have hC2 := hC2'; have hS := S_pos
  obtain ⟨hCl, hCh⟩ := C_bnd; obtain ⟨hSl, hSh⟩ := S_bnd; obtain ⟨hPl, hPh⟩ := P_bnd
  have e : (2 * 𝒮) ^ 0 * (((7270293 : ℝ) / 2500000)) = (((7270293 : ℝ) / 2500000)) := by
    linear_combination ((0:ℝ)) * hRS + ((0:ℝ)) * hSC + ((0:ℝ)) * hC2
  have hp : (0:ℝ) < (2 * 𝒮) ^ 0 := by positivity
  have h2 : (0:ℝ) < (((7270293 : ℝ) / 2500000)) := by linarith
  rw [← e] at h2
  exact pos_of_mul_pos_right h2 hp.le

lemma cf66 : (0:ℝ) < (((1865711 : ℝ) / 1000000) + (-1 : ℝ) * circumradius * 𝒮) := by
  have hRS := hRS'; have hSC := hSC'; have hC2 := hC2'; have hS := S_pos
  obtain ⟨hCl, hCh⟩ := C_bnd; obtain ⟨hSl, hSh⟩ := S_bnd; obtain ⟨hPl, hPh⟩ := P_bnd
  have e : (2 * 𝒮) ^ 1 * (((1865711 : ℝ) / 1000000) + (-1 : ℝ) * circumradius * 𝒮) = (((1365711 : ℝ) / 500000) * 𝒮) := by
    linear_combination (((-1 : ℝ) * 𝒮)) * hRS + ((0:ℝ)) * hSC + ((0:ℝ)) * hC2
  have hp : (0:ℝ) < (2 * 𝒮) ^ 1 := by positivity
  have h2 : (0:ℝ) < (((1365711 : ℝ) / 500000) * 𝒮) := by linarith
  rw [← e] at h2
  exact pos_of_mul_pos_right h2 hp.le

lemma cf67 : (0:ℝ) < (((325751 : ℝ) / 312500) + (1 : ℝ) * circumradius * 𝒮) := by
  have hRS := hRS'; have hSC := hSC'; have hC2 := hC2'; have hS := S_pos
  obtain ⟨hCl, hCh⟩ := C_bnd; obtain ⟨hSl, hSh⟩ := S_bnd; obtain ⟨hPl, hPh⟩ := P_bnd
  have e : (2 * 𝒮) ^ 1 * (((325751 : ℝ) / 312500) + (1 : ℝ) * circumradius * 𝒮) = (((482001 : ℝ) / 156250) * 𝒮) := by
    linear_combination (((1 : ℝ) * 𝒮)) * hRS + ((0:ℝ)) * hSC + ((0:ℝ)) * hC2
  have hp : (0:ℝ) < (2 * 𝒮) ^ 1 := by positivity
  have h2 : (0:ℝ) < (((482001 : ℝ) / 156250) * 𝒮) := by linarith
  rw [← e] at h2
  exact pos_of_mul_pos_right h2 hp.le

lemma cf68 : (0:ℝ) ≤ ((-1 : ℝ) * circumradius + (1 : ℝ) * 𝒞 * circumradius + (2 : ℝ) * circumradius * 𝒞 ^ 2) := by
  have hRS := hRS'; have hSC := hSC'; have hC2 := hC2'; have hS := S_pos
  obtain ⟨hCl, hCh⟩ := C_bnd; obtain ⟨hSl, hSh⟩ := S_bnd; obtain ⟨hPl, hPh⟩ := P_bnd
  have e : (2 * 𝒮) ^ 1 * ((-1 : ℝ) * circumradius + (1 : ℝ) * 𝒞 * circumradius + (2 : ℝ) * circumradius * 𝒞 ^ 2) = (((-1 : ℝ) / 2) + (2 : ℝ) * 𝒞) := by
    linear_combination (((-1 : ℝ) + (1 : ℝ) * 𝒞 + (2 : ℝ) * 𝒞 ^ 2)) * hRS + ((0:ℝ)) * hSC + ((((1 : ℝ) / 2))) * hC2
  have hp : (0:ℝ) < (2 * 𝒮) ^ 1 := by positivity
  have h2 : (0:ℝ) < (((-1 : ℝ) / 2) + (2 : ℝ) * 𝒞) := by linarith
  rw [← e] at h2
  exact (pos_of_mul_pos_right h2 hp.le).le

lemma cf69 : (0:ℝ) < (((7270293 : ℝ) / 2500000) + (1 : ℝ) * circumradius + (-1 : ℝ) * 𝒞 * circumradius + (-2 : ℝ) * circumradius * 𝒞 ^ 2) := by
  have hRS := hRS'; have hSC := hSC'; have hC2 := hC2'; have hS := S_pos
  obtain ⟨hCl, hCh⟩ := C_bnd; obtain ⟨hSl, hSh⟩ := S_bnd; obtain ⟨hPl, hPh⟩ := P_bnd
  have e : (2 * 𝒮) ^ 1 * (((7270293 : ℝ) / 2500000) + (1 : ℝ) * circumradius + (-1 : ℝ) * 𝒞 * circumradius + (-2 : ℝ) * circumradius * 𝒞 ^ 2) = (((1 : ℝ) / 2) + (-2 : ℝ) * 𝒞 + ((7270293 : ℝ) / 1250000) * 𝒮) := by
    linear_combination (((1 : ℝ) + (-1 : ℝ) * 𝒞 + (-2 : ℝ) * 𝒞 ^ 2)) * hRS + ((0:ℝ)) * hSC + ((((-1 : ℝ) / 2))) * hC2
  have hp : (0:ℝ) < (2 * 𝒮) ^ 1 := by positivity
  have h2 : (0:ℝ) < (((1 : ℝ) / 2) + (-2 : ℝ) * 𝒞 + ((7270293 : ℝ) / 1250000) * 𝒮) := by linarith
  rw [← e] at h2
  exact pos_of_mul_pos_right h2 hp.le

lemma cf70 : (0:ℝ) < (((1865711 : ℝ) / 1000000) + (-2 : ℝ) * 𝒞 * circumradius * 𝒮) := by
  have hRS := hRS'; have hSC := hSC'; have hC2 := hC2'; have hS := S_pos
  obtain ⟨hCl, hCh⟩ := C_bnd; obtain ⟨hSl, hSh⟩ := S_bnd; obtain ⟨hPl, hPh⟩ := P_bnd
  have e : (2 * 𝒮) ^ 1 * (((1865711 : ℝ) / 1000000) + (-2 : ℝ) * 𝒞 * circumradius * 𝒮) = (((1865711 : ℝ) / 500000) * 𝒮 + (-2 : ℝ) * 𝒞 * 𝒮) := by
    linear_combination (((-2 : ℝ) * 𝒞 * 𝒮)) * hRS + ((0:ℝ)) * hSC + ((0:ℝ)) * hC2
  have hp : (0:ℝ) < (2 * 𝒮) ^ 1 := by positivity
  have h2 : (0:ℝ) < (((1865711 : ℝ) / 500000) * 𝒮 + (-2 : ℝ) * 𝒞 * 𝒮) := by linarith
  rw [← e] at h2
  exact pos_of_mul_pos_right h2 hp.le

lemma cf71 : (0:ℝ) < (((325751 : ℝ) / 312500) + (2 : ℝ) * 𝒞 * circumradius * 𝒮) := by
  have hRS := hRS'; have hSC := hSC'; have hC2 := hC2'; have hS := S_pos
  obtain ⟨hCl, hCh⟩ := C_bnd; obtain ⟨hSl, hSh⟩ := S_bnd; obtain ⟨hPl, hPh⟩ := P_bnd
  have e : (2 * 𝒮) ^ 1 * (((325751 : ℝ) / 312500) + (2 : ℝ) * 𝒞 * circumradius * 𝒮) = (((325751 : ℝ) / 156250) * 𝒮 + (2 : ℝ) * 𝒞 * 𝒮) := by
    linear_combination (((2 : ℝ) * 𝒞 * 𝒮)) * hRS + ((0:ℝ)) * hSC + ((0:ℝ)) * hC2
  have hp : (0:ℝ) < (2 * 𝒮) ^ 1 := by positivity
  have h2 : (0:ℝ) < (((325751 : ℝ) / 156250) * 𝒮 + (2 : ℝ) * 𝒞 * 𝒮) := by linarith
  rw [← e] at h2
  exact pos_of_mul_pos_right h2 hp.le

lemma cf72 : (0:ℝ) ≤ ((-2 : ℝ) * circumradius * 𝒞 ^ 3 + (2 : ℝ) * 𝒞 * circumradius + (-2 : ℝ) * 𝒞 * circumradius * 𝒮 ^ 2) := by
  have hRS := hRS'; have hSC := hSC'; have hC2 := hC2'; have hS := S_pos
  obtain ⟨hCl, hCh⟩ := C_bnd; obtain ⟨hSl, hSh⟩ := S_bnd; obtain ⟨hPl, hPh⟩ := P_bnd
  have e : (2 * 𝒮) ^ 1 * ((-2 : ℝ) * circumradius * 𝒞 ^ 3 + (2 : ℝ) * 𝒞 * circumradius + (-2 : ℝ) * 𝒞 * circumradius * 𝒮 ^ 2) = (0:ℝ) := by
    linear_combination (((-2 : ℝ) * 𝒞 ^ 3 + (2 : ℝ) * 𝒞 + (-2 : ℝ) * 𝒞 * 𝒮 ^ 2)) * hRS + (((-2 : ℝ) * 𝒞)) * hSC + ((0:ℝ)) * hC2
  have hp : (0:ℝ) < (2 * 𝒮) ^ 1 := by positivity
  have : (2 * 𝒮) ^ 1 * ((-2 : ℝ) * circumradius * 𝒞 ^ 3 + (2 : ℝ) * 𝒞 * circumradius + (-2 : ℝ) * 𝒞 * circumradius * 𝒮 ^ 2) = 0 := by rw [e]
  exact le_of_eq ((mul_eq_zero.mp this).resolve_left hp.ne').symm

lemma cf73 : (0:ℝ) ≤ (0:ℝ) := by
  have hRS := hRS'; have hSC := hSC'; have hC2 := hC2'; have hS := S_pos
  obtain ⟨hCl, hCh⟩ := C_bnd; obtain ⟨hSl, hSh⟩ := S_bnd; obtain ⟨hPl, hPh⟩ := P_bnd
  have e : (2 * 𝒮) ^ 0 * (0:ℝ) = (0:ℝ) := by
    linear_combination ((0:ℝ)) * hRS + ((0:ℝ)) * hSC + ((0:ℝ)) * hC2
  have hp : (0:ℝ) < (2 * 𝒮) ^ 0 := by positivity
  have : (2 * 𝒮) ^ 0 * (0:ℝ) = 0 := by rw [e]
  exact le_of_eq ((mul_eq_zero.mp this).resolve_left hp.ne').symm

lemma cf74 : (0:ℝ) ≤ ((-2 : ℝ) * circumradius * 𝒞 ^ 3 + (2 : ℝ) * 𝒞 * circumradius + (2 : ℝ) * 𝒞 * circumradius * 𝒮 ^ 2) := by
  have hRS := hRS'; have hSC := hSC'; have hC2 := hC2'; have hS := S_pos
  obtain ⟨hCl, hCh⟩ := C_bnd; obtain ⟨hSl, hSh⟩ := S_bnd; obtain ⟨hPl, hPh⟩ := P_bnd
  have e : (2 * 𝒮) ^ 1 * ((-2 : ℝ) * circumradius * 𝒞 ^ 3 + (2 : ℝ) * 𝒞 * circumradius + (2 : ℝ) * 𝒞 * circumradius * 𝒮 ^ 2) = (((-1 : ℝ) / 2) + (2 : ℝ) * 𝒞) := by
    linear_combination (((-2 : ℝ) * 𝒞 ^ 3 + (2 : ℝ) * 𝒞 + (2 : ℝ) * 𝒞 * 𝒮 ^ 2)) * hRS + (((2 : ℝ) * 𝒞)) * hSC + ((((-1 : ℝ) / 2) + (-1 : ℝ) * 𝒞)) * hC2
  have hp : (0:ℝ) < (2 * 𝒮) ^ 1 := by positivity
  have h2 : (0:ℝ) < (((-1 : ℝ) / 2) + (2 : ℝ) * 𝒞) := by linarith
  rw [← e] at h2
  exact (pos_of_mul_pos_right h2 hp.le).le

lemma cf75 : (0:ℝ) ≤ ((1 : ℝ) * 𝒞 * circumradius + (1 : ℝ) * circumradius * 𝒞 ^ 2 + (1 : ℝ) * circumradius * 𝒮 ^ 2) := by
  have hRS := hRS'; have hSC := hSC'; have hC2 := hC2'; have hS := S_pos
  obtain ⟨hCl, hCh⟩ := C_bnd; obtain ⟨hSl, hSh⟩ := S_bnd; obtain ⟨hPl, hPh⟩ := P_bnd
  have e : (2 * 𝒮) ^ 1 * ((1 : ℝ) * 𝒞 * circumradius + (1 : ℝ) * circumradius * 𝒞 ^ 2 + (1 : ℝ) * circumradius * 𝒮 ^ 2) = ((1 : ℝ) + (1 : ℝ) * 𝒞) := by
    linear_combination (((1 : ℝ) * 𝒞 + (1 : ℝ) * 𝒞 ^ 2 + (1 : ℝ) * 𝒮 ^ 2)) * hRS + (((1 : ℝ))) * hSC + ((0:ℝ)) * hC2
  have hp : (0:ℝ) < (2 * 𝒮) ^ 1 := by positivity
  have h2 : (0:ℝ) < ((1 : ℝ) + (1 : ℝ) * 𝒞) := by linarith
  rw [← e] at h2
  exact (pos_of_mul_pos_right h2 hp.le).le

lemma cf76 : (0:ℝ) ≤ ((1 : ℝ) * 𝒞 * circumradius + (1 : ℝ) * circumradius * 𝒞 ^ 2 + (-1 : ℝ) * circumradius * 𝒮 ^ 2) := by
  have hRS := hRS'; have hSC := hSC'; have hC2 := hC2'; have hS := S_pos
  obtain ⟨hCl, hCh⟩ := C_bnd; obtain ⟨hSl, hSh⟩ := S_bnd; obtain ⟨hPl, hPh⟩ := P_bnd
  have e : (2 * 𝒮) ^ 1 * ((1 : ℝ) * 𝒞 * circumradius + (1 : ℝ) * circumradius * 𝒞 ^ 2 + (-1 : ℝ) * circumradius * 𝒮 ^ 2) = (((-1 : ℝ) / 2) + (2 : ℝ) * 𝒞) := by
    linear_combination (((1 : ℝ) * 𝒞 + (1 : ℝ) * 𝒞 ^ 2 + (-1 : ℝ) * 𝒮 ^ 2)) * hRS + (((-1 : ℝ))) * hSC + ((((1 : ℝ) / 2))) * hC2
  have hp : (0:ℝ) < (2 * 𝒮) ^ 1 := by positivity
  have h2 : (0:ℝ) < (((-1 : ℝ) / 2) + (2 : ℝ) * 𝒞) := by linarith
  rw [← e] at h2
  exact (pos_of_mul_pos_right h2 hp.le).le

lemma cf77 : (0:ℝ) ≤ ((1 : ℝ) * 𝒞 + (2 : ℝ) * 𝒞 * circumradius * 𝒮) := by
  have hRS := hRS'; have hSC := hSC'; have hC2 := hC2'; have hS := S_pos
  obtain ⟨hCl, hCh⟩ := C_bnd; obtain ⟨hSl, hSh⟩ := S_bnd; obtain ⟨hPl, hPh⟩ := P_bnd
  have e : (2 * 𝒮) ^ 1 * ((1 : ℝ) * 𝒞 + (2 : ℝ) * 𝒞 * circumradius * 𝒮) = ((4 : ℝ) * 𝒞 * 𝒮) := by
    linear_combination (((2 : ℝ) * 𝒞 * 𝒮)) * hRS + ((0:ℝ)) * hSC + ((0:ℝ)) * hC2
  have hp : (0:ℝ) < (2 * 𝒮) ^ 1 := by positivity
  have h2 : (0:ℝ) < ((4 : ℝ) * 𝒞 * 𝒮) := by linarith
  rw [← e] at h2
  exact (pos_of_mul_pos_right h2 hp.le).le

lemma cf78 : (0:ℝ) ≤ ((1 : ℝ) * 𝒞 + (1 : ℝ) * circumradius * 𝒮) := by
  have hRS := hRS'; have hSC := hSC'; have hC2 := hC2'; have hS := S_pos
  obtain ⟨hCl, hCh⟩ := C_bnd; obtain ⟨hSl, hSh⟩ := S_bnd; obtain ⟨hPl, hPh⟩ := P_bnd
  have e : (2 * 𝒮) ^ 1 * ((1 : ℝ) * 𝒞 + (1 : ℝ) * circumradius * 𝒮) = ((1 : ℝ) * 𝒮 + (2 : ℝ) * 𝒞 * 𝒮) := by
    linear_combination (((1 : ℝ) * 𝒮)) * hRS + ((0:ℝ)) * hSC + ((0:ℝ)) * hC2
  have hp : (0:ℝ) < (2 * 𝒮) ^ 1 := by positivity
  have h2 : (0:ℝ) < ((1 : ℝ) * 𝒮 + (2 : ℝ) * 𝒞 * 𝒮) := by linarith
  rw [← e] at h2
  exact (pos_of_mul_pos_right h2 hp.le).le

lemma cf79 : (0:ℝ) ≤ ((1 : ℝ) * 𝒞 + (-1 : ℝ) * circumradius * 𝒮) := by
  have hRS := hRS'; have hSC := hSC'; have hC2 := hC2'; have hS := S_pos
  obtain ⟨hCl, hCh⟩ := C_bnd; obtain ⟨hSl, hSh⟩ := S_bnd; obtain ⟨hPl, hPh⟩ := P_bnd
  have e : (2 * 𝒮) ^ 1 * ((1 : ℝ) * 𝒞 + (-1 : ℝ) * circumradius * 𝒮) = ((-1 : ℝ) * 𝒮 + (2 : ℝ) * 𝒞 * 𝒮) := by
    linear_combination (((-1 : ℝ) * 𝒮)) * hRS + ((0:ℝ)) * hSC + ((0:ℝ)) * hC2
  have hp : (0:ℝ) < (2 * 𝒮) ^ 1 := by positivity
  have h2 : (0:ℝ) < ((-1 : ℝ) * 𝒮 + (2 : ℝ) * 𝒞 * 𝒮) := by linarith
  rw [← e] at h2
  exact (pos_of_mul_pos_right h2 hp.le).le

lemma cf80 : (0:ℝ) ≤ ((1 : ℝ) * 𝒞 + (1 : ℝ) * circumradius * 𝒮 + (-4 : ℝ) * circumradius * 𝒮 * 𝒞 ^ 2) := by
  have hRS := hRS'; have hSC := hSC'; have hC2 := hC2'; have hS := S_pos
  obtain ⟨hCl, hCh⟩ := C_bnd; obtain ⟨hSl, hSh⟩ := S_bnd; obtain ⟨hPl, hPh⟩ := P_bnd
  have e : (2 * 𝒮) ^ 1 * ((1 : ℝ) * 𝒞 + (1 : ℝ) * circumradius * 𝒮 + (-4 : ℝ) * circumradius * 𝒮 * 𝒞 ^ 2) = (0:ℝ) := by
    linear_combination (((1 : ℝ) * 𝒮 + (-4 : ℝ) * 𝒮 * 𝒞 ^ 2)) * hRS + ((0:ℝ)) * hSC + (((-1 : ℝ) * 𝒮)) * hC2
  have hp : (0:ℝ) < (2 * 𝒮) ^ 1 := by positivity
  have : (2 * 𝒮) ^ 1 * ((1 : ℝ) * 𝒞 + (1 : ℝ) * circumradius * 𝒮 + (-4 : ℝ) * circumradius * 𝒮 * 𝒞 ^ 2) = 0 := by rw [e]
  exact le_of_eq ((mul_eq_zero.mp this).resolve_left hp.ne').symm

lemma cf81 : (0:ℝ) ≤ ((1 : ℝ) * 𝒞) := by
  have hRS := hRS'; have hSC := hSC'; have hC2 := hC2'; have hS := S_pos
  obtain ⟨hCl, hCh⟩ := C_bnd; obtain ⟨hSl, hSh⟩ := S_bnd; obtain ⟨hPl, hPh⟩ := P_bnd
  have e : (2 * 𝒮) ^ 0 * ((1 : ℝ) * 𝒞) = ((1 : ℝ) * 𝒞) := by
    linear_combination ((0:ℝ)) * hRS + ((0:ℝ)) * hSC + ((0:ℝ)) * hC2
  have hp : (0:ℝ) < (2 * 𝒮) ^ 0 := by positivity
  have h2 : (0:ℝ) < ((1 : ℝ) * 𝒞) := by linarith
  rw [← e] at h2
  exact (pos_of_mul_pos_right h2 hp.le).le

lemma cf82 : (0:ℝ) ≤ ((-2 : ℝ) * circumradius * 𝒞 ^ 3 + (2 : ℝ) * 𝒞 * circumradius + (2 : ℝ) * 𝒞 * circumradius * 𝒮 ^ 2) := by
  have hRS := hRS'; have hSC := hSC'; have hC2 := hC2'; have hS := S_pos
  obtain ⟨hCl, hCh⟩ := C_bnd; obtain ⟨hSl, hSh⟩ := S_bnd; obtain ⟨hPl, hPh⟩ := P_bnd
  have e : (2 * 𝒮) ^ 1 * ((-2 : ℝ) * circumradius * 𝒞 ^ 3 + (2 : ℝ) * 𝒞 * circumradius + (2 : ℝ) * 𝒞 * circumradius * 𝒮 ^ 2) = (((-1 : ℝ) / 2) + (2 : ℝ) * 𝒞) := by
    linear_combination (((-2 : ℝ) * 𝒞 ^ 3 + (2 : ℝ) * 𝒞 + (2 : ℝ) * 𝒞 * 𝒮 ^ 2)) * hRS + (((2 : ℝ) * 𝒞)) * hSC + ((((-1 : ℝ) / 2) + (-1 : ℝ) * 𝒞)) * hC2
  have hp : (0:ℝ) < (2 * 𝒮) ^ 1 := by positivity
  have h2 : (0:ℝ) < (((-1 : ℝ) / 2) + (2 : ℝ) * 𝒞) := by linarith
  rw [← e] at h2
  exact (pos_of_mul_pos_right h2 hp.le).le

lemma cf83 : (0:ℝ) ≤ (0:ℝ) := by
  have hRS := hRS'; have hSC := hSC'; have hC2 := hC2'; have hS := S_pos
  obtain ⟨hCl, hCh⟩ := C_bnd; obtain ⟨hSl, hSh⟩ := S_bnd; obtain ⟨hPl, hPh⟩ := P_bnd
  have e : (2 * 𝒮) ^ 0 * (0:ℝ) = (0:ℝ) := by
    linear_combination ((0:ℝ)) * hRS + ((0:ℝ)) * hSC + ((0:ℝ)) * hC2
  have hp : (0:ℝ) < (2 * 𝒮) ^ 0 := by positivity
  have : (2 * 𝒮) ^ 0 * (0:ℝ) = 0 := by rw [e]
  exact le_of_eq ((mul_eq_zero.mp this).resolve_left hp.ne').symm

lemma cf84 : (0:ℝ) ≤ ((-2 : ℝ) * circumradius * 𝒞 ^ 3 + (2 : ℝ) * 𝒞 * circumradius + (-2 : ℝ) * 𝒞 * circumradius * 𝒮 ^ 2) := by
  have hRS := hRS'; have hSC := hSC'; have hC2 := hC2'; have hS := S_pos
  obtain ⟨hCl, hCh⟩ := C_bnd; obtain ⟨hSl, hSh⟩ := S_bnd; obtain ⟨hPl, hPh⟩ := P_bnd
  have e : (2 * 𝒮) ^ 1 * ((-2 : ℝ) * circumradius * 𝒞 ^ 3 + (2 : ℝ) * 𝒞 * circumradius + (-2 : ℝ) * 𝒞 * circumradius * 𝒮 ^ 2) = (0:ℝ) := by
    linear_combination (((-2 : ℝ) * 𝒞 ^ 3 + (2 : ℝ) * 𝒞 + (-2 : ℝ) * 𝒞 * 𝒮 ^ 2)) * hRS + (((-2 : ℝ) * 𝒞)) * hSC + ((0:ℝ)) * hC2
  have hp : (0:ℝ) < (2 * 𝒮) ^ 1 := by positivity
  have : (2 * 𝒮) ^ 1 * ((-2 : ℝ) * circumradius * 𝒞 ^ 3 + (2 : ℝ) * 𝒞 * circumradius + (-2 : ℝ) * 𝒞 * circumradius * 𝒮 ^ 2) = 0 := by rw [e]
  exact le_of_eq ((mul_eq_zero.mp this).resolve_left hp.ne').symm

lemma cf85 : (0:ℝ) ≤ ((1 : ℝ) * 𝒞 * circumradius + (1 : ℝ) * circumradius * 𝒞 ^ 2 + (-1 : ℝ) * circumradius * 𝒮 ^ 2) := by
  have hRS := hRS'; have hSC := hSC'; have hC2 := hC2'; have hS := S_pos
  obtain ⟨hCl, hCh⟩ := C_bnd; obtain ⟨hSl, hSh⟩ := S_bnd; obtain ⟨hPl, hPh⟩ := P_bnd
  have e : (2 * 𝒮) ^ 1 * ((1 : ℝ) * 𝒞 * circumradius + (1 : ℝ) * circumradius * 𝒞 ^ 2 + (-1 : ℝ) * circumradius * 𝒮 ^ 2) = (((-1 : ℝ) / 2) + (2 : ℝ) * 𝒞) := by
    linear_combination (((1 : ℝ) * 𝒞 + (1 : ℝ) * 𝒞 ^ 2 + (-1 : ℝ) * 𝒮 ^ 2)) * hRS + (((-1 : ℝ))) * hSC + ((((1 : ℝ) / 2))) * hC2
  have hp : (0:ℝ) < (2 * 𝒮) ^ 1 := by positivity
  have h2 : (0:ℝ) < (((-1 : ℝ) / 2) + (2 : ℝ) * 𝒞) := by linarith
  rw [← e] at h2
  exact (pos_of_mul_pos_right h2 hp.le).le

lemma cf86 : (0:ℝ) ≤ ((1 : ℝ) * 𝒞 * circumradius + (1 : ℝ) * circumradius * 𝒞 ^ 2 + (1 : ℝ) * circumradius * 𝒮 ^ 2) := by
  have hRS := hRS'; have hSC := hSC'; have hC2 := hC2'; have hS := S_pos
  obtain ⟨hCl, hCh⟩ := C_bnd; obtain ⟨hSl, hSh⟩ := S_bnd; obtain ⟨hPl, hPh⟩ := P_bnd
  have e : (2 * 𝒮) ^ 1 * ((1 : ℝ) * 𝒞 * circumradius + (1 : ℝ) * circumradius * 𝒞 ^ 2 + (1 : ℝ) * circumradius * 𝒮 ^ 2) = ((1 : ℝ) + (1 : ℝ) * 𝒞) := by
    linear_combination (((1 : ℝ) * 𝒞 + (1 : ℝ) * 𝒞 ^ 2 + (1 : ℝ) * 𝒮 ^ 2)) * hRS + (((1 : ℝ))) * hSC + ((0:ℝ)) * hC2
  have hp : (0:ℝ) < (2 * 𝒮) ^ 1 := by positivity
  have h2 : (0:ℝ) < ((1 : ℝ) + (1 : ℝ) * 𝒞) := by linarith
  rw [← e] at h2
  exact (pos_of_mul_pos_right h2 hp.le).le

lemma cf87 : (0:ℝ) ≤ ((1 : ℝ) * 𝒞 + (-1 : ℝ) * circumradius * 𝒮) := by
  have hRS := hRS'; have hSC := hSC'; have hC2 := hC2'; have hS := S_pos
  obtain ⟨hCl, hCh⟩ := C_bnd; obtain ⟨hSl, hSh⟩ := S_bnd; obtain ⟨hPl, hPh⟩ := P_bnd
  have e : (2 * 𝒮) ^ 1 * ((1 : ℝ) * 𝒞 + (-1 : ℝ) * circumradius * 𝒮) = ((-1 : ℝ) * 𝒮 + (2 : ℝ) * 𝒞 * 𝒮) := by
    linear_combination (((-1 : ℝ) * 𝒮)) * hRS + ((0:ℝ)) * hSC + ((0:ℝ)) * hC2
  have hp : (0:ℝ) < (2 * 𝒮) ^ 1 := by positivity
  have h2 : (0:ℝ) < ((-1 : ℝ) * 𝒮 + (2 : ℝ) * 𝒞 * 𝒮) := by linarith
  rw [← e] at h2
  exact (pos_of_mul_pos_right h2 hp.le).le

lemma cf88 : (0:ℝ) ≤ ((1 : ℝ) * 𝒞 + (1 : ℝ) * circumradius * 𝒮) := by
  have hRS := hRS'; have hSC := hSC'; have hC2 := hC2'; have hS := S_pos
  obtain ⟨hCl, hCh⟩ := C_bnd; obtain ⟨hSl, hSh⟩ := S_bnd; obtain ⟨hPl, hPh⟩ := P_bnd
  have e : (2 * 𝒮) ^ 1 * ((1 : ℝ) * 𝒞 + (1 : ℝ) * circumradius * 𝒮) = ((1 : ℝ) * 𝒮 + (2 : ℝ) * 𝒞 * 𝒮) := by
    linear_combination (((1 : ℝ) * 𝒮)) * hRS + ((0:ℝ)) * hSC + ((0:ℝ)) * hC2
  have hp : (0:ℝ) < (2 * 𝒮) ^ 1 := by positivity
  have h2 : (0:ℝ) < ((1 : ℝ) * 𝒮 + (2 : ℝ) * 𝒞 * 𝒮) := by linarith
  rw [← e] at h2
  exact (pos_of_mul_pos_right h2 hp.le).le

lemma cf89 : (0:ℝ) ≤ ((1 : ℝ) * 𝒞 + (2 : ℝ) * 𝒞 * circumradius * 𝒮) := by
  have hRS := hRS'; have hSC := hSC'; have hC2 := hC2'; have hS := S_pos
  obtain ⟨hCl, hCh⟩ := C_bnd; obtain ⟨hSl, hSh⟩ := S_bnd; obtain ⟨hPl, hPh⟩ := P_bnd
  have e : (2 * 𝒮) ^ 1 * ((1 : ℝ) * 𝒞 + (2 : ℝ) * 𝒞 * circumradius * 𝒮) = ((4 : ℝ) * 𝒞 * 𝒮) := by
    linear_combination (((2 : ℝ) * 𝒞 * 𝒮)) * hRS + ((0:ℝ)) * hSC + ((0:ℝ)) * hC2
  have hp : (0:ℝ) < (2 * 𝒮) ^ 1 := by positivity
  have h2 : (0:ℝ) < ((4 : ℝ) * 𝒞 * 𝒮) := by linarith
  rw [← e] at h2
  exact (pos_of_mul_pos_right h2 hp.le).le

lemma cf90 : (0:ℝ) ≤ ((1 : ℝ) * 𝒞) := by
  have hRS := hRS'; have hSC := hSC'; have hC2 := hC2'; have hS := S_pos
  obtain ⟨hCl, hCh⟩ := C_bnd; obtain ⟨hSl, hSh⟩ := S_bnd; obtain ⟨hPl, hPh⟩ := P_bnd
  have e : (2 * 𝒮) ^ 0 * ((1 : ℝ) * 𝒞) = ((1 : ℝ) * 𝒞) := by
    linear_combination ((0:ℝ)) * hRS + ((0:ℝ)) * hSC + ((0:ℝ)) * hC2
  have hp : (0:ℝ) < (2 * 𝒮) ^ 0 := by positivity
  have h2 : (0:ℝ) < ((1 : ℝ) * 𝒞) := by linarith
  rw [← e] at h2
  exact (pos_of_mul_pos_right h2 hp.le).le

lemma cf91 : (0:ℝ) ≤ ((1 : ℝ) * 𝒞 + (1 : ℝ) * circumradius * 𝒮 + (-4 : ℝ) * circumradius * 𝒮 * 𝒞 ^ 2) := by
  have hRS := hRS'; have hSC := hSC'; have hC2 := hC2'; have hS := S_pos
  obtain ⟨hCl, hCh⟩ := C_bnd; obtain ⟨hSl, hSh⟩ := S_bnd; obtain ⟨hPl, hPh⟩ := P_bnd
  have e : (2 * 𝒮) ^ 1 * ((1 : ℝ) * 𝒞 + (1 : ℝ) * circumradius * 𝒮 + (-4 : ℝ) * circumradius * 𝒮 * 𝒞 ^ 2) = (0:ℝ) := by
    linear_combination (((1 : ℝ) * 𝒮 + (-4 : ℝ) * 𝒮 * 𝒞 ^ 2)) * hRS + ((0:ℝ)) * hSC + (((-1 : ℝ) * 𝒮)) * hC2
  have hp : (0:ℝ) < (2 * 𝒮) ^ 1 := by positivity
  have : (2 * 𝒮) ^ 1 * ((1 : ℝ) * 𝒞 + (1 : ℝ) * circumradius * 𝒮 + (-4 : ℝ) * circumradius * 𝒮 * 𝒞 ^ 2) = 0 := by rw [e]
  exact le_of_eq ((mul_eq_zero.mp this).resolve_left hp.ne').symm

lemma cf92 : (0:ℝ) ≤ (0:ℝ) := by
  have hRS := hRS'; have hSC := hSC'; have hC2 := hC2'; have hS := S_pos
  obtain ⟨hCl, hCh⟩ := C_bnd; obtain ⟨hSl, hSh⟩ := S_bnd; obtain ⟨hPl, hPh⟩ := P_bnd
  have e : (2 * 𝒮) ^ 0 * (0:ℝ) = (0:ℝ) := by
    linear_combination ((0:ℝ)) * hRS + ((0:ℝ)) * hSC + ((0:ℝ)) * hC2
  have hp : (0:ℝ) < (2 * 𝒮) ^ 0 := by positivity
  have : (2 * 𝒮) ^ 0 * (0:ℝ) = 0 := by rw [e]
  exact le_of_eq ((mul_eq_zero.mp this).resolve_left hp.ne').symm

lemma cf93 : (0:ℝ) ≤ ((-2 : ℝ) * circumradius * 𝒞 ^ 3 + (2 : ℝ) * 𝒞 * circumradius + (-2 : ℝ) * 𝒞 * circumradius * 𝒮 ^ 2) := by
  have hRS := hRS'; have hSC := hSC'; have hC2 := hC2'; have hS := S_pos
  obtain ⟨hCl, hCh⟩ := C_bnd; obtain ⟨hSl, hSh⟩ := S_bnd; obtain ⟨hPl, hPh⟩ := P_bnd
  have e : (2 * 𝒮) ^ 1 * ((-2 : ℝ) * circumradius * 𝒞 ^ 3 + (2 : ℝ) * 𝒞 * circumradius + (-2 : ℝ) * 𝒞 * circumradius * 𝒮 ^ 2) = (0:ℝ) := by
    linear_combination (((-2 : ℝ) * 𝒞 ^ 3 + (2 : ℝ) * 𝒞 + (-2 : ℝ) * 𝒞 * 𝒮 ^ 2)) * hRS + (((-2 : ℝ) * 𝒞)) * hSC + ((0:ℝ)) * hC2
  have hp : (0:ℝ) < (2 * 𝒮) ^ 1 := by positivity
  have : (2 * 𝒮) ^ 1 * ((-2 : ℝ) * circumradius * 𝒞 ^ 3 + (2 : ℝ) * 𝒞 * circumradius + (-2 : ℝ) * 𝒞 * circumradius * 𝒮 ^ 2) = 0 := by rw [e]
  exact le_of_eq ((mul_eq_zero.mp this).resolve_left hp.ne').symm

lemma cf94 : (0:ℝ) ≤ ((1 : ℝ) * 𝒞 * circumradius + (1 : ℝ) * circumradius * 𝒞 ^ 2 + (-1 : ℝ) * circumradius * 𝒮 ^ 2) := by
  have hRS := hRS'; have hSC := hSC'; have hC2 := hC2'; have hS := S_pos
  obtain ⟨hCl, hCh⟩ := C_bnd; obtain ⟨hSl, hSh⟩ := S_bnd; obtain ⟨hPl, hPh⟩ := P_bnd
  have e : (2 * 𝒮) ^ 1 * ((1 : ℝ) * 𝒞 * circumradius + (1 : ℝ) * circumradius * 𝒞 ^ 2 + (-1 : ℝ) * circumradius * 𝒮 ^ 2) = (((-1 : ℝ) / 2) + (2 : ℝ) * 𝒞) := by
    linear_combination (((1 : ℝ) * 𝒞 + (1 : ℝ) * 𝒞 ^ 2 + (-1 : ℝ) * 𝒮 ^ 2)) * hRS + (((-1 : ℝ))) * hSC + ((((1 : ℝ) / 2))) * hC2
  have hp : (0:ℝ) < (2 * 𝒮) ^ 1 := by positivity
  have h2 : (0:ℝ) < (((-1 : ℝ) / 2) + (2 : ℝ) * 𝒞) := by linarith
  rw [← e] at h2
  exact (pos_of_mul_pos_right h2 hp.le).le

lemma cf95 : (0:ℝ) ≤ ((1 : ℝ) * 𝒞 * circumradius + (1 : ℝ) * circumradius * 𝒞 ^ 2 + (1 : ℝ) * circumradius * 𝒮 ^ 2) := by
  have hRS := hRS'; have hSC := hSC'; have hC2 := hC2'; have hS := S_pos
  obtain ⟨hCl, hCh⟩ := C_bnd; obtain ⟨hSl, hSh⟩ := S_bnd; obtain ⟨hPl, hPh⟩ := P_bnd
  have e : (2 * 𝒮) ^ 1 * ((1 : ℝ) * 𝒞 * circumradius + (1 : ℝ) * circumradius * 𝒞 ^ 2 + (1 : ℝ) * circumradius * 𝒮 ^ 2) = ((1 : ℝ) + (1 : ℝ) * 𝒞) := by
    linear_combination (((1 : ℝ) * 𝒞 + (1 : ℝ) * 𝒞 ^ 2 + (1 : ℝ) * 𝒮 ^ 2)) * hRS + (((1 : ℝ))) * hSC + ((0:ℝ)) * hC2
  have hp : (0:ℝ) < (2 * 𝒮) ^ 1 := by positivity
  have h2 : (0:ℝ) < ((1 : ℝ) + (1 : ℝ) * 𝒞) := by linarith
  rw [← e] at h2
  exact (pos_of_mul_pos_right h2 hp.le).le

lemma cf96 : (0:ℝ) ≤ ((-2 : ℝ) * circumradius * 𝒞 ^ 3 + (2 : ℝ) * 𝒞 * circumradius + (2 : ℝ) * 𝒞 * circumradius * 𝒮 ^ 2) := by
  have hRS := hRS'; have hSC := hSC'; have hC2 := hC2'; have hS := S_pos
  obtain ⟨hCl, hCh⟩ := C_bnd; obtain ⟨hSl, hSh⟩ := S_bnd; obtain ⟨hPl, hPh⟩ := P_bnd
  have e : (2 * 𝒮) ^ 1 * ((-2 : ℝ) * circumradius * 𝒞 ^ 3 + (2 : ℝ) * 𝒞 * circumradius + (2 : ℝ) * 𝒞 * circumradius * 𝒮 ^ 2) = (((-1 : ℝ) / 2) + (2 : ℝ) * 𝒞) := by
    linear_combination (((-2 : ℝ) * 𝒞 ^ 3 + (2 : ℝ) * 𝒞 + (2 : ℝ) * 𝒞 * 𝒮 ^ 2)) * hRS + (((2 : ℝ) * 𝒞)) * hSC + ((((-1 : ℝ) / 2) + (-1 : ℝ) * 𝒞)) * hC2
  have hp : (0:ℝ) < (2 * 𝒮) ^ 1 := by positivity
  have h2 : (0:ℝ) < (((-1 : ℝ) / 2) + (2 : ℝ) * 𝒞) := by linarith
  rw [← e] at h2
  exact (pos_of_mul_pos_right h2 hp.le).le

lemma cf97 : (0:ℝ) ≤ ((1 : ℝ) * 𝒞 * circumradius + (1 : ℝ) * circumradius * 𝒞 ^ 2 + (1 : ℝ) * circumradius * 𝒮 ^ 2) := by
  have hRS := hRS'; have hSC := hSC'; have hC2 := hC2'; have hS := S_pos
  obtain ⟨hCl, hCh⟩ := C_bnd; obtain ⟨hSl, hSh⟩ := S_bnd; obtain ⟨hPl, hPh⟩ := P_bnd
  have e : (2 * 𝒮) ^ 1 * ((1 : ℝ) * 𝒞 * circumradius + (1 : ℝ) * circumradius * 𝒞 ^ 2 + (1 : ℝ) * circumradius * 𝒮 ^ 2) = ((1 : ℝ) + (1 : ℝ) * 𝒞) := by
    linear_combination (((1 : ℝ) * 𝒞 + (1 : ℝ) * 𝒞 ^ 2 + (1 : ℝ) * 𝒮 ^ 2)) * hRS + (((1 : ℝ))) * hSC + ((0:ℝ)) * hC2
  have hp : (0:ℝ) < (2 * 𝒮) ^ 1 := by positivity
  have h2 : (0:ℝ) < ((1 : ℝ) + (1 : ℝ) * 𝒞) := by linarith
  rw [← e] at h2
  exact (pos_of_mul_pos_right h2 hp.le).le

lemma cf98 : (0:ℝ) ≤ ((-2 : ℝ) * circumradius * 𝒞 ^ 3 + (2 : ℝ) * 𝒞 * circumradius + (2 : ℝ) * 𝒞 * circumradius * 𝒮 ^ 2) := by
  have hRS := hRS'; have hSC := hSC'; have hC2 := hC2'; have hS := S_pos
  obtain ⟨hCl, hCh⟩ := C_bnd; obtain ⟨hSl, hSh⟩ := S_bnd; obtain ⟨hPl, hPh⟩ := P_bnd
  have e : (2 * 𝒮) ^ 1 * ((-2 : ℝ) * circumradius * 𝒞 ^ 3 + (2 : ℝ) * 𝒞 * circumradius + (2 : ℝ) * 𝒞 * circumradius * 𝒮 ^ 2) = (((-1 : ℝ) / 2) + (2 : ℝ) * 𝒞) := by
    linear_combination (((-2 : ℝ) * 𝒞 ^ 3 + (2 : ℝ) * 𝒞 + (2 : ℝ) * 𝒞 * 𝒮 ^ 2)) * hRS + (((2 : ℝ) * 𝒞)) * hSC + ((((-1 : ℝ) / 2) + (-1 : ℝ) * 𝒞)) * hC2
  have hp : (0:ℝ) < (2 * 𝒮) ^ 1 := by positivity
  have h2 : (0:ℝ) < (((-1 : ℝ) / 2) + (2 : ℝ) * 𝒞) := by linarith
  rw [← e] at h2
  exact (pos_of_mul_pos_right h2 hp.le).le

lemma cf99 : (0:ℝ) ≤ (0:ℝ) := by
  have hRS := hRS'; have hSC := hSC'; have hC2 := hC2'; have hS := S_pos
  obtain ⟨hCl, hCh⟩ := C_bnd; obtain ⟨hSl, hSh⟩ := S_bnd; obtain ⟨hPl, hPh⟩ := P_bnd
  have e : (2 * 𝒮) ^ 0 * (0:ℝ) = (0:ℝ) := by
    linear_combination ((0:ℝ)) * hRS + ((0:ℝ)) * hSC + ((0:ℝ)) * hC2
  have hp : (0:ℝ) < (2 * 𝒮) ^ 0 := by positivity
  have : (2 * 𝒮) ^ 0 * (0:ℝ) = 0 := by rw [e]
  exact le_of_eq ((mul_eq_zero.mp this).resolve_left hp.ne').symm

lemma cf100 : (0:ℝ) ≤ ((-2 : ℝ) * circumradius * 𝒞 ^ 3 + (2 : ℝ) * 𝒞 * circumradius + (-2 : ℝ) * 𝒞 * circumradius * 𝒮 ^ 2) := by
  have hRS := hRS'; have hSC := hSC'; have hC2 := hC2'; have hS := S_pos
  obtain ⟨hCl, hCh⟩ := C_bnd; obtain ⟨hSl, hSh⟩ := S_bnd; obtain ⟨hPl, hPh⟩ := P_bnd
  have e : (2 * 𝒮) ^ 1 * ((-2 : ℝ) * circumradius * 𝒞 ^ 3 + (2 : ℝ) * 𝒞 * circumradius + (-2 : ℝ) * 𝒞 * circumradius * 𝒮 ^ 2) = (0:ℝ) := by
    linear_combination (((-2 : ℝ) * 𝒞 ^ 3 + (2 : ℝ) * 𝒞 + (-2 : ℝ) * 𝒞 * 𝒮 ^ 2)) * hRS + (((-2 : ℝ) * 𝒞)) * hSC + ((0:ℝ)) * hC2
  have hp : (0:ℝ) < (2 * 𝒮) ^ 1 := by positivity
  have : (2 * 𝒮) ^ 1 * ((-2 : ℝ) * circumradius * 𝒞 ^ 3 + (2 : ℝ) * 𝒞 * circumradius + (-2 : ℝ) * 𝒞 * circumradius * 𝒮 ^ 2) = 0 := by rw [e]
  exact le_of_eq ((mul_eq_zero.mp this).resolve_left hp.ne').symm

lemma cf101 : (0:ℝ) ≤ ((1 : ℝ) * 𝒞 * circumradius + (1 : ℝ) * circumradius * 𝒞 ^ 2 + (-1 : ℝ) * circumradius * 𝒮 ^ 2) := by
  have hRS := hRS'; have hSC := hSC'; have hC2 := hC2'; have hS := S_pos
  obtain ⟨hCl, hCh⟩ := C_bnd; obtain ⟨hSl, hSh⟩ := S_bnd; obtain ⟨hPl, hPh⟩ := P_bnd
  have e : (2 * 𝒮) ^ 1 * ((1 : ℝ) * 𝒞 * circumradius + (1 : ℝ) * circumradius * 𝒞 ^ 2 + (-1 : ℝ) * circumradius * 𝒮 ^ 2) = (((-1 : ℝ) / 2) + (2 : ℝ) * 𝒞) := by
    linear_combination (((1 : ℝ) * 𝒞 + (1 : ℝ) * 𝒞 ^ 2 + (-1 : ℝ) * 𝒮 ^ 2)) * hRS + (((-1 : ℝ))) * hSC + ((((1 : ℝ) / 2))) * hC2
  have hp : (0:ℝ) < (2 * 𝒮) ^ 1 := by positivity
  have h2 : (0:ℝ) < (((-1 : ℝ) / 2) + (2 : ℝ) * 𝒞) := by linarith
  rw [← e] at h2
  exact (pos_of_mul_pos_right h2 hp.le).le

lemma s3_lo : ((7270293 : ℝ) / 2500000) ≤ s3 := by
  have h := cf1; have hD : (0:ℝ) < 𝒮 * (𝒞 + 𝒮) ^ 2 := by have := S_pos; have := C_pos; positivity
  unfold s3; rw [le_div_iff₀ hD]; nlinarith [h]

lemma s3_hi : s3 ≤ ((29081173 : ℝ) / 10000000) := by
  have h := cf2; have hD : (0:ℝ) < 𝒮 * (𝒞 + 𝒮) ^ 2 := by have := S_pos; have := C_pos; positivity
  unfold s3; rw [div_le_iff₀ hD]; nlinarith [h]

lemma x0_lo : ((1614673 : ℝ) / 1000000) ≤ x0 := by
  have h1 := cf3; have h2 := cf4; have h3 := s3_lo
  unfold x0; nlinarith [mul_nonneg h1.le (sub_nonneg.2 h3)]

lemma x0_hi : x0 ≤ ((64587 : ℝ) / 40000) := by
  have h1 := cf3; have h2 := cf5; have h3 := s3_hi
  unfold x0; nlinarith [mul_nonneg h1.le (sub_nonneg.2 h3)]

lemma y2_lo : ((1865711 : ℝ) / 1000000) ≤ y2 := by
  have h1 := cf6; have h2 := cf7; have h3 := s3_lo
  unfold y2; nlinarith [mul_nonneg h1.le (sub_nonneg.2 h3)]

lemma y2_hi : y2 ≤ ((932857 : ℝ) / 500000) := by
  have h1 := cf6; have h2 := cf8; have h3 := s3_hi
  unfold y2; nlinarith [mul_nonneg h1.le (sub_nonneg.2 h3)]

lemma E1 : ((-1 : ℝ) * 𝒞 + (-1 : ℝ) * 𝒞 ^ 2 + (1 : ℝ) * 𝒞 * s3 + (1 : ℝ) * 𝒮 * s3 + (-1 : ℝ) * 𝒞 * circumradius + (-1 : ℝ) * circumradius * 𝒞 ^ 2 + (-1 : ℝ) * 𝒮 * x0 + (-1 : ℝ) * 𝒞 * circumradius * 𝒮) = 0 := by
  have h := cf9; unfold x0; linarith [h]

lemma E3 : ((1 : ℝ) * 𝒞 * s3 + (1 : ℝ) * 𝒮 * s3 + (-1 : ℝ) * 𝒞 * 𝒮 + (-1 : ℝ) * 𝒮 * y2 + (-2 : ℝ) * 𝒞 * circumradius + (-2 : ℝ) * circumradius * 𝒞 ^ 2) = 0 := by
  have h := cf10; unfold y2; linarith [h]

lemma E2 : ((-1 : ℝ) * 𝒞 + (1 : ℝ) * 𝒞 * y2 + (1 : ℝ) * 𝒮 * x0 + (-1 : ℝ) * 𝒞 * circumradius + (-1 : ℝ) * circumradius * 𝒞 ^ 2 + (-1 : ℝ) * 𝒞 * circumradius * 𝒮) = 0 := by
  have hz := cf11
  have hs3 : s3 * (𝒮 * (𝒞 + 𝒮) ^ 2) = 𝒞 * (𝒞 ^ 2 + 2 * 𝒞 * 𝒮 ^ 2 + 𝒞 * 𝒮 + 𝒞 + 3 * 𝒮 ^ 2 + 𝒮) := by
    have := S_pos; have := C_pos; unfold s3; exact div_mul_cancel₀ _ (by positivity)
  have hD : (𝒮 * (𝒞 + 𝒮) ^ 2) ≠ 0 := by have := S_pos; have := C_pos; positivity
  have h : (𝒮 * (𝒞 + 𝒮) ^ 2) * ((-1 : ℝ) * 𝒞 + (1 : ℝ) * 𝒞 * y2 + (1 : ℝ) * 𝒮 * x0 + (-1 : ℝ) * 𝒞 * circumradius + (-1 : ℝ) * circumradius * 𝒞 ^ 2 + (-1 : ℝ) * 𝒞 * circumradius * 𝒮) = 0 := by
    unfold x0 y2
    linear_combination (((1 : ℝ) * 𝒞 + (1 : ℝ) * 𝒮 + (2 : ℝ) * circumradius * 𝒞 ^ 2 + (2 : ℝ) * 𝒞 * circumradius * 𝒮)) * hs3 + hz
  exact (mul_eq_zero.mp h).resolve_left hD

lemma vc_P0_0 : circumradius * cos (π / 10 + 2 * π * ((0:ℕ):ℝ) / 5) = circumradius * ((2 : ℝ) * 𝒞 * 𝒮) := by
  rw [show π / 10 + 2 * π * ((0:ℕ):ℝ) / 5 = π / 10 by push_cast; ring, tab_c_18]; try ring
lemma vs_P0_0 : circumradius * sin (π / 10 + 2 * π * ((0:ℕ):ℝ) / 5) = circumradius * ((-1 : ℝ) + (2 : ℝ) * 𝒞 ^ 2) := by
  rw [show π / 10 + 2 * π * ((0:ℕ):ℝ) / 5 = π / 10 by push_cast; ring, tab_s_18]; try ring
lemma vc_P0_1 : circumradius * cos (π / 10 + 2 * π * ((1:ℕ):ℝ) / 5) = circumradius * (0:ℝ) := by
  rw [show π / 10 + 2 * π * ((1:ℕ):ℝ) / 5 = π / 2 by push_cast; ring, tab_c_90]; try ring
lemma vs_P0_1 : circumradius * sin (π / 10 + 2 * π * ((1:ℕ):ℝ) / 5) = circumradius * ((1 : ℝ)) := by
  rw [show π / 10 + 2 * π * ((1:ℕ):ℝ) / 5 = π / 2 by push_cast; ring, tab_s_90]; try ring
lemma vc_P0_2 : circumradius * cos (π / 10 + 2 * π * ((2:ℕ):ℝ) / 5) = circumradius * ((-2 : ℝ) * 𝒞 * 𝒮) := by
  rw [show π / 10 + 2 * π * ((2:ℕ):ℝ) / 5 = 9 * π / 10 by push_cast; ring, tab_c_162]; try ring
lemma vs_P0_2 : circumradius * sin (π / 10 + 2 * π * ((2:ℕ):ℝ) / 5) = circumradius * ((-1 : ℝ) + (2 : ℝ) * 𝒞 ^ 2) := by
  rw [show π / 10 + 2 * π * ((2:ℕ):ℝ) / 5 = 9 * π / 10 by push_cast; ring, tab_s_162]; try ring
lemma vc_P0_3 : circumradius * cos (π / 10 + 2 * π * ((3:ℕ):ℝ) / 5) = circumradius * ((-1 : ℝ) * 𝒮) := by
  rw [show π / 10 + 2 * π * ((3:ℕ):ℝ) / 5 = 13 * π / 10 by push_cast; ring, tab_c_234]; try ring
lemma vs_P0_3 : circumradius * sin (π / 10 + 2 * π * ((3:ℕ):ℝ) / 5) = circumradius * ((-1 : ℝ) * 𝒞) := by
  rw [show π / 10 + 2 * π * ((3:ℕ):ℝ) / 5 = 13 * π / 10 by push_cast; ring, tab_s_234]; try ring
lemma vc_P0_4 : circumradius * cos (π / 10 + 2 * π * ((4:ℕ):ℝ) / 5) = circumradius * ((1 : ℝ) * 𝒮) := by
  rw [show π / 10 + 2 * π * ((4:ℕ):ℝ) / 5 = 17 * π / 10 by push_cast; ring, tab_c_306]; try ring
lemma vs_P0_4 : circumradius * sin (π / 10 + 2 * π * ((4:ℕ):ℝ) / 5) = circumradius * ((-1 : ℝ) * 𝒞) := by
  rw [show π / 10 + 2 * π * ((4:ℕ):ℝ) / 5 = 17 * π / 10 by push_cast; ring, tab_s_306]; try ring
lemma box_P0 : pentagon (x0) (circumradius * 𝒞) (π / 10) ⊆ Set.Icc 0 s3 ×ˢ Set.Icc 0 s3 := by
  apply hull_sub ((convex_Icc _ _).prod (convex_Icc _ _))
  intro k hk
  interval_cases k
  · rw [vc_P0_0, vs_P0_0]; simp only [Set.mem_prod, Set.mem_Icc]
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · nlinarith [cf12, x0_lo]
    · nlinarith [cf13, x0_hi, s3_lo]
    · nlinarith [cf14]
    · nlinarith [cf15, s3_lo]
  · rw [vc_P0_1, vs_P0_1]; simp only [Set.mem_prod, Set.mem_Icc]
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · nlinarith [cf16, x0_lo]
    · nlinarith [cf17, x0_hi, s3_lo]
    · nlinarith [cf18]
    · nlinarith [cf19, s3_lo]
  · rw [vc_P0_2, vs_P0_2]; simp only [Set.mem_prod, Set.mem_Icc]
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · nlinarith [cf20, x0_lo]
    · nlinarith [cf21, x0_hi, s3_lo]
    · nlinarith [cf22]
    · nlinarith [cf23, s3_lo]
  · rw [vc_P0_3, vs_P0_3]; simp only [Set.mem_prod, Set.mem_Icc]
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · nlinarith [cf24, x0_lo]
    · nlinarith [cf25, x0_hi, s3_lo]
    · nlinarith [cf26]
    · nlinarith [cf27, s3_lo]
  · rw [vc_P0_4, vs_P0_4]; simp only [Set.mem_prod, Set.mem_Icc]
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · nlinarith [cf28, x0_lo]
    · nlinarith [cf29, x0_hi, s3_lo]
    · nlinarith [cf30]
    · nlinarith [cf31, s3_lo]
lemma vc_P1_0 : circumradius * cos (π / 5 + 2 * π * ((0:ℕ):ℝ) / 5) = circumradius * ((1 : ℝ) * 𝒞) := by
  rw [show π / 5 + 2 * π * ((0:ℕ):ℝ) / 5 = π / 5 by push_cast; ring, tab_c_36]; try ring
lemma vs_P1_0 : circumradius * sin (π / 5 + 2 * π * ((0:ℕ):ℝ) / 5) = circumradius * ((1 : ℝ) * 𝒮) := by
  rw [show π / 5 + 2 * π * ((0:ℕ):ℝ) / 5 = π / 5 by push_cast; ring, tab_s_36]; try ring
lemma vc_P1_1 : circumradius * cos (π / 5 + 2 * π * ((1:ℕ):ℝ) / 5) = circumradius * ((1 : ℝ) + (-2 : ℝ) * 𝒞 ^ 2) := by
  rw [show π / 5 + 2 * π * ((1:ℕ):ℝ) / 5 = 3 * π / 5 by push_cast; ring, tab_c_108]; try ring
lemma vs_P1_1 : circumradius * sin (π / 5 + 2 * π * ((1:ℕ):ℝ) / 5) = circumradius * ((2 : ℝ) * 𝒞 * 𝒮) := by
  rw [show π / 5 + 2 * π * ((1:ℕ):ℝ) / 5 = 3 * π / 5 by push_cast; ring, tab_s_108]; try ring
lemma vc_P1_2 : circumradius * cos (π / 5 + 2 * π * ((2:ℕ):ℝ) / 5) = circumradius * ((-1 : ℝ)) := by
  rw [show π / 5 + 2 * π * ((2:ℕ):ℝ) / 5 = π by push_cast; ring, tab_c_180]; try ring
lemma vs_P1_2 : circumradius * sin (π / 5 + 2 * π * ((2:ℕ):ℝ) / 5) = circumradius * (0:ℝ) := by
  rw [show π / 5 + 2 * π * ((2:ℕ):ℝ) / 5 = π by push_cast; ring, tab_s_180]; try ring
lemma vc_P1_3 : circumradius * cos (π / 5 + 2 * π * ((3:ℕ):ℝ) / 5) = circumradius * ((1 : ℝ) + (-2 : ℝ) * 𝒞 ^ 2) := by
  rw [show π / 5 + 2 * π * ((3:ℕ):ℝ) / 5 = 7 * π / 5 by push_cast; ring, tab_c_252]; try ring
lemma vs_P1_3 : circumradius * sin (π / 5 + 2 * π * ((3:ℕ):ℝ) / 5) = circumradius * ((-2 : ℝ) * 𝒞 * 𝒮) := by
  rw [show π / 5 + 2 * π * ((3:ℕ):ℝ) / 5 = 7 * π / 5 by push_cast; ring, tab_s_252]; try ring
lemma vc_P1_4 : circumradius * cos (π / 5 + 2 * π * ((4:ℕ):ℝ) / 5) = circumradius * ((1 : ℝ) * 𝒞) := by
  rw [show π / 5 + 2 * π * ((4:ℕ):ℝ) / 5 = 9 * π / 5 by push_cast; ring, tab_c_324]; try ring
lemma vs_P1_4 : circumradius * sin (π / 5 + 2 * π * ((4:ℕ):ℝ) / 5) = circumradius * ((-1 : ℝ) * 𝒮) := by
  rw [show π / 5 + 2 * π * ((4:ℕ):ℝ) / 5 = 9 * π / 5 by push_cast; ring, tab_s_324]; try ring
lemma box_P1 : pentagon (s3 - circumradius * 𝒞) (s3 - 𝒞) (π / 5) ⊆ Set.Icc 0 s3 ×ˢ Set.Icc 0 s3 := by
  apply hull_sub ((convex_Icc _ _).prod (convex_Icc _ _))
  intro k hk
  interval_cases k
  · rw [vc_P1_0, vs_P1_0]; simp only [Set.mem_prod, Set.mem_Icc]
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · nlinarith [cf32, s3_lo]
    · nlinarith [cf33]
    · nlinarith [cf34, s3_lo]
    · nlinarith [cf35]
  · rw [vc_P1_1, vs_P1_1]; simp only [Set.mem_prod, Set.mem_Icc]
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · nlinarith [cf36, s3_lo]
    · nlinarith [cf37]
    · nlinarith [cf38, s3_lo]
    · nlinarith [cf39]
  · rw [vc_P1_2, vs_P1_2]; simp only [Set.mem_prod, Set.mem_Icc]
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · nlinarith [cf40, s3_lo]
    · nlinarith [cf41]
    · nlinarith [cf42, s3_lo]
    · nlinarith [cf43]
  · rw [vc_P1_3, vs_P1_3]; simp only [Set.mem_prod, Set.mem_Icc]
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · nlinarith [cf44, s3_lo]
    · nlinarith [cf45]
    · nlinarith [cf46, s3_lo]
    · nlinarith [cf47]
  · rw [vc_P1_4, vs_P1_4]; simp only [Set.mem_prod, Set.mem_Icc]
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · nlinarith [cf48, s3_lo]
    · nlinarith [cf49]
    · nlinarith [cf50, s3_lo]
    · nlinarith [cf51]
lemma vc_P2_0 : circumradius * cos (0 + 2 * π * ((0:ℕ):ℝ) / 5) = circumradius * ((1 : ℝ)) := by
  rw [show 0 + 2 * π * ((0:ℕ):ℝ) / 5 = 0 by push_cast; ring, tab_c_0]; try ring
lemma vs_P2_0 : circumradius * sin (0 + 2 * π * ((0:ℕ):ℝ) / 5) = circumradius * (0:ℝ) := by
  rw [show 0 + 2 * π * ((0:ℕ):ℝ) / 5 = 0 by push_cast; ring, tab_s_0]; try ring
lemma vc_P2_1 : circumradius * cos (0 + 2 * π * ((1:ℕ):ℝ) / 5) = circumradius * ((-1 : ℝ) + (2 : ℝ) * 𝒞 ^ 2) := by
  rw [show 0 + 2 * π * ((1:ℕ):ℝ) / 5 = 2 * π / 5 by push_cast; ring, tab_c_72]; try ring
lemma vs_P2_1 : circumradius * sin (0 + 2 * π * ((1:ℕ):ℝ) / 5) = circumradius * ((2 : ℝ) * 𝒞 * 𝒮) := by
  rw [show 0 + 2 * π * ((1:ℕ):ℝ) / 5 = 2 * π / 5 by push_cast; ring, tab_s_72]; try ring
lemma vc_P2_2 : circumradius * cos (0 + 2 * π * ((2:ℕ):ℝ) / 5) = circumradius * ((-1 : ℝ) * 𝒞) := by
  rw [show 0 + 2 * π * ((2:ℕ):ℝ) / 5 = 4 * π / 5 by push_cast; ring, tab_c_144]; try ring
lemma vs_P2_2 : circumradius * sin (0 + 2 * π * ((2:ℕ):ℝ) / 5) = circumradius * ((1 : ℝ) * 𝒮) := by
  rw [show 0 + 2 * π * ((2:ℕ):ℝ) / 5 = 4 * π / 5 by push_cast; ring, tab_s_144]; try ring
lemma vc_P2_3 : circumradius * cos (0 + 2 * π * ((3:ℕ):ℝ) / 5) = circumradius * ((-1 : ℝ) * 𝒞) := by
  rw [show 0 + 2 * π * ((3:ℕ):ℝ) / 5 = 6 * π / 5 by push_cast; ring, tab_c_216]; try ring
lemma vs_P2_3 : circumradius * sin (0 + 2 * π * ((3:ℕ):ℝ) / 5) = circumradius * ((-1 : ℝ) * 𝒮) := by
  rw [show 0 + 2 * π * ((3:ℕ):ℝ) / 5 = 6 * π / 5 by push_cast; ring, tab_s_216]; try ring
lemma vc_P2_4 : circumradius * cos (0 + 2 * π * ((4:ℕ):ℝ) / 5) = circumradius * ((-1 : ℝ) + (2 : ℝ) * 𝒞 ^ 2) := by
  rw [show 0 + 2 * π * ((4:ℕ):ℝ) / 5 = 8 * π / 5 by push_cast; ring, tab_c_288]; try ring
lemma vs_P2_4 : circumradius * sin (0 + 2 * π * ((4:ℕ):ℝ) / 5) = circumradius * ((-2 : ℝ) * 𝒞 * 𝒮) := by
  rw [show 0 + 2 * π * ((4:ℕ):ℝ) / 5 = 8 * π / 5 by push_cast; ring, tab_s_288]; try ring
lemma box_P2 : pentagon (circumradius * 𝒞) (y2) (0) ⊆ Set.Icc 0 s3 ×ˢ Set.Icc 0 s3 := by
  apply hull_sub ((convex_Icc _ _).prod (convex_Icc _ _))
  intro k hk
  interval_cases k
  · rw [vc_P2_0, vs_P2_0]; simp only [Set.mem_prod, Set.mem_Icc]
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · nlinarith [cf52]
    · nlinarith [cf53, s3_lo]
    · nlinarith [cf54, y2_lo]
    · nlinarith [cf55, s3_lo, y2_hi]
  · rw [vc_P2_1, vs_P2_1]; simp only [Set.mem_prod, Set.mem_Icc]
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · nlinarith [cf56]
    · nlinarith [cf57, s3_lo]
    · nlinarith [cf58, y2_lo]
    · nlinarith [cf59, s3_lo, y2_hi]
  · rw [vc_P2_2, vs_P2_2]; simp only [Set.mem_prod, Set.mem_Icc]
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · nlinarith [cf60]
    · nlinarith [cf61, s3_lo]
    · nlinarith [cf62, y2_lo]
    · nlinarith [cf63, s3_lo, y2_hi]
  · rw [vc_P2_3, vs_P2_3]; simp only [Set.mem_prod, Set.mem_Icc]
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · nlinarith [cf64]
    · nlinarith [cf65, s3_lo]
    · nlinarith [cf66, y2_lo]
    · nlinarith [cf67, s3_lo, y2_hi]
  · rw [vc_P2_4, vs_P2_4]; simp only [Set.mem_prod, Set.mem_Icc]
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · nlinarith [cf68]
    · nlinarith [cf69, s3_lo]
    · nlinarith [cf70, y2_lo]
    · nlinarith [cf71, s3_lo, y2_hi]
lemma hp_P0_h01 : pentagon (x0) (circumradius * 𝒞) (π / 10) ⊆ {x : ℝ × ℝ | 𝒮 * x.1 + 𝒞 * x.2 ≤ (𝒮 * x0 + 𝒞 * (circumradius * 𝒞) + circumradius * 𝒞)} := by
  apply hull_sub (convex_le _ _ _)
  intro k hk
  interval_cases k
  · rw [vc_P0_0, vs_P0_0]; simp only [Set.mem_setOf_eq]
    nlinarith [cf72]
  · rw [vc_P0_1, vs_P0_1]; simp only [Set.mem_setOf_eq]
    nlinarith [cf73]
  · rw [vc_P0_2, vs_P0_2]; simp only [Set.mem_setOf_eq]
    nlinarith [cf74]
  · rw [vc_P0_3, vs_P0_3]; simp only [Set.mem_setOf_eq]
    nlinarith [cf75]
  · rw [vc_P0_4, vs_P0_4]; simp only [Set.mem_setOf_eq]
    nlinarith [cf76]
lemma hp_P1_h01 : pentagon (s3 - circumradius * 𝒞) (s3 - 𝒞) (π / 5) ⊆ {x : ℝ × ℝ | (𝒮 * x0 + 𝒞 * (circumradius * 𝒞) + circumradius * 𝒞) ≤ 𝒮 * x.1 + 𝒞 * x.2} := by
  apply hull_sub (convex_ge _ _ _)
  intro k hk
  interval_cases k
  · rw [vc_P1_0, vs_P1_0]; simp only [Set.mem_setOf_eq]
    nlinarith [E1, cf77]
  · rw [vc_P1_1, vs_P1_1]; simp only [Set.mem_setOf_eq]
    nlinarith [E1, cf78]
  · rw [vc_P1_2, vs_P1_2]; simp only [Set.mem_setOf_eq]
    nlinarith [E1, cf79]
  · rw [vc_P1_3, vs_P1_3]; simp only [Set.mem_setOf_eq]
    nlinarith [E1, cf80]
  · rw [vc_P1_4, vs_P1_4]; simp only [Set.mem_setOf_eq]
    nlinarith [E1, cf81]
lemma hp_P0_h02 : pentagon (x0) (circumradius * 𝒞) (π / 10) ⊆ {x : ℝ × ℝ | (-𝒮) * x.1 + 𝒞 * x.2 ≤ (-𝒮 * x0 + 𝒞 * (circumradius * 𝒞) + circumradius * 𝒞)} := by
  apply hull_sub (convex_le _ _ _)
  intro k hk
  interval_cases k
  · rw [vc_P0_0, vs_P0_0]; simp only [Set.mem_setOf_eq]
    nlinarith [cf82]
  · rw [vc_P0_1, vs_P0_1]; simp only [Set.mem_setOf_eq]
    nlinarith [cf83]
  · rw [vc_P0_2, vs_P0_2]; simp only [Set.mem_setOf_eq]
    nlinarith [cf84]
  · rw [vc_P0_3, vs_P0_3]; simp only [Set.mem_setOf_eq]
    nlinarith [cf85]
  · rw [vc_P0_4, vs_P0_4]; simp only [Set.mem_setOf_eq]
    nlinarith [cf86]
lemma hp_P2_h02 : pentagon (circumradius * 𝒞) (y2) (0) ⊆ {x : ℝ × ℝ | (-𝒮 * x0 + 𝒞 * (circumradius * 𝒞) + circumradius * 𝒞) ≤ (-𝒮) * x.1 + 𝒞 * x.2} := by
  apply hull_sub (convex_ge _ _ _)
  intro k hk
  interval_cases k
  · rw [vc_P2_0, vs_P2_0]; simp only [Set.mem_setOf_eq]
    nlinarith [E2, cf87]
  · rw [vc_P2_1, vs_P2_1]; simp only [Set.mem_setOf_eq]
    nlinarith [E2, cf88]
  · rw [vc_P2_2, vs_P2_2]; simp only [Set.mem_setOf_eq]
    nlinarith [E2, cf89]
  · rw [vc_P2_3, vs_P2_3]; simp only [Set.mem_setOf_eq]
    nlinarith [E2, cf90]
  · rw [vc_P2_4, vs_P2_4]; simp only [Set.mem_setOf_eq]
    nlinarith [E2, cf91]
lemma hp_P2_h12 : pentagon (circumradius * 𝒞) (y2) (0) ⊆ {x : ℝ × ℝ | 𝒞 * x.1 + 𝒮 * x.2 ≤ (𝒞 * (circumradius * 𝒞) + 𝒮 * y2 + circumradius * 𝒞)} := by
  apply hull_sub (convex_le _ _ _)
  intro k hk
  interval_cases k
  · rw [vc_P2_0, vs_P2_0]; simp only [Set.mem_setOf_eq]
    nlinarith [cf92]
  · rw [vc_P2_1, vs_P2_1]; simp only [Set.mem_setOf_eq]
    nlinarith [cf93]
  · rw [vc_P2_2, vs_P2_2]; simp only [Set.mem_setOf_eq]
    nlinarith [cf94]
  · rw [vc_P2_3, vs_P2_3]; simp only [Set.mem_setOf_eq]
    nlinarith [cf95]
  · rw [vc_P2_4, vs_P2_4]; simp only [Set.mem_setOf_eq]
    nlinarith [cf96]
lemma hp_P1_h12 : pentagon (s3 - circumradius * 𝒞) (s3 - 𝒞) (π / 5) ⊆ {x : ℝ × ℝ | (𝒞 * (circumradius * 𝒞) + 𝒮 * y2 + circumradius * 𝒞) ≤ 𝒞 * x.1 + 𝒮 * x.2} := by
  apply hull_sub (convex_ge _ _ _)
  intro k hk
  interval_cases k
  · rw [vc_P1_0, vs_P1_0]; simp only [Set.mem_setOf_eq]
    nlinarith [E3, cf97]
  · rw [vc_P1_1, vs_P1_1]; simp only [Set.mem_setOf_eq]
    nlinarith [E3, cf98]
  · rw [vc_P1_2, vs_P1_2]; simp only [Set.mem_setOf_eq]
    nlinarith [E3, cf99]
  · rw [vc_P1_3, vs_P1_3]; simp only [Set.mem_setOf_eq]
    nlinarith [E3, cf100]
  · rw [vc_P1_4, vs_P1_4]; simp only [Set.mem_setOf_eq]
    nlinarith [E3, cf101]

theorem proof : PacksInSquare 3 s3 := by
  have hn : 0 < 𝒮 ^ 2 + 𝒞 ^ 2 := by rw [hSC']; norm_num
  refine ⟨![x0, s3 - circumradius * 𝒞, circumradius * 𝒞], ![circumradius * 𝒞, s3 - 𝒞, y2],
    ![π / 10, π / 5, 0], ?_, ?_⟩
  · intro i
    fin_cases i
    · exact box_P0
    · exact box_P1
    · exact box_P2
  · have d01 : Disjoint (interior (pentagon x0 (circumradius * 𝒞) (π / 10)))
        (interior (pentagon (s3 - circumradius * 𝒞) (s3 - 𝒞) (π / 5))) :=
      halfplane_disjoint _ _ _ (by nlinarith) hp_P0_h01 hp_P1_h01
    have d02 : Disjoint (interior (pentagon x0 (circumradius * 𝒞) (π / 10)))
        (interior (pentagon (circumradius * 𝒞) y2 0)) :=
      halfplane_disjoint _ _ _ (by nlinarith) hp_P0_h02 hp_P2_h02
    have d21 : Disjoint (interior (pentagon (circumradius * 𝒞) y2 0))
        (interior (pentagon (s3 - circumradius * 𝒞) (s3 - 𝒞) (π / 5))) :=
      halfplane_disjoint _ _ _ (by nlinarith) hp_P2_h12 hp_P1_h12
    intro i j hij
    fin_cases i <;> fin_cases j
    all_goals first
      | exact absurd rfl hij
      | exact d01 | exact d01.symm | exact d02 | exact d02.symm | exact d21 | exact d21.symm

end Submissions.PentagonsThreeAttain.Pinwheel
