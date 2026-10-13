import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic

namespace Submissions.PentagonsThirteenAttain.LoydRecord

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

lemma R_lo : (8506508081 / 10000000000 : ℝ) ≤ circumradius := by
  have h1 := hRS'; obtain ⟨hl, hh⟩ := S_bnd; have hS := S_pos
  by_contra h; push_neg at h
  nlinarith [mul_lt_mul_of_pos_right h hS]
lemma R_hi : circumradius ≤ (1701301617 / 2000000000 : ℝ) := by
  have h1 := hRS'; obtain ⟨hl, hh⟩ := S_bnd; have hS := S_pos
  by_contra h; push_neg at h
  nlinarith [mul_lt_mul_of_pos_right h hS]
lemma P_lo : (6881909599 / 10000000000 : ℝ) ≤ circumradius * 𝒞 := by
  have h1 := R_lo; obtain ⟨hl, hh⟩ := C_bnd; have hR := R_pos
  nlinarith [mul_le_mul_of_nonneg_left hl hR.le]
lemma P_hi : circumradius * 𝒞 ≤ (1720477401 / 2500000000 : ℝ) := by
  have h1 := R_hi; obtain ⟨hl, hh⟩ := C_bnd; have hR := R_pos
  nlinarith [mul_le_mul_of_nonneg_left hh hR.le]
lemma C_lo : (8090169943 / 10000000000 : ℝ) ≤ 𝒞 := C_bnd.1
lemma C_hi : 𝒞 ≤ (8090169944 / 10000000000 : ℝ) := C_bnd.2
lemma R_sq_le : circumradius ^ 2 ≤ (1701301617 / 2000000000 : ℝ) ^ 2 := by
  have := R_hi; have := R_pos; nlinarith

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

/-- `R cos (2πk/5)` and `R sin (2πk/5)` for `k = 0..4`, in terms of `R`, `R·C` and `C`. -/
lemma T0c : circumradius * cos (2 * π * ((0:ℕ):ℝ) / 5) = circumradius := by
  rw [show 2 * π * ((0:ℕ):ℝ) / 5 = 0 by simp, cos_zero, mul_one]
lemma T0s : circumradius * sin (2 * π * ((0:ℕ):ℝ) / 5) = 0 := by
  rw [show 2 * π * ((0:ℕ):ℝ) / 5 = 0 by simp, sin_zero, mul_zero]
lemma T1c : circumradius * cos (2 * π * ((1:ℕ):ℝ) / 5) = circumradius * 𝒞 - circumradius / 2 := by
  rw [show 2 * π * ((1:ℕ):ℝ) / 5 = 2 * π / 5 by push_cast; ring, tab_c_72]
  linear_combination (circumradius / 2) * hC2'
lemma T1s : circumradius * sin (2 * π * ((1:ℕ):ℝ) / 5) = 𝒞 := by
  rw [show 2 * π * ((1:ℕ):ℝ) / 5 = 2 * π / 5 by push_cast; ring, tab_s_72]
  linear_combination 𝒞 * hRS'
lemma T2c : circumradius * cos (2 * π * ((2:ℕ):ℝ) / 5) = -(circumradius * 𝒞) := by
  rw [show 2 * π * ((2:ℕ):ℝ) / 5 = 4 * π / 5 by push_cast; ring, tab_c_144]; ring
lemma T2s : circumradius * sin (2 * π * ((2:ℕ):ℝ) / 5) = 1 / 2 := by
  rw [show 2 * π * ((2:ℕ):ℝ) / 5 = 4 * π / 5 by push_cast; ring, tab_s_144]
  linear_combination (1 / 2 : ℝ) * hRS'
lemma T3c : circumradius * cos (2 * π * ((3:ℕ):ℝ) / 5) = -(circumradius * 𝒞) := by
  rw [show 2 * π * ((3:ℕ):ℝ) / 5 = 6 * π / 5 by push_cast; ring, tab_c_216]; ring
lemma T3s : circumradius * sin (2 * π * ((3:ℕ):ℝ) / 5) = -1 / 2 := by
  rw [show 2 * π * ((3:ℕ):ℝ) / 5 = 6 * π / 5 by push_cast; ring, tab_s_216]
  linear_combination (-1 / 2 : ℝ) * hRS'
lemma T4c : circumradius * cos (2 * π * ((4:ℕ):ℝ) / 5) = circumradius * 𝒞 - circumradius / 2 := by
  rw [show 2 * π * ((4:ℕ):ℝ) / 5 = 8 * π / 5 by push_cast; ring, tab_c_288]
  linear_combination (circumradius / 2) * hC2'
lemma T4s : circumradius * sin (2 * π * ((4:ℕ):ℝ) / 5) = -𝒞 := by
  rw [show 2 * π * ((4:ℕ):ℝ) / 5 = 8 * π / 5 by push_cast; ring, tab_s_288]
  linear_combination (-𝒞) * hRS'

lemma vx (θ φ : ℝ) :
    circumradius * cos (θ + φ) = cos θ * (circumradius * cos φ) - sin θ * (circumradius * sin φ) := by
  rw [cos_add]; ring
lemma vy (θ φ : ℝ) :
    circumradius * sin (θ + φ) = sin θ * (circumradius * cos φ) + cos θ * (circumradius * sin φ) := by
  rw [sin_add]; ring

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

/-- A pentagon lies in a half-plane `n·x ≤ d` once its five vertices do. -/
lemma pent_le {a b θ c s n1 n2 d : ℝ} (hc : cos θ = c) (hs : sin θ = s)
    (h0 : n1 * (a + (c * circumradius - s * 0)) + n2 * (b + (s * circumradius + c * 0)) ≤ d)
    (h1 : n1 * (a + (c * (circumradius * 𝒞 - circumradius / 2) - s * 𝒞)) +
      n2 * (b + (s * (circumradius * 𝒞 - circumradius / 2) + c * 𝒞)) ≤ d)
    (h2 : n1 * (a + (c * (-(circumradius * 𝒞)) - s * (1 / 2))) +
      n2 * (b + (s * (-(circumradius * 𝒞)) + c * (1 / 2))) ≤ d)
    (h3 : n1 * (a + (c * (-(circumradius * 𝒞)) - s * (-1 / 2))) +
      n2 * (b + (s * (-(circumradius * 𝒞)) + c * (-1 / 2))) ≤ d)
    (h4 : n1 * (a + (c * (circumradius * 𝒞 - circumradius / 2) - s * (-𝒞))) +
      n2 * (b + (s * (circumradius * 𝒞 - circumradius / 2) + c * (-𝒞))) ≤ d) :
    pentagon a b θ ⊆ {x : ℝ × ℝ | n1 * x.1 + n2 * x.2 ≤ d} := by
  apply hull_sub (convex_le _ _ _)
  intro k hk
  interval_cases k
  · show n1 * (a + circumradius * cos (θ + 2 * π * ((0:ℕ):ℝ) / 5)) +
      n2 * (b + circumradius * sin (θ + 2 * π * ((0:ℕ):ℝ) / 5)) ≤ d
    rw [vx, vy, T0c, T0s, hc, hs]; exact h0
  · show n1 * (a + circumradius * cos (θ + 2 * π * ((1:ℕ):ℝ) / 5)) +
      n2 * (b + circumradius * sin (θ + 2 * π * ((1:ℕ):ℝ) / 5)) ≤ d
    rw [vx, vy, T1c, T1s, hc, hs]; exact h1
  · show n1 * (a + circumradius * cos (θ + 2 * π * ((2:ℕ):ℝ) / 5)) +
      n2 * (b + circumradius * sin (θ + 2 * π * ((2:ℕ):ℝ) / 5)) ≤ d
    rw [vx, vy, T2c, T2s, hc, hs]; exact h2
  · show n1 * (a + circumradius * cos (θ + 2 * π * ((3:ℕ):ℝ) / 5)) +
      n2 * (b + circumradius * sin (θ + 2 * π * ((3:ℕ):ℝ) / 5)) ≤ d
    rw [vx, vy, T3c, T3s, hc, hs]; exact h3
  · show n1 * (a + circumradius * cos (θ + 2 * π * ((4:ℕ):ℝ) / 5)) +
      n2 * (b + circumradius * sin (θ + 2 * π * ((4:ℕ):ℝ) / 5)) ≤ d
    rw [vx, vy, T4c, T4s, hc, hs]; exact h4

/-- The same, for the other side `d ≤ n·x`. -/
lemma pent_ge {a b θ c s n1 n2 d : ℝ} (hc : cos θ = c) (hs : sin θ = s)
    (h0 : d ≤ n1 * (a + (c * circumradius - s * 0)) + n2 * (b + (s * circumradius + c * 0)))
    (h1 : d ≤ n1 * (a + (c * (circumradius * 𝒞 - circumradius / 2) - s * 𝒞)) +
      n2 * (b + (s * (circumradius * 𝒞 - circumradius / 2) + c * 𝒞)))
    (h2 : d ≤ n1 * (a + (c * (-(circumradius * 𝒞)) - s * (1 / 2))) +
      n2 * (b + (s * (-(circumradius * 𝒞)) + c * (1 / 2))))
    (h3 : d ≤ n1 * (a + (c * (-(circumradius * 𝒞)) - s * (-1 / 2))) +
      n2 * (b + (s * (-(circumradius * 𝒞)) + c * (-1 / 2))))
    (h4 : d ≤ n1 * (a + (c * (circumradius * 𝒞 - circumradius / 2) - s * (-𝒞))) +
      n2 * (b + (s * (circumradius * 𝒞 - circumradius / 2) + c * (-𝒞)))) :
    pentagon a b θ ⊆ {x : ℝ × ℝ | d ≤ n1 * x.1 + n2 * x.2} := by
  apply hull_sub (convex_ge _ _ _)
  intro k hk
  interval_cases k
  · show d ≤ n1 * (a + circumradius * cos (θ + 2 * π * ((0:ℕ):ℝ) / 5)) +
      n2 * (b + circumradius * sin (θ + 2 * π * ((0:ℕ):ℝ) / 5))
    rw [vx, vy, T0c, T0s, hc, hs]; exact h0
  · show d ≤ n1 * (a + circumradius * cos (θ + 2 * π * ((1:ℕ):ℝ) / 5)) +
      n2 * (b + circumradius * sin (θ + 2 * π * ((1:ℕ):ℝ) / 5))
    rw [vx, vy, T1c, T1s, hc, hs]; exact h1
  · show d ≤ n1 * (a + circumradius * cos (θ + 2 * π * ((2:ℕ):ℝ) / 5)) +
      n2 * (b + circumradius * sin (θ + 2 * π * ((2:ℕ):ℝ) / 5))
    rw [vx, vy, T2c, T2s, hc, hs]; exact h2
  · show d ≤ n1 * (a + circumradius * cos (θ + 2 * π * ((3:ℕ):ℝ) / 5)) +
      n2 * (b + circumradius * sin (θ + 2 * π * ((3:ℕ):ℝ) / 5))
    rw [vx, vy, T3c, T3s, hc, hs]; exact h3
  · show d ≤ n1 * (a + circumradius * cos (θ + 2 * π * ((4:ℕ):ℝ) / 5)) +
      n2 * (b + circumradius * sin (θ + 2 * π * ((4:ℕ):ℝ) / 5))
    rw [vx, vy, T4c, T4s, hc, hs]; exact h4

lemma pent_abs_le_of_sq {x e : ℝ} (he : 0 ≤ e) (h : x ^ 2 ≤ e ^ 2) : -e ≤ x ∧ x ≤ e := by
  constructor <;> nlinarith

lemma proj_bound (n1 n2 e φ : ℝ) (he : 0 ≤ e)
    (hR : circumradius ^ 2 * (n1 ^ 2 + n2 ^ 2) ≤ e ^ 2) :
    -e ≤ circumradius * (n1 * cos φ + n2 * sin φ) ∧
      circumradius * (n1 * cos φ + n2 * sin φ) ≤ e := by
  have key : (n1 * cos φ + n2 * sin φ) ^ 2 + (n1 * sin φ - n2 * cos φ) ^ 2 =
      (n1 ^ 2 + n2 ^ 2) * (sin φ ^ 2 + cos φ ^ 2) := by ring
  rw [sin_sq_add_cos_sq, mul_one] at key
  have hu : (n1 * cos φ + n2 * sin φ) ^ 2 ≤ n1 ^ 2 + n2 ^ 2 := by
    nlinarith [sq_nonneg (n1 * sin φ - n2 * cos φ)]
  have h3 := mul_le_mul_of_nonneg_left hu (sq_nonneg circumradius)
  have h2 : (circumradius * (n1 * cos φ + n2 * sin φ)) ^ 2 ≤ e ^ 2 := by
    rw [mul_pow]; linarith
  exact pent_abs_le_of_sq he h2

/-- A pentagon lies within distance `R` of its centre along any direction. -/
lemma pent_far_le {a b θ n1 n2 e d : ℝ} (he : 0 ≤ e)
    (hR : circumradius ^ 2 * (n1 ^ 2 + n2 ^ 2) ≤ e ^ 2) (hd : n1 * a + n2 * b + e ≤ d) :
    pentagon a b θ ⊆ {x : ℝ × ℝ | n1 * x.1 + n2 * x.2 ≤ d} := by
  apply hull_sub (convex_le _ _ _)
  intro k _
  simp only [Set.mem_setOf_eq]
  have := (proj_bound n1 n2 e (θ + 2 * π * (k : ℝ) / 5) he hR).2
  nlinarith [this]

lemma pent_far_ge {a b θ n1 n2 e d : ℝ} (he : 0 ≤ e)
    (hR : circumradius ^ 2 * (n1 ^ 2 + n2 ^ 2) ≤ e ^ 2) (hd : d ≤ n1 * a + n2 * b - e) :
    pentagon a b θ ⊆ {x : ℝ × ℝ | d ≤ n1 * x.1 + n2 * x.2} := by
  apply hull_sub (convex_ge _ _ _)
  intro k _
  simp only [Set.mem_setOf_eq]
  have := (proj_bound n1 n2 e (θ + 2 * π * (k : ℝ) / 5) he hR).1
  nlinarith [this]

lemma box_of {P : Set (ℝ × ℝ)} {S : ℝ}
    (h1 : P ⊆ {x : ℝ × ℝ | (-1) * x.1 + 0 * x.2 ≤ 0})
    (h2 : P ⊆ {x : ℝ × ℝ | 1 * x.1 + 0 * x.2 ≤ S})
    (h3 : P ⊆ {x : ℝ × ℝ | 0 * x.1 + (-1) * x.2 ≤ 0})
    (h4 : P ⊆ {x : ℝ × ℝ | 0 * x.1 + 1 * x.2 ≤ S}) :
    P ⊆ Set.Icc 0 S ×ˢ Set.Icc 0 S := by
  intro p hp
  have a1 := h1 hp; have a2 := h2 hp; have a3 := h3 hp; have a4 := h4 hp
  simp only [Set.mem_setOf_eq] at a1 a2 a3 a4
  simp only [Set.mem_prod, Set.mem_Icc]
  exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩

lemma hc0 : cos (arccos (609321480728679 / 640678519271321 : ℝ)) = (609321480728679 / 640678519271321 : ℝ) :=
  Real.cos_arccos (by norm_num) (by norm_num)
lemma hs0 : sin (arccos (609321480728679 / 640678519271321 : ℝ)) = (197980550000000 / 640678519271321 : ℝ) := by
  rw [Real.sin_arccos, show (1:ℝ) - (609321480728679 / 640678519271321 : ℝ) ^ 2 = (197980550000000 / 640678519271321 : ℝ) ^ 2 by norm_num]
  exact Real.sqrt_sq (by norm_num)
lemma hc1 : cos (arccos (61206391959301831 / 63793608040698169 : ℝ)) = (61206391959301831 / 63793608040698169 : ℝ) :=
  Real.cos_arccos (by norm_num) (by norm_num)
lemma hs1 : sin (arccos (61206391959301831 / 63793608040698169 : ℝ)) = (17983381500000000 / 63793608040698169 : ℝ) := by
  rw [Real.sin_arccos, show (1:ℝ) - (61206391959301831 / 63793608040698169 : ℝ) ^ 2 = (17983381500000000 / 63793608040698169 : ℝ) ^ 2 by norm_num]
  exact Real.sqrt_sq (by norm_num)
lemma hc2 : cos (arccos (559705058434431 / 1393419941565569 : ℝ)) = (559705058434431 / 1393419941565569 : ℝ) :=
  Real.cos_arccos (by norm_num) (by norm_num)
lemma hs2 : sin (arccos (559705058434431 / 1393419941565569 : ℝ)) = (1276067937500000 / 1393419941565569 : ℝ) := by
  rw [Real.sin_arccos, show (1:ℝ) - (559705058434431 / 1393419941565569 : ℝ) ^ 2 = (1276067937500000 / 1393419941565569 : ℝ) ^ 2 by norm_num]
  exact Real.sqrt_sq (by norm_num)
lemma hc3 : cos (arccos (740383816821348399 / 1259616183178651601 : ℝ)) = (740383816821348399 / 1259616183178651601 : ℝ) :=
  Real.cos_arccos (by norm_num) (by norm_num)
lemma hs3 : sin (arccos (740383816821348399 / 1259616183178651601 : ℝ)) = (1019050898000000000 / 1259616183178651601 : ℝ) := by
  rw [Real.sin_arccos, show (1:ℝ) - (740383816821348399 / 1259616183178651601 : ℝ) ^ 2 = (1019050898000000000 / 1259616183178651601 : ℝ) ^ 2 by norm_num]
  exact Real.sqrt_sq (by norm_num)
lemma hc4 : cos (arccos (3493856215434639 / 4318643784565361 : ℝ)) = (3493856215434639 / 4318643784565361 : ℝ) :=
  Real.cos_arccos (by norm_num) (by norm_num)
lemma hs4 : sin (arccos (3493856215434639 / 4318643784565361 : ℝ)) = (2538435125000000 / 4318643784565361 : ℝ) := by
  rw [Real.sin_arccos, show (1:ℝ) - (3493856215434639 / 4318643784565361 : ℝ) ^ 2 = (2538435125000000 / 4318643784565361 : ℝ) ^ 2 by norm_num]
  exact Real.sqrt_sq (by norm_num)
lemma hc5 : cos (arccos (926604690537318031 / 1073395309462681969 : ℝ)) = (926604690537318031 / 1073395309462681969 : ℝ) :=
  Real.cos_arccos (by norm_num) (by norm_num)
lemma hs5 : sin (arccos (926604690537318031 / 1073395309462681969 : ℝ)) = (541831374000000000 / 1073395309462681969 : ℝ) := by
  rw [Real.sin_arccos, show (1:ℝ) - (926604690537318031 / 1073395309462681969 : ℝ) ^ 2 = (541831374000000000 / 1073395309462681969 : ℝ) ^ 2 by norm_num]
  exact Real.sqrt_sq (by norm_num)
lemma hc6 : cos (arccos (609321480728679 / 640678519271321 : ℝ)) = (609321480728679 / 640678519271321 : ℝ) :=
  Real.cos_arccos (by norm_num) (by norm_num)
lemma hs6 : sin (arccos (609321480728679 / 640678519271321 : ℝ)) = (197980550000000 / 640678519271321 : ℝ) := by
  rw [Real.sin_arccos, show (1:ℝ) - (609321480728679 / 640678519271321 : ℝ) ^ 2 = (197980550000000 / 640678519271321 : ℝ) ^ 2 by norm_num]
  exact Real.sqrt_sq (by norm_num)
lemma hc7 : cos (arccos (115267567140471 / 373013682859529 : ℝ)) = (115267567140471 / 373013682859529 : ℝ) :=
  Real.cos_arccos (by norm_num) (by norm_num)
lemma hs7 : sin (arccos (115267567140471 / 373013682859529 : ℝ)) = (354757093750000 / 373013682859529 : ℝ) := by
  rw [Real.sin_arccos, show (1:ℝ) - (115267567140471 / 373013682859529 : ℝ) ^ 2 = (354757093750000 / 373013682859529 : ℝ) ^ 2 by norm_num]
  exact Real.sqrt_sq (by norm_num)
lemma hc8 : cos (arccos (232693732679495631 / 267306267320504369 : ℝ)) = (232693732679495631 / 267306267320504369 : ℝ) :=
  Real.cos_arccos (by norm_num) (by norm_num)
lemma hs8 : sin (arccos (232693732679495631 / 267306267320504369 : ℝ)) = (131553287000000000 / 267306267320504369 : ℝ) := by
  rw [Real.sin_arccos, show (1:ℝ) - (232693732679495631 / 267306267320504369 : ℝ) ^ 2 = (131553287000000000 / 267306267320504369 : ℝ) ^ 2 by norm_num]
  exact Real.sqrt_sq (by norm_num)
lemma hc9 : cos (arccos (62499975254507751 / 62500024745492249 : ℝ)) = (62499975254507751 / 62500024745492249 : ℝ) :=
  Real.cos_arccos (by norm_num) (by norm_num)
lemma hs9 : sin (arccos (62499975254507751 / 62500024745492249 : ℝ)) = (78653500000000 / 62500024745492249 : ℝ) := by
  rw [Real.sin_arccos, show (1:ℝ) - (62499975254507751 / 62500024745492249 : ℝ) ^ 2 = (78653500000000 / 62500024745492249 : ℝ) ^ 2 by norm_num]
  exact Real.sqrt_sq (by norm_num)
lemma hc10 : cos (arccos (740383816821348399 / 1259616183178651601 : ℝ)) = (740383816821348399 / 1259616183178651601 : ℝ) :=
  Real.cos_arccos (by norm_num) (by norm_num)
lemma hs10 : sin (arccos (740383816821348399 / 1259616183178651601 : ℝ)) = (1019050898000000000 / 1259616183178651601 : ℝ) := by
  rw [Real.sin_arccos, show (1:ℝ) - (740383816821348399 / 1259616183178651601 : ℝ) ^ 2 = (1019050898000000000 / 1259616183178651601 : ℝ) ^ 2 by norm_num]
  exact Real.sqrt_sq (by norm_num)
lemma hc11 : cos (arccos (586557495560487399 / 1413442504439512601 : ℝ)) = (586557495560487399 / 1413442504439512601 : ℝ) :=
  Real.cos_arccos (by norm_num) (by norm_num)
lemma hs11 : sin (arccos (586557495560487399 / 1413442504439512601 : ℝ)) = (1285989898000000000 / 1413442504439512601 : ℝ) := by
  rw [Real.sin_arccos, show (1:ℝ) - (586557495560487399 / 1413442504439512601 : ℝ) ^ 2 = (1285989898000000000 / 1413442504439512601 : ℝ) ^ 2 by norm_num]
  exact Real.sqrt_sq (by norm_num)
lemma hc12 : cos (arccos (740383816821348399 / 1259616183178651601 : ℝ)) = (740383816821348399 / 1259616183178651601 : ℝ) :=
  Real.cos_arccos (by norm_num) (by norm_num)
lemma hs12 : sin (arccos (740383816821348399 / 1259616183178651601 : ℝ)) = (1019050898000000000 / 1259616183178651601 : ℝ) := by
  rw [Real.sin_arccos, show (1:ℝ) - (740383816821348399 / 1259616183178651601 : ℝ) ^ 2 = (1019050898000000000 / 1259616183178651601 : ℝ) ^ 2 by norm_num]
  exact Real.sqrt_sq (by norm_num)

lemma w0_0 : pentagon (623934821 / 250000000 : ℝ) (688191907 / 1000000000 : ℝ) (arccos (609321480728679 / 640678519271321 : ℝ)) ⊆ {x : ℝ × ℝ | (-1) * x.1 + 0 * x.2 ≤ 0} :=
  pent_far_le (e := (1701301617 / 2000000000 : ℝ)) (by norm_num) (by nlinarith [R_sq_le]) (by norm_num)
lemma w0_1 : pentagon (623934821 / 250000000 : ℝ) (688191907 / 1000000000 : ℝ) (arccos (609321480728679 / 640678519271321 : ℝ)) ⊆ {x : ℝ × ℝ | 1 * x.1 + 0 * x.2 ≤ (552103 / 100000 : ℝ)} :=
  pent_far_le (e := (1701301617 / 2000000000 : ℝ)) (by norm_num) (by nlinarith [R_sq_le]) (by norm_num)
lemma w0_2 : pentagon (623934821 / 250000000 : ℝ) (688191907 / 1000000000 : ℝ) (arccos (609321480728679 / 640678519271321 : ℝ)) ⊆ {x : ℝ × ℝ | 0 * x.1 + (-1) * x.2 ≤ 0} :=
  pent_le hc0 hs0 (by linarith [R_lo, R_hi, P_lo, P_hi, C_lo, C_hi]) (by linarith [R_lo, R_hi, P_lo, P_hi, C_lo, C_hi]) (by linarith [R_lo, R_hi, P_lo, P_hi, C_lo, C_hi]) (by linarith [R_lo, R_hi, P_lo, P_hi, C_lo, C_hi]) (by linarith [R_lo, R_hi, P_lo, P_hi, C_lo, C_hi])
lemma w0_3 : pentagon (623934821 / 250000000 : ℝ) (688191907 / 1000000000 : ℝ) (arccos (609321480728679 / 640678519271321 : ℝ)) ⊆ {x : ℝ × ℝ | 0 * x.1 + 1 * x.2 ≤ (552103 / 100000 : ℝ)} :=
  pent_far_le (e := (1701301617 / 2000000000 : ℝ)) (by norm_num) (by nlinarith [R_sq_le]) (by norm_num)
lemma box0 : pentagon (623934821 / 250000000 : ℝ) (688191907 / 1000000000 : ℝ) (arccos (609321480728679 / 640678519271321 : ℝ)) ⊆ Set.Icc 0 (552103 / 100000 : ℝ) ×ˢ Set.Icc 0 (552103 / 100000 : ℝ) :=
  box_of w0_0 w0_1 w0_2 w0_3
lemma w1_0 : pentagon (802776843 / 1000000000 : ℝ) (191580027 / 250000000 : ℝ) (arccos (61206391959301831 / 63793608040698169 : ℝ)) ⊆ {x : ℝ × ℝ | (-1) * x.1 + 0 * x.2 ≤ 0} :=
  pent_le hc1 hs1 (by linarith [R_lo, R_hi, P_lo, P_hi, C_lo, C_hi]) (by linarith [R_lo, R_hi, P_lo, P_hi, C_lo, C_hi]) (by linarith [R_lo, R_hi, P_lo, P_hi, C_lo, C_hi]) (by linarith [R_lo, R_hi, P_lo, P_hi, C_lo, C_hi]) (by linarith [R_lo, R_hi, P_lo, P_hi, C_lo, C_hi])
lemma w1_1 : pentagon (802776843 / 1000000000 : ℝ) (191580027 / 250000000 : ℝ) (arccos (61206391959301831 / 63793608040698169 : ℝ)) ⊆ {x : ℝ × ℝ | 1 * x.1 + 0 * x.2 ≤ (552103 / 100000 : ℝ)} :=
  pent_far_le (e := (1701301617 / 2000000000 : ℝ)) (by norm_num) (by nlinarith [R_sq_le]) (by norm_num)
lemma w1_2 : pentagon (802776843 / 1000000000 : ℝ) (191580027 / 250000000 : ℝ) (arccos (61206391959301831 / 63793608040698169 : ℝ)) ⊆ {x : ℝ × ℝ | 0 * x.1 + (-1) * x.2 ≤ 0} :=
  pent_le hc1 hs1 (by linarith [R_lo, R_hi, P_lo, P_hi, C_lo, C_hi]) (by linarith [R_lo, R_hi, P_lo, P_hi, C_lo, C_hi]) (by linarith [R_lo, R_hi, P_lo, P_hi, C_lo, C_hi]) (by linarith [R_lo, R_hi, P_lo, P_hi, C_lo, C_hi]) (by linarith [R_lo, R_hi, P_lo, P_hi, C_lo, C_hi])
lemma w1_3 : pentagon (802776843 / 1000000000 : ℝ) (191580027 / 250000000 : ℝ) (arccos (61206391959301831 / 63793608040698169 : ℝ)) ⊆ {x : ℝ × ℝ | 0 * x.1 + 1 * x.2 ≤ (552103 / 100000 : ℝ)} :=
  pent_far_le (e := (1701301617 / 2000000000 : ℝ)) (by norm_num) (by nlinarith [R_sq_le]) (by norm_num)
lemma box1 : pentagon (802776843 / 1000000000 : ℝ) (191580027 / 250000000 : ℝ) (arccos (61206391959301831 / 63793608040698169 : ℝ)) ⊆ Set.Icc 0 (552103 / 100000 : ℝ) ×ˢ Set.Icc 0 (552103 / 100000 : ℝ) :=
  box_of w1_0 w1_1 w1_2 w1_3
lemma w2_0 : pentagon (3431749619 / 1000000000 : ℝ) (3262254353 / 1000000000 : ℝ) (arccos (559705058434431 / 1393419941565569 : ℝ)) ⊆ {x : ℝ × ℝ | (-1) * x.1 + 0 * x.2 ≤ 0} :=
  pent_far_le (e := (1701301617 / 2000000000 : ℝ)) (by norm_num) (by nlinarith [R_sq_le]) (by norm_num)
lemma w2_1 : pentagon (3431749619 / 1000000000 : ℝ) (3262254353 / 1000000000 : ℝ) (arccos (559705058434431 / 1393419941565569 : ℝ)) ⊆ {x : ℝ × ℝ | 1 * x.1 + 0 * x.2 ≤ (552103 / 100000 : ℝ)} :=
  pent_far_le (e := (1701301617 / 2000000000 : ℝ)) (by norm_num) (by nlinarith [R_sq_le]) (by norm_num)
lemma w2_2 : pentagon (3431749619 / 1000000000 : ℝ) (3262254353 / 1000000000 : ℝ) (arccos (559705058434431 / 1393419941565569 : ℝ)) ⊆ {x : ℝ × ℝ | 0 * x.1 + (-1) * x.2 ≤ 0} :=
  pent_far_le (e := (1701301617 / 2000000000 : ℝ)) (by norm_num) (by nlinarith [R_sq_le]) (by norm_num)
lemma w2_3 : pentagon (3431749619 / 1000000000 : ℝ) (3262254353 / 1000000000 : ℝ) (arccos (559705058434431 / 1393419941565569 : ℝ)) ⊆ {x : ℝ × ℝ | 0 * x.1 + 1 * x.2 ≤ (552103 / 100000 : ℝ)} :=
  pent_far_le (e := (1701301617 / 2000000000 : ℝ)) (by norm_num) (by nlinarith [R_sq_le]) (by norm_num)
lemma box2 : pentagon (3431749619 / 1000000000 : ℝ) (3262254353 / 1000000000 : ℝ) (arccos (559705058434431 / 1393419941565569 : ℝ)) ⊆ Set.Icc 0 (552103 / 100000 : ℝ) ×ˢ Set.Icc 0 (552103 / 100000 : ℝ) :=
  box_of w2_0 w2_1 w2_2 w2_3
lemma w3_0 : pentagon (2362406791 / 1000000000 : ℝ) (4832838093 / 1000000000 : ℝ) (arccos (740383816821348399 / 1259616183178651601 : ℝ)) ⊆ {x : ℝ × ℝ | (-1) * x.1 + 0 * x.2 ≤ 0} :=
  pent_far_le (e := (1701301617 / 2000000000 : ℝ)) (by norm_num) (by nlinarith [R_sq_le]) (by norm_num)
lemma w3_1 : pentagon (2362406791 / 1000000000 : ℝ) (4832838093 / 1000000000 : ℝ) (arccos (740383816821348399 / 1259616183178651601 : ℝ)) ⊆ {x : ℝ × ℝ | 1 * x.1 + 0 * x.2 ≤ (552103 / 100000 : ℝ)} :=
  pent_far_le (e := (1701301617 / 2000000000 : ℝ)) (by norm_num) (by nlinarith [R_sq_le]) (by norm_num)
lemma w3_2 : pentagon (2362406791 / 1000000000 : ℝ) (4832838093 / 1000000000 : ℝ) (arccos (740383816821348399 / 1259616183178651601 : ℝ)) ⊆ {x : ℝ × ℝ | 0 * x.1 + (-1) * x.2 ≤ 0} :=
  pent_far_le (e := (1701301617 / 2000000000 : ℝ)) (by norm_num) (by nlinarith [R_sq_le]) (by norm_num)
lemma w3_3 : pentagon (2362406791 / 1000000000 : ℝ) (4832838093 / 1000000000 : ℝ) (arccos (740383816821348399 / 1259616183178651601 : ℝ)) ⊆ {x : ℝ × ℝ | 0 * x.1 + 1 * x.2 ≤ (552103 / 100000 : ℝ)} :=
  pent_le hc3 hs3 (by linarith [R_lo, R_hi, P_lo, P_hi, C_lo, C_hi]) (by linarith [R_lo, R_hi, P_lo, P_hi, C_lo, C_hi]) (by linarith [R_lo, R_hi, P_lo, P_hi, C_lo, C_hi]) (by linarith [R_lo, R_hi, P_lo, P_hi, C_lo, C_hi]) (by linarith [R_lo, R_hi, P_lo, P_hi, C_lo, C_hi])
lemma box3 : pentagon (2362406791 / 1000000000 : ℝ) (4832838093 / 1000000000 : ℝ) (arccos (740383816821348399 / 1259616183178651601 : ℝ)) ⊆ Set.Icc 0 (552103 / 100000 : ℝ) ×ˢ Set.Icc 0 (552103 / 100000 : ℝ) :=
  box_of w3_0 w3_1 w3_2 w3_3
lemma w4_0 : pentagon (4832838093 / 1000000000 : ℝ) (2133854777 / 1000000000 : ℝ) (arccos (3493856215434639 / 4318643784565361 : ℝ)) ⊆ {x : ℝ × ℝ | (-1) * x.1 + 0 * x.2 ≤ 0} :=
  pent_far_le (e := (1701301617 / 2000000000 : ℝ)) (by norm_num) (by nlinarith [R_sq_le]) (by norm_num)
lemma w4_1 : pentagon (4832838093 / 1000000000 : ℝ) (2133854777 / 1000000000 : ℝ) (arccos (3493856215434639 / 4318643784565361 : ℝ)) ⊆ {x : ℝ × ℝ | 1 * x.1 + 0 * x.2 ≤ (552103 / 100000 : ℝ)} :=
  pent_le hc4 hs4 (by linarith [R_lo, R_hi, P_lo, P_hi, C_lo, C_hi]) (by linarith [R_lo, R_hi, P_lo, P_hi, C_lo, C_hi]) (by linarith [R_lo, R_hi, P_lo, P_hi, C_lo, C_hi]) (by linarith [R_lo, R_hi, P_lo, P_hi, C_lo, C_hi]) (by linarith [R_lo, R_hi, P_lo, P_hi, C_lo, C_hi])
lemma w4_2 : pentagon (4832838093 / 1000000000 : ℝ) (2133854777 / 1000000000 : ℝ) (arccos (3493856215434639 / 4318643784565361 : ℝ)) ⊆ {x : ℝ × ℝ | 0 * x.1 + (-1) * x.2 ≤ 0} :=
  pent_far_le (e := (1701301617 / 2000000000 : ℝ)) (by norm_num) (by nlinarith [R_sq_le]) (by norm_num)
lemma w4_3 : pentagon (4832838093 / 1000000000 : ℝ) (2133854777 / 1000000000 : ℝ) (arccos (3493856215434639 / 4318643784565361 : ℝ)) ⊆ {x : ℝ × ℝ | 0 * x.1 + 1 * x.2 ≤ (552103 / 100000 : ℝ)} :=
  pent_far_le (e := (1701301617 / 2000000000 : ℝ)) (by norm_num) (by nlinarith [R_sq_le]) (by norm_num)
lemma box4 : pentagon (4832838093 / 1000000000 : ℝ) (2133854777 / 1000000000 : ℝ) (arccos (3493856215434639 / 4318643784565361 : ℝ)) ⊆ Set.Icc 0 (552103 / 100000 : ℝ) ×ˢ Set.Icc 0 (552103 / 100000 : ℝ) :=
  box_of w4_0 w4_1 w4_2 w4_3
lemma w5_0 : pentagon (2058684837 / 1000000000 : ℝ) (420490387 / 125000000 : ℝ) (arccos (926604690537318031 / 1073395309462681969 : ℝ)) ⊆ {x : ℝ × ℝ | (-1) * x.1 + 0 * x.2 ≤ 0} :=
  pent_far_le (e := (1701301617 / 2000000000 : ℝ)) (by norm_num) (by nlinarith [R_sq_le]) (by norm_num)
lemma w5_1 : pentagon (2058684837 / 1000000000 : ℝ) (420490387 / 125000000 : ℝ) (arccos (926604690537318031 / 1073395309462681969 : ℝ)) ⊆ {x : ℝ × ℝ | 1 * x.1 + 0 * x.2 ≤ (552103 / 100000 : ℝ)} :=
  pent_far_le (e := (1701301617 / 2000000000 : ℝ)) (by norm_num) (by nlinarith [R_sq_le]) (by norm_num)
lemma w5_2 : pentagon (2058684837 / 1000000000 : ℝ) (420490387 / 125000000 : ℝ) (arccos (926604690537318031 / 1073395309462681969 : ℝ)) ⊆ {x : ℝ × ℝ | 0 * x.1 + (-1) * x.2 ≤ 0} :=
  pent_far_le (e := (1701301617 / 2000000000 : ℝ)) (by norm_num) (by nlinarith [R_sq_le]) (by norm_num)
lemma w5_3 : pentagon (2058684837 / 1000000000 : ℝ) (420490387 / 125000000 : ℝ) (arccos (926604690537318031 / 1073395309462681969 : ℝ)) ⊆ {x : ℝ × ℝ | 0 * x.1 + 1 * x.2 ≤ (552103 / 100000 : ℝ)} :=
  pent_far_le (e := (1701301617 / 2000000000 : ℝ)) (by norm_num) (by nlinarith [R_sq_le]) (by norm_num)
lemma box5 : pentagon (2058684837 / 1000000000 : ℝ) (420490387 / 125000000 : ℝ) (arccos (926604690537318031 / 1073395309462681969 : ℝ)) ⊆ Set.Icc 0 (552103 / 100000 : ℝ) ×ˢ Set.Icc 0 (552103 / 100000 : ℝ) :=
  box_of w5_0 w5_1 w5_2 w5_3
lemma w6_0 : pentagon (427541651 / 100000000 : ℝ) (688191907 / 1000000000 : ℝ) (arccos (609321480728679 / 640678519271321 : ℝ)) ⊆ {x : ℝ × ℝ | (-1) * x.1 + 0 * x.2 ≤ 0} :=
  pent_far_le (e := (1701301617 / 2000000000 : ℝ)) (by norm_num) (by nlinarith [R_sq_le]) (by norm_num)
lemma w6_1 : pentagon (427541651 / 100000000 : ℝ) (688191907 / 1000000000 : ℝ) (arccos (609321480728679 / 640678519271321 : ℝ)) ⊆ {x : ℝ × ℝ | 1 * x.1 + 0 * x.2 ≤ (552103 / 100000 : ℝ)} :=
  pent_far_le (e := (1701301617 / 2000000000 : ℝ)) (by norm_num) (by nlinarith [R_sq_le]) (by norm_num)
lemma w6_2 : pentagon (427541651 / 100000000 : ℝ) (688191907 / 1000000000 : ℝ) (arccos (609321480728679 / 640678519271321 : ℝ)) ⊆ {x : ℝ × ℝ | 0 * x.1 + (-1) * x.2 ≤ 0} :=
  pent_le hc6 hs6 (by linarith [R_lo, R_hi, P_lo, P_hi, C_lo, C_hi]) (by linarith [R_lo, R_hi, P_lo, P_hi, C_lo, C_hi]) (by linarith [R_lo, R_hi, P_lo, P_hi, C_lo, C_hi]) (by linarith [R_lo, R_hi, P_lo, P_hi, C_lo, C_hi]) (by linarith [R_lo, R_hi, P_lo, P_hi, C_lo, C_hi])
lemma w6_3 : pentagon (427541651 / 100000000 : ℝ) (688191907 / 1000000000 : ℝ) (arccos (609321480728679 / 640678519271321 : ℝ)) ⊆ {x : ℝ × ℝ | 0 * x.1 + 1 * x.2 ≤ (552103 / 100000 : ℝ)} :=
  pent_far_le (e := (1701301617 / 2000000000 : ℝ)) (by norm_num) (by nlinarith [R_sq_le]) (by norm_num)
lemma box6 : pentagon (427541651 / 100000000 : ℝ) (688191907 / 1000000000 : ℝ) (arccos (609321480728679 / 640678519271321 : ℝ)) ⊆ Set.Icc 0 (552103 / 100000 : ℝ) ×ˢ Set.Icc 0 (552103 / 100000 : ℝ) :=
  box_of w6_0 w6_1 w6_2 w6_3
lemma w7_0 : pentagon (688191907 / 1000000000 : ℝ) (2889578283 / 1000000000 : ℝ) (arccos (115267567140471 / 373013682859529 : ℝ)) ⊆ {x : ℝ × ℝ | (-1) * x.1 + 0 * x.2 ≤ 0} :=
  pent_le hc7 hs7 (by linarith [R_lo, R_hi, P_lo, P_hi, C_lo, C_hi]) (by linarith [R_lo, R_hi, P_lo, P_hi, C_lo, C_hi]) (by linarith [R_lo, R_hi, P_lo, P_hi, C_lo, C_hi]) (by linarith [R_lo, R_hi, P_lo, P_hi, C_lo, C_hi]) (by linarith [R_lo, R_hi, P_lo, P_hi, C_lo, C_hi])
lemma w7_1 : pentagon (688191907 / 1000000000 : ℝ) (2889578283 / 1000000000 : ℝ) (arccos (115267567140471 / 373013682859529 : ℝ)) ⊆ {x : ℝ × ℝ | 1 * x.1 + 0 * x.2 ≤ (552103 / 100000 : ℝ)} :=
  pent_far_le (e := (1701301617 / 2000000000 : ℝ)) (by norm_num) (by nlinarith [R_sq_le]) (by norm_num)
lemma w7_2 : pentagon (688191907 / 1000000000 : ℝ) (2889578283 / 1000000000 : ℝ) (arccos (115267567140471 / 373013682859529 : ℝ)) ⊆ {x : ℝ × ℝ | 0 * x.1 + (-1) * x.2 ≤ 0} :=
  pent_far_le (e := (1701301617 / 2000000000 : ℝ)) (by norm_num) (by nlinarith [R_sq_le]) (by norm_num)
lemma w7_3 : pentagon (688191907 / 1000000000 : ℝ) (2889578283 / 1000000000 : ℝ) (arccos (115267567140471 / 373013682859529 : ℝ)) ⊆ {x : ℝ × ℝ | 0 * x.1 + 1 * x.2 ≤ (552103 / 100000 : ℝ)} :=
  pent_far_le (e := (1701301617 / 2000000000 : ℝ)) (by norm_num) (by nlinarith [R_sq_le]) (by norm_num)
lemma box7 : pentagon (688191907 / 1000000000 : ℝ) (2889578283 / 1000000000 : ℝ) (arccos (115267567140471 / 373013682859529 : ℝ)) ⊆ Set.Icc 0 (552103 / 100000 : ℝ) ×ˢ Set.Icc 0 (552103 / 100000 : ℝ) :=
  box_of w7_0 w7_1 w7_2 w7_3
lemma w8_0 : pentagon (478052591 / 100000000 : ℝ) (921971257 / 250000000 : ℝ) (arccos (232693732679495631 / 267306267320504369 : ℝ)) ⊆ {x : ℝ × ℝ | (-1) * x.1 + 0 * x.2 ≤ 0} :=
  pent_far_le (e := (1701301617 / 2000000000 : ℝ)) (by norm_num) (by nlinarith [R_sq_le]) (by norm_num)
lemma w8_1 : pentagon (478052591 / 100000000 : ℝ) (921971257 / 250000000 : ℝ) (arccos (232693732679495631 / 267306267320504369 : ℝ)) ⊆ {x : ℝ × ℝ | 1 * x.1 + 0 * x.2 ≤ (552103 / 100000 : ℝ)} :=
  pent_le hc8 hs8 (by linarith [R_lo, R_hi, P_lo, P_hi, C_lo, C_hi]) (by linarith [R_lo, R_hi, P_lo, P_hi, C_lo, C_hi]) (by linarith [R_lo, R_hi, P_lo, P_hi, C_lo, C_hi]) (by linarith [R_lo, R_hi, P_lo, P_hi, C_lo, C_hi]) (by linarith [R_lo, R_hi, P_lo, P_hi, C_lo, C_hi])
lemma w8_2 : pentagon (478052591 / 100000000 : ℝ) (921971257 / 250000000 : ℝ) (arccos (232693732679495631 / 267306267320504369 : ℝ)) ⊆ {x : ℝ × ℝ | 0 * x.1 + (-1) * x.2 ≤ 0} :=
  pent_far_le (e := (1701301617 / 2000000000 : ℝ)) (by norm_num) (by nlinarith [R_sq_le]) (by norm_num)
lemma w8_3 : pentagon (478052591 / 100000000 : ℝ) (921971257 / 250000000 : ℝ) (arccos (232693732679495631 / 267306267320504369 : ℝ)) ⊆ {x : ℝ × ℝ | 0 * x.1 + 1 * x.2 ≤ (552103 / 100000 : ℝ)} :=
  pent_far_le (e := (1701301617 / 2000000000 : ℝ)) (by norm_num) (by nlinarith [R_sq_le]) (by norm_num)
lemma box8 : pentagon (478052591 / 100000000 : ℝ) (921971257 / 250000000 : ℝ) (arccos (232693732679495631 / 267306267320504369 : ℝ)) ⊆ Set.Icc 0 (552103 / 100000 : ℝ) ×ˢ Set.Icc 0 (552103 / 100000 : ℝ) :=
  box_of w8_0 w8_1 w8_2 w8_3
lemma w9_0 : pentagon (346666363 / 500000000 : ℝ) (2330244233 / 500000000 : ℝ) (arccos (62499975254507751 / 62500024745492249 : ℝ)) ⊆ {x : ℝ × ℝ | (-1) * x.1 + 0 * x.2 ≤ 0} :=
  pent_le hc9 hs9 (by linarith [R_lo, R_hi, P_lo, P_hi, C_lo, C_hi]) (by linarith [R_lo, R_hi, P_lo, P_hi, C_lo, C_hi]) (by linarith [R_lo, R_hi, P_lo, P_hi, C_lo, C_hi]) (by linarith [R_lo, R_hi, P_lo, P_hi, C_lo, C_hi]) (by linarith [R_lo, R_hi, P_lo, P_hi, C_lo, C_hi])
lemma w9_1 : pentagon (346666363 / 500000000 : ℝ) (2330244233 / 500000000 : ℝ) (arccos (62499975254507751 / 62500024745492249 : ℝ)) ⊆ {x : ℝ × ℝ | 1 * x.1 + 0 * x.2 ≤ (552103 / 100000 : ℝ)} :=
  pent_far_le (e := (1701301617 / 2000000000 : ℝ)) (by norm_num) (by nlinarith [R_sq_le]) (by norm_num)
lemma w9_2 : pentagon (346666363 / 500000000 : ℝ) (2330244233 / 500000000 : ℝ) (arccos (62499975254507751 / 62500024745492249 : ℝ)) ⊆ {x : ℝ × ℝ | 0 * x.1 + (-1) * x.2 ≤ 0} :=
  pent_far_le (e := (1701301617 / 2000000000 : ℝ)) (by norm_num) (by nlinarith [R_sq_le]) (by norm_num)
lemma w9_3 : pentagon (346666363 / 500000000 : ℝ) (2330244233 / 500000000 : ℝ) (arccos (62499975254507751 / 62500024745492249 : ℝ)) ⊆ {x : ℝ × ℝ | 0 * x.1 + 1 * x.2 ≤ (552103 / 100000 : ℝ)} :=
  pent_far_le (e := (1701301617 / 2000000000 : ℝ)) (by norm_num) (by nlinarith [R_sq_le]) (by norm_num)
lemma box9 : pentagon (346666363 / 500000000 : ℝ) (2330244233 / 500000000 : ℝ) (arccos (62499975254507751 / 62500024745492249 : ℝ)) ⊆ Set.Icc 0 (552103 / 100000 : ℝ) ×ˢ Set.Icc 0 (552103 / 100000 : ℝ) :=
  box_of w9_0 w9_1 w9_2 w9_3
lemma w10_0 : pentagon (3634983 / 2000000 : ℝ) (948360003 / 500000000 : ℝ) (arccos (740383816821348399 / 1259616183178651601 : ℝ)) ⊆ {x : ℝ × ℝ | (-1) * x.1 + 0 * x.2 ≤ 0} :=
  pent_far_le (e := (1701301617 / 2000000000 : ℝ)) (by norm_num) (by nlinarith [R_sq_le]) (by norm_num)
lemma w10_1 : pentagon (3634983 / 2000000 : ℝ) (948360003 / 500000000 : ℝ) (arccos (740383816821348399 / 1259616183178651601 : ℝ)) ⊆ {x : ℝ × ℝ | 1 * x.1 + 0 * x.2 ≤ (552103 / 100000 : ℝ)} :=
  pent_far_le (e := (1701301617 / 2000000000 : ℝ)) (by norm_num) (by nlinarith [R_sq_le]) (by norm_num)
lemma w10_2 : pentagon (3634983 / 2000000 : ℝ) (948360003 / 500000000 : ℝ) (arccos (740383816821348399 / 1259616183178651601 : ℝ)) ⊆ {x : ℝ × ℝ | 0 * x.1 + (-1) * x.2 ≤ 0} :=
  pent_far_le (e := (1701301617 / 2000000000 : ℝ)) (by norm_num) (by nlinarith [R_sq_le]) (by norm_num)
lemma w10_3 : pentagon (3634983 / 2000000 : ℝ) (948360003 / 500000000 : ℝ) (arccos (740383816821348399 / 1259616183178651601 : ℝ)) ⊆ {x : ℝ × ℝ | 0 * x.1 + 1 * x.2 ≤ (552103 / 100000 : ℝ)} :=
  pent_far_le (e := (1701301617 / 2000000000 : ℝ)) (by norm_num) (by nlinarith [R_sq_le]) (by norm_num)
lemma box10 : pentagon (3634983 / 2000000 : ℝ) (948360003 / 500000000 : ℝ) (arccos (740383816821348399 / 1259616183178651601 : ℝ)) ⊆ Set.Icc 0 (552103 / 100000 : ℝ) ×ˢ Set.Icc 0 (552103 / 100000 : ℝ) :=
  box_of w10_0 w10_1 w10_2 w10_3
lemma w11_0 : pentagon (776866263 / 200000000 : ℝ) (1186770703 / 250000000 : ℝ) (arccos (586557495560487399 / 1413442504439512601 : ℝ)) ⊆ {x : ℝ × ℝ | (-1) * x.1 + 0 * x.2 ≤ 0} :=
  pent_far_le (e := (1701301617 / 2000000000 : ℝ)) (by norm_num) (by nlinarith [R_sq_le]) (by norm_num)
lemma w11_1 : pentagon (776866263 / 200000000 : ℝ) (1186770703 / 250000000 : ℝ) (arccos (586557495560487399 / 1413442504439512601 : ℝ)) ⊆ {x : ℝ × ℝ | 1 * x.1 + 0 * x.2 ≤ (552103 / 100000 : ℝ)} :=
  pent_far_le (e := (1701301617 / 2000000000 : ℝ)) (by norm_num) (by nlinarith [R_sq_le]) (by norm_num)
lemma w11_2 : pentagon (776866263 / 200000000 : ℝ) (1186770703 / 250000000 : ℝ) (arccos (586557495560487399 / 1413442504439512601 : ℝ)) ⊆ {x : ℝ × ℝ | 0 * x.1 + (-1) * x.2 ≤ 0} :=
  pent_far_le (e := (1701301617 / 2000000000 : ℝ)) (by norm_num) (by nlinarith [R_sq_le]) (by norm_num)
lemma w11_3 : pentagon (776866263 / 200000000 : ℝ) (1186770703 / 250000000 : ℝ) (arccos (586557495560487399 / 1413442504439512601 : ℝ)) ⊆ {x : ℝ × ℝ | 0 * x.1 + 1 * x.2 ≤ (552103 / 100000 : ℝ)} :=
  pent_le hc11 hs11 (by linarith [R_lo, R_hi, P_lo, P_hi, C_lo, C_hi]) (by linarith [R_lo, R_hi, P_lo, P_hi, C_lo, C_hi]) (by linarith [R_lo, R_hi, P_lo, P_hi, C_lo, C_hi]) (by linarith [R_lo, R_hi, P_lo, P_hi, C_lo, C_hi]) (by linarith [R_lo, R_hi, P_lo, P_hi, C_lo, C_hi])
lemma box11 : pentagon (776866263 / 200000000 : ℝ) (1186770703 / 250000000 : ℝ) (arccos (586557495560487399 / 1413442504439512601 : ℝ)) ⊆ Set.Icc 0 (552103 / 100000 : ℝ) ×ˢ Set.Icc 0 (552103 / 100000 : ℝ) :=
  box_of w11_0 w11_1 w11_2 w11_3
lemma w12_0 : pentagon (3385577897 / 1000000000 : ℝ) (174299027 / 100000000 : ℝ) (arccos (740383816821348399 / 1259616183178651601 : ℝ)) ⊆ {x : ℝ × ℝ | (-1) * x.1 + 0 * x.2 ≤ 0} :=
  pent_far_le (e := (1701301617 / 2000000000 : ℝ)) (by norm_num) (by nlinarith [R_sq_le]) (by norm_num)
lemma w12_1 : pentagon (3385577897 / 1000000000 : ℝ) (174299027 / 100000000 : ℝ) (arccos (740383816821348399 / 1259616183178651601 : ℝ)) ⊆ {x : ℝ × ℝ | 1 * x.1 + 0 * x.2 ≤ (552103 / 100000 : ℝ)} :=
  pent_far_le (e := (1701301617 / 2000000000 : ℝ)) (by norm_num) (by nlinarith [R_sq_le]) (by norm_num)
lemma w12_2 : pentagon (3385577897 / 1000000000 : ℝ) (174299027 / 100000000 : ℝ) (arccos (740383816821348399 / 1259616183178651601 : ℝ)) ⊆ {x : ℝ × ℝ | 0 * x.1 + (-1) * x.2 ≤ 0} :=
  pent_far_le (e := (1701301617 / 2000000000 : ℝ)) (by norm_num) (by nlinarith [R_sq_le]) (by norm_num)
lemma w12_3 : pentagon (3385577897 / 1000000000 : ℝ) (174299027 / 100000000 : ℝ) (arccos (740383816821348399 / 1259616183178651601 : ℝ)) ⊆ {x : ℝ × ℝ | 0 * x.1 + 1 * x.2 ≤ (552103 / 100000 : ℝ)} :=
  pent_far_le (e := (1701301617 / 2000000000 : ℝ)) (by norm_num) (by nlinarith [R_sq_le]) (by norm_num)
lemma box12 : pentagon (3385577897 / 1000000000 : ℝ) (174299027 / 100000000 : ℝ) (arccos (740383816821348399 / 1259616183178651601 : ℝ)) ⊆ Set.Icc 0 (552103 / 100000 : ℝ) ×ˢ Set.Icc 0 (552103 / 100000 : ℝ) :=
  box_of w12_0 w12_1 w12_2 w12_3

lemma d0_1 : Disjoint (interior (pentagon (623934821 / 250000000 : ℝ) (688191907 / 1000000000 : ℝ) (arccos (609321480728679 / 640678519271321 : ℝ)))) (interior (pentagon (802776843 / 1000000000 : ℝ) (191580027 / 250000000 : ℝ) (arccos (61206391959301831 / 63793608040698169 : ℝ)))) := by
  exact halfplane_disjoint (-188380559 / 200000000 : ℝ) (20992849 / 62500000 : ℝ) (-61405369583 / 50000000000 : ℝ) (by norm_num)
    (pent_le hc0 hs0 (by linarith [R_lo, R_hi, P_lo, P_hi, C_lo, C_hi]) (by linarith [R_lo, R_hi, P_lo, P_hi, C_lo, C_hi]) (by linarith [R_lo, R_hi, P_lo, P_hi, C_lo, C_hi]) (by linarith [R_lo, R_hi, P_lo, P_hi, C_lo, C_hi]) (by linarith [R_lo, R_hi, P_lo, P_hi, C_lo, C_hi]))
    (pent_ge hc1 hs1 (by linarith [R_lo, R_hi, P_lo, P_hi, C_lo, C_hi]) (by linarith [R_lo, R_hi, P_lo, P_hi, C_lo, C_hi]) (by linarith [R_lo, R_hi, P_lo, P_hi, C_lo, C_hi]) (by linarith [R_lo, R_hi, P_lo, P_hi, C_lo, C_hi]) (by linarith [R_lo, R_hi, P_lo, P_hi, C_lo, C_hi]))
lemma d0_2 : Disjoint (interior (pentagon (623934821 / 250000000 : ℝ) (688191907 / 1000000000 : ℝ) (arccos (609321480728679 / 640678519271321 : ℝ)))) (interior (pentagon (3431749619 / 1000000000 : ℝ) (3262254353 / 1000000000 : ℝ) (arccos (559705058434431 / 1393419941565569 : ℝ)))) := by
  have hR : circumradius ^ 2 * ((187202067 / 200000000 : ℝ) ^ 2 + (1287031223 / 500000000 : ℝ) ^ 2) ≤ (7501912823134315141 / 2000000000000000000 : ℝ) ^ 2 := by nlinarith [R_sq_le]
  exact halfplane_disjoint (187202067 / 200000000 : ℝ) (1287031223 / 500000000 : ℝ) (3143377247322592893 / 400000000000000000 : ℝ) (by norm_num)
    (pent_far_le (e := (7501912823134315141 / 2000000000000000000 : ℝ)) (by norm_num) hR (by norm_num))
    (pent_far_ge (e := (7501912823134315141 / 2000000000000000000 : ℝ)) (by norm_num) hR (by norm_num))
lemma d0_3 : Disjoint (interior (pentagon (623934821 / 250000000 : ℝ) (688191907 / 1000000000 : ℝ) (arccos (609321480728679 / 640678519271321 : ℝ)))) (interior (pentagon (2362406791 / 1000000000 : ℝ) (4832838093 / 1000000000 : ℝ) (arccos (740383816821348399 / 1259616183178651601 : ℝ)))) := by
  have hR : circumradius ^ 2 * ((-133332493 / 1000000000 : ℝ) ^ 2 + (2072323093 / 500000000 : ℝ) ^ 2) ≤ (3439173912162788329 / 400000000000000000 : ℝ) ^ 2 := by nlinarith [R_sq_le]
  exact halfplane_disjoint (-133332493 / 1000000000 : ℝ) (2072323093 / 500000000 : ℝ) (889398688190146601 / 80000000000000000 : ℝ) (by norm_num)
    (pent_far_le (e := (3439173912162788329 / 400000000000000000 : ℝ)) (by norm_num) hR (by norm_num))
    (pent_far_ge (e := (3439173912162788329 / 400000000000000000 : ℝ)) (by norm_num) hR (by norm_num))
lemma d0_4 : Disjoint (interior (pentagon (623934821 / 250000000 : ℝ) (688191907 / 1000000000 : ℝ) (arccos (609321480728679 / 640678519271321 : ℝ)))) (interior (pentagon (4832838093 / 1000000000 : ℝ) (2133854777 / 1000000000 : ℝ) (arccos (3493856215434639 / 4318643784565361 : ℝ)))) := by
  have hR : circumradius ^ 2 * ((2337098809 / 1000000000 : ℝ) ^ 2 + (144566287 / 100000000 : ℝ) ^ 2) ≤ (7551971976725855381 / 2000000000000000000 : ℝ) ^ 2 := by nlinarith [R_sq_le]
  exact halfplane_disjoint (2337098809 / 1000000000 : ℝ) (144566287 / 100000000 : ℝ) (21207337567916467073 / 2000000000000000000 : ℝ) (by norm_num)
    (pent_far_le (e := (7551971976725855381 / 2000000000000000000 : ℝ)) (by norm_num) hR (by norm_num))
    (pent_far_ge (e := (7551971976725855381 / 2000000000000000000 : ℝ)) (by norm_num) hR (by norm_num))
lemma d0_5 : Disjoint (interior (pentagon (623934821 / 250000000 : ℝ) (688191907 / 1000000000 : ℝ) (arccos (609321480728679 / 640678519271321 : ℝ)))) (interior (pentagon (2058684837 / 1000000000 : ℝ) (420490387 / 125000000 : ℝ) (arccos (926604690537318031 / 1073395309462681969 : ℝ)))) := by
  have hR : circumradius ^ 2 * ((-437054447 / 1000000000 : ℝ) ^ 2 + (2675731189 / 1000000000 : ℝ) ^ 2) ≤ (735055398542982953 / 200000000000000000 : ℝ) ^ 2 := by nlinarith [R_sq_le]
  exact halfplane_disjoint (-437054447 / 1000000000 : ℝ) (2675731189 / 1000000000 : ℝ) (27661997435421289 / 6250000000000000 : ℝ) (by norm_num)
    (pent_far_le (e := (735055398542982953 / 200000000000000000 : ℝ)) (by norm_num) hR (by norm_num))
    (pent_far_ge (e := (735055398542982953 / 200000000000000000 : ℝ)) (by norm_num) hR (by norm_num))
lemma d0_6 : Disjoint (interior (pentagon (623934821 / 250000000 : ℝ) (688191907 / 1000000000 : ℝ) (arccos (609321480728679 / 640678519271321 : ℝ)))) (interior (pentagon (427541651 / 100000000 : ℝ) (688191907 / 1000000000 : ℝ) (arccos (609321480728679 / 640678519271321 : ℝ)))) := by
  have hR : circumradius ^ 2 * ((889838613 / 500000000 : ℝ) ^ 2 + (0 : ℝ) ^ 2) ≤ (791812757185763769 / 500000000000000000 : ℝ) ^ 2 := by nlinarith [R_sq_le]
  exact halfplane_disjoint (889838613 / 500000000 : ℝ) (0 : ℝ) (3012617940069936861 / 500000000000000000 : ℝ) (by norm_num)
    (pent_far_le (e := (791812757185763769 / 500000000000000000 : ℝ)) (by norm_num) hR (by norm_num))
    (pent_far_ge (e := (791812757185763769 / 500000000000000000 : ℝ)) (by norm_num) hR (by norm_num))
lemma d0_7 : Disjoint (interior (pentagon (623934821 / 250000000 : ℝ) (688191907 / 1000000000 : ℝ) (arccos (609321480728679 / 640678519271321 : ℝ)))) (interior (pentagon (688191907 / 1000000000 : ℝ) (2889578283 / 1000000000 : ℝ) (arccos (115267567140471 / 373013682859529 : ℝ)))) := by
  have hR : circumradius ^ 2 * ((-1807547377 / 1000000000 : ℝ) ^ 2 + (275173297 / 125000000 : ℝ) ^ 2) ≤ (1622665899307598701 / 400000000000000000 : ℝ) ^ 2 := by nlinarith [R_sq_le]
  exact halfplane_disjoint (-1807547377 / 1000000000 : ℝ) (275173297 / 125000000 : ℝ) (2120948079884395433 / 2000000000000000000 : ℝ) (by norm_num)
    (pent_far_le (e := (1622665899307598701 / 400000000000000000 : ℝ)) (by norm_num) hR (by norm_num))
    (pent_far_ge (e := (1622665899307598701 / 400000000000000000 : ℝ)) (by norm_num) hR (by norm_num))
lemma d0_8 : Disjoint (interior (pentagon (623934821 / 250000000 : ℝ) (688191907 / 1000000000 : ℝ) (arccos (609321480728679 / 640678519271321 : ℝ)))) (interior (pentagon (478052591 / 100000000 : ℝ) (921971257 / 250000000 : ℝ) (arccos (232693732679495631 / 267306267320504369 : ℝ)))) := by
  have hR : circumradius ^ 2 * ((1142393313 / 500000000 : ℝ) ^ 2 + (2999693121 / 1000000000 : ℝ) ^ 2) ≤ (14218408746523184517 / 2000000000000000000 : ℝ) ^ 2 := by nlinarith [R_sq_le]
  exact halfplane_disjoint (1142393313 / 500000000 : ℝ) (2999693121 / 1000000000 : ℝ) (29751601281366759579 / 2000000000000000000 : ℝ) (by norm_num)
    (pent_far_le (e := (14218408746523184517 / 2000000000000000000 : ℝ)) (by norm_num) hR (by norm_num))
    (pent_far_ge (e := (14218408746523184517 / 2000000000000000000 : ℝ)) (by norm_num) hR (by norm_num))
lemma d0_9 : Disjoint (interior (pentagon (623934821 / 250000000 : ℝ) (688191907 / 1000000000 : ℝ) (arccos (609321480728679 / 640678519271321 : ℝ)))) (interior (pentagon (346666363 / 500000000 : ℝ) (2330244233 / 500000000 : ℝ) (arccos (62499975254507751 / 62500024745492249 : ℝ)))) := by
  have hR : circumradius ^ 2 * ((-901203279 / 500000000 : ℝ) ^ 2 + (3972296559 / 1000000000 : ℝ) ^ 2) ≤ (3805561870592929569 / 400000000000000000 : ℝ) ^ 2 := by nlinarith [R_sq_le]
  exact halfplane_disjoint (-901203279 / 500000000 : ℝ) (3972296559 / 1000000000 : ℝ) (15498540336100494927 / 2000000000000000000 : ℝ) (by norm_num)
    (pent_far_le (e := (3805561870592929569 / 400000000000000000 : ℝ)) (by norm_num) hR (by norm_num))
    (pent_far_ge (e := (3805561870592929569 / 400000000000000000 : ℝ)) (by norm_num) hR (by norm_num))
lemma d0_10 : Disjoint (interior (pentagon (623934821 / 250000000 : ℝ) (688191907 / 1000000000 : ℝ) (arccos (609321480728679 / 640678519271321 : ℝ)))) (interior (pentagon (3634983 / 2000000 : ℝ) (948360003 / 500000000 : ℝ) (arccos (740383816821348399 / 1259616183178651601 : ℝ)))) := by
  exact halfplane_disjoint (-146946313 / 250000000 : ℝ) (161803399 / 200000000 : ℝ) (-222007887609 / 1000000000000 : ℝ) (by norm_num)
    (pent_le hc0 hs0 (by linarith [R_lo, R_hi, P_lo, P_hi, C_lo, C_hi]) (by linarith [R_lo, R_hi, P_lo, P_hi, C_lo, C_hi]) (by linarith [R_lo, R_hi, P_lo, P_hi, C_lo, C_hi]) (by linarith [R_lo, R_hi, P_lo, P_hi, C_lo, C_hi]) (by linarith [R_lo, R_hi, P_lo, P_hi, C_lo, C_hi]))
    (pent_ge hc10 hs10 (by linarith [R_lo, R_hi, P_lo, P_hi, C_lo, C_hi]) (by linarith [R_lo, R_hi, P_lo, P_hi, C_lo, C_hi]) (by linarith [R_lo, R_hi, P_lo, P_hi, C_lo, C_hi]) (by linarith [R_lo, R_hi, P_lo, P_hi, C_lo, C_hi]) (by linarith [R_lo, R_hi, P_lo, P_hi, C_lo, C_hi]))
lemma d0_11 : Disjoint (interior (pentagon (623934821 / 250000000 : ℝ) (688191907 / 1000000000 : ℝ) (arccos (609321480728679 / 640678519271321 : ℝ)))) (interior (pentagon (776866263 / 200000000 : ℝ) (1186770703 / 250000000 : ℝ) (arccos (586557495560487399 / 1413442504439512601 : ℝ)))) := by
  have hR : circumradius ^ 2 * ((1388592031 / 1000000000 : ℝ) ^ 2 + (811778181 / 200000000 : ℝ) ^ 2) ≤ (9201391603624211993 / 1000000000000000000 : ℝ) ^ 2 := by nlinarith [R_sq_le]
  exact halfplane_disjoint (1388592031 / 1000000000 : ℝ) (811778181 / 200000000 : ℝ) (966265697316072727 / 62500000000000000 : ℝ) (by norm_num)
    (pent_far_le (e := (9201391603624211993 / 1000000000000000000 : ℝ)) (by norm_num) hR (by norm_num))
    (pent_far_ge (e := (9201391603624211993 / 1000000000000000000 : ℝ)) (by norm_num) hR (by norm_num))
lemma d0_12 : Disjoint (interior (pentagon (623934821 / 250000000 : ℝ) (688191907 / 1000000000 : ℝ) (arccos (609321480728679 / 640678519271321 : ℝ)))) (interior (pentagon (3385577897 / 1000000000 : ℝ) (174299027 / 100000000 : ℝ) (arccos (740383816821348399 / 1259616183178651601 : ℝ)))) := by
  exact halfplane_disjoint (587785253 / 1000000000 : ℝ) (404508497 / 500000000 : ℝ) (2711909601971 / 1000000000000 : ℝ) (by norm_num)
    (pent_le hc0 hs0 (by linarith [R_lo, R_hi, P_lo, P_hi, C_lo, C_hi]) (by linarith [R_lo, R_hi, P_lo, P_hi, C_lo, C_hi]) (by linarith [R_lo, R_hi, P_lo, P_hi, C_lo, C_hi]) (by linarith [R_lo, R_hi, P_lo, P_hi, C_lo, C_hi]) (by linarith [R_lo, R_hi, P_lo, P_hi, C_lo, C_hi]))
    (pent_ge hc12 hs12 (by linarith [R_lo, R_hi, P_lo, P_hi, C_lo, C_hi]) (by linarith [R_lo, R_hi, P_lo, P_hi, C_lo, C_hi]) (by linarith [R_lo, R_hi, P_lo, P_hi, C_lo, C_hi]) (by linarith [R_lo, R_hi, P_lo, P_hi, C_lo, C_hi]) (by linarith [R_lo, R_hi, P_lo, P_hi, C_lo, C_hi]))
lemma d1_2 : Disjoint (interior (pentagon (802776843 / 1000000000 : ℝ) (191580027 / 250000000 : ℝ) (arccos (61206391959301831 / 63793608040698169 : ℝ)))) (interior (pentagon (3431749619 / 1000000000 : ℝ) (3262254353 / 1000000000 : ℝ) (arccos (559705058434431 / 1393419941565569 : ℝ)))) := by
  have hR : circumradius ^ 2 * ((328621597 / 125000000 : ℝ) ^ 2 + (499186849 / 200000000 : ℝ) ^ 2) ≤ (13141185612312866201 / 2000000000000000000 : ℝ) ^ 2 := by nlinarith [R_sq_le]
  exact halfplane_disjoint (328621597 / 125000000 : ℝ) (499186849 / 200000000 : ℝ) (21187511743591915457 / 2000000000000000000 : ℝ) (by norm_num)
    (pent_far_le (e := (13141185612312866201 / 2000000000000000000 : ℝ)) (by norm_num) hR (by norm_num))
    (pent_far_ge (e := (13141185612312866201 / 2000000000000000000 : ℝ)) (by norm_num) hR (by norm_num))
lemma d1_3 : Disjoint (interior (pentagon (802776843 / 1000000000 : ℝ) (191580027 / 250000000 : ℝ) (arccos (61206391959301831 / 63793608040698169 : ℝ)))) (interior (pentagon (2362406791 / 1000000000 : ℝ) (4832838093 / 1000000000 : ℝ) (arccos (740383816821348399 / 1259616183178651601 : ℝ)))) := by
  have hR : circumradius ^ 2 * ((389907487 / 250000000 : ℝ) ^ 2 + (813303597 / 200000000 : ℝ) ^ 2) ≤ (18969014097026942929 / 2000000000000000000 : ℝ) ^ 2 := by nlinarith [R_sq_le]
  exact halfplane_disjoint (389907487 / 250000000 : ℝ) (813303597 / 200000000 : ℝ) (27705592711732616017 / 2000000000000000000 : ℝ) (by norm_num)
    (pent_far_le (e := (18969014097026942929 / 2000000000000000000 : ℝ)) (by norm_num) hR (by norm_num))
    (pent_far_ge (e := (18969014097026942929 / 2000000000000000000 : ℝ)) (by norm_num) hR (by norm_num))
lemma d1_4 : Disjoint (interior (pentagon (802776843 / 1000000000 : ℝ) (191580027 / 250000000 : ℝ) (arccos (61206391959301831 / 63793608040698169 : ℝ)))) (interior (pentagon (4832838093 / 1000000000 : ℝ) (2133854777 / 1000000000 : ℝ) (arccos (3493856215434639 / 4318643784565361 : ℝ)))) := by
  have hR : circumradius ^ 2 * ((3224049 / 800000 : ℝ) ^ 2 + (1367534669 / 1000000000 : ℝ) ^ 2) ≤ (18111544749668502061 / 2000000000000000000 : ℝ) ^ 2 := by nlinarith [R_sq_le]
  exact halfplane_disjoint (3224049 / 800000 : ℝ) (1367534669 / 1000000000 : ℝ) (5335592614979083613 / 400000000000000000 : ℝ) (by norm_num)
    (pent_far_le (e := (18111544749668502061 / 2000000000000000000 : ℝ)) (by norm_num) hR (by norm_num))
    (pent_far_ge (e := (18111544749668502061 / 2000000000000000000 : ℝ)) (by norm_num) hR (by norm_num))
lemma d1_5 : Disjoint (interior (pentagon (802776843 / 1000000000 : ℝ) (191580027 / 250000000 : ℝ) (arccos (61206391959301831 / 63793608040698169 : ℝ)))) (interior (pentagon (2058684837 / 1000000000 : ℝ) (420490387 / 125000000 : ℝ) (arccos (926604690537318031 / 1073395309462681969 : ℝ)))) := by
  have hR : circumradius ^ 2 * ((627953997 / 500000000 : ℝ) ^ 2 + (649400747 / 250000000 : ℝ) ^ 2) ≤ (416242308632981609 / 100000000000000000 : ℝ) ^ 2 := by nlinarith [R_sq_le]
  exact halfplane_disjoint (627953997 / 500000000 : ℝ) (649400747 / 250000000 : ℝ) (895154042894610217 / 125000000000000000 : ℝ) (by norm_num)
    (pent_far_le (e := (416242308632981609 / 100000000000000000 : ℝ)) (by norm_num) hR (by norm_num))
    (pent_far_ge (e := (416242308632981609 / 100000000000000000 : ℝ)) (by norm_num) hR (by norm_num))
lemma d1_6 : Disjoint (interior (pentagon (802776843 / 1000000000 : ℝ) (191580027 / 250000000 : ℝ) (arccos (61206391959301831 / 63793608040698169 : ℝ)))) (interior (pentagon (427541651 / 100000000 : ℝ) (688191907 / 1000000000 : ℝ) (arccos (609321480728679 / 640678519271321 : ℝ)))) := by
  have hR : circumradius ^ 2 * ((3472639667 / 1000000000 : ℝ) ^ 2 + (-78128201 / 1000000000 : ℝ) ^ 2) ≤ (1206533027261336729 / 200000000000000000 : ℝ) ^ 2 := by nlinarith [R_sq_le]
  exact halfplane_disjoint (3472639667 / 1000000000 : ℝ) (-78128201 / 1000000000 : ℝ) (4380274316814674609 / 500000000000000000 : ℝ) (by norm_num)
    (pent_far_le (e := (1206533027261336729 / 200000000000000000 : ℝ)) (by norm_num) hR (by norm_num))
    (pent_far_ge (e := (1206533027261336729 / 200000000000000000 : ℝ)) (by norm_num) hR (by norm_num))
lemma d1_7 : Disjoint (interior (pentagon (802776843 / 1000000000 : ℝ) (191580027 / 250000000 : ℝ) (arccos (61206391959301831 / 63793608040698169 : ℝ)))) (interior (pentagon (688191907 / 1000000000 : ℝ) (2889578283 / 1000000000 : ℝ) (arccos (115267567140471 / 373013682859529 : ℝ)))) := by
  have hR : circumradius ^ 2 * ((-14323117 / 125000000 : ℝ) ^ 2 + (84930327 / 40000000 : ℝ) ^ 2) ≤ (4521354985262454721 / 2000000000000000000 : ℝ) ^ 2 := by nlinarith [R_sq_le]
  exact halfplane_disjoint (-14323117 / 125000000 : ℝ) (84930327 / 40000000 : ℝ) (303662943474533857 / 80000000000000000 : ℝ) (by norm_num)
    (pent_far_le (e := (4521354985262454721 / 2000000000000000000 : ℝ)) (by norm_num) hR (by norm_num))
    (pent_far_ge (e := (4521354985262454721 / 2000000000000000000 : ℝ)) (by norm_num) hR (by norm_num))
lemma d1_8 : Disjoint (interior (pentagon (802776843 / 1000000000 : ℝ) (191580027 / 250000000 : ℝ) (arccos (61206391959301831 / 63793608040698169 : ℝ)))) (interior (pentagon (478052591 / 100000000 : ℝ) (921971257 / 250000000 : ℝ) (arccos (232693732679495631 / 267306267320504369 : ℝ)))) := by
  have hR : circumradius ^ 2 * ((3977749067 / 1000000000 : ℝ) ^ 2 + (73039123 / 25000000 : ℝ) ^ 2) ≤ (24358029221793976889 / 2000000000000000000 : ℝ) ^ 2 := by nlinarith [R_sq_le]
  exact halfplane_disjoint (3977749067 / 1000000000 : ℝ) (73039123 / 25000000 : ℝ) (35222226788345710571 / 2000000000000000000 : ℝ) (by norm_num)
    (pent_far_le (e := (24358029221793976889 / 2000000000000000000 : ℝ)) (by norm_num) hR (by norm_num))
    (pent_far_ge (e := (24358029221793976889 / 2000000000000000000 : ℝ)) (by norm_num) hR (by norm_num))
lemma d1_9 : Disjoint (interior (pentagon (802776843 / 1000000000 : ℝ) (191580027 / 250000000 : ℝ) (arccos (61206391959301831 / 63793608040698169 : ℝ)))) (interior (pentagon (346666363 / 500000000 : ℝ) (2330244233 / 500000000 : ℝ) (arccos (62499975254507751 / 62500024745492249 : ℝ)))) := by
  have hR : circumradius ^ 2 * ((-109444117 / 1000000000 : ℝ) ^ 2 + (1947084179 / 500000000 : ℝ) ^ 2) ≤ (15176525215194325853 / 2000000000000000000 : ℝ) ^ 2 := by nlinarith [R_sq_le]
  exact halfplane_disjoint (-109444117 / 1000000000 : ℝ) (1947084179 / 500000000 : ℝ) (20969165843079445919 / 2000000000000000000 : ℝ) (by norm_num)
    (pent_far_le (e := (15176525215194325853 / 2000000000000000000 : ℝ)) (by norm_num) hR (by norm_num))
    (pent_far_ge (e := (15176525215194325853 / 2000000000000000000 : ℝ)) (by norm_num) hR (by norm_num))
lemma d1_10 : Disjoint (interior (pentagon (802776843 / 1000000000 : ℝ) (191580027 / 250000000 : ℝ) (arccos (61206391959301831 / 63793608040698169 : ℝ)))) (interior (pentagon (3634983 / 2000000 : ℝ) (948360003 / 500000000 : ℝ) (arccos (740383816821348399 / 1259616183178651601 : ℝ)))) := by
  exact halfplane_disjoint (9539221 / 15625000 : ℝ) (792008437 / 1000000000 : ℝ) (1847468391301 / 1000000000000 : ℝ) (by norm_num)
    (pent_le hc1 hs1 (by linarith [R_lo, R_hi, P_lo, P_hi, C_lo, C_hi]) (by linarith [R_lo, R_hi, P_lo, P_hi, C_lo, C_hi]) (by linarith [R_lo, R_hi, P_lo, P_hi, C_lo, C_hi]) (by linarith [R_lo, R_hi, P_lo, P_hi, C_lo, C_hi]) (by linarith [R_lo, R_hi, P_lo, P_hi, C_lo, C_hi]))
    (pent_ge hc10 hs10 (by linarith [R_lo, R_hi, P_lo, P_hi, C_lo, C_hi]) (by linarith [R_lo, R_hi, P_lo, P_hi, C_lo, C_hi]) (by linarith [R_lo, R_hi, P_lo, P_hi, C_lo, C_hi]) (by linarith [R_lo, R_hi, P_lo, P_hi, C_lo, C_hi]) (by linarith [R_lo, R_hi, P_lo, P_hi, C_lo, C_hi]))
lemma d1_11 : Disjoint (interior (pentagon (802776843 / 1000000000 : ℝ) (191580027 / 250000000 : ℝ) (arccos (61206391959301831 / 63793608040698169 : ℝ)))) (interior (pentagon (776866263 / 200000000 : ℝ) (1186770703 / 250000000 : ℝ) (arccos (586557495560487399 / 1413442504439512601 : ℝ)))) := by
  have hR : circumradius ^ 2 * ((385194309 / 125000000 : ℝ) ^ 2 + (248797669 / 62500000 : ℝ) ^ 2) ≤ (15839031043412869 / 1250000000000000 : ℝ) ^ 2 := by nlinarith [R_sq_le]
  exact halfplane_disjoint (385194309 / 125000000 : ℝ) (248797669 / 62500000 : ℝ) (2274445488818329891 / 125000000000000000 : ℝ) (by norm_num)
    (pent_far_le (e := (15839031043412869 / 1250000000000000 : ℝ)) (by norm_num) hR (by norm_num))
    (pent_far_ge (e := (15839031043412869 / 1250000000000000 : ℝ)) (by norm_num) hR (by norm_num))
lemma d1_12 : Disjoint (interior (pentagon (802776843 / 1000000000 : ℝ) (191580027 / 250000000 : ℝ) (arccos (61206391959301831 / 63793608040698169 : ℝ)))) (interior (pentagon (3385577897 / 1000000000 : ℝ) (174299027 / 100000000 : ℝ) (arccos (740383816821348399 / 1259616183178651601 : ℝ)))) := by
  have hR : circumradius ^ 2 * ((1291400527 / 500000000 : ℝ) ^ 2 + (488335081 / 500000000 : ℝ) ^ 2) ≤ (190618647247115429 / 50000000000000000 : ℝ) ^ 2 := by nlinarith [R_sq_le]
  exact halfplane_disjoint (1291400527 / 500000000 : ℝ) (488335081 / 500000000 : ℝ) (3317113902596859299 / 500000000000000000 : ℝ) (by norm_num)
    (pent_far_le (e := (190618647247115429 / 50000000000000000 : ℝ)) (by norm_num) hR (by norm_num))
    (pent_far_ge (e := (190618647247115429 / 50000000000000000 : ℝ)) (by norm_num) hR (by norm_num))
lemma d2_3 : Disjoint (interior (pentagon (3431749619 / 1000000000 : ℝ) (3262254353 / 1000000000 : ℝ) (arccos (559705058434431 / 1393419941565569 : ℝ)))) (interior (pentagon (2362406791 / 1000000000 : ℝ) (4832838093 / 1000000000 : ℝ) (arccos (740383816821348399 / 1259616183178651601 : ℝ)))) := by
  have hR : circumradius ^ 2 * ((-267335707 / 250000000 : ℝ) ^ 2 + (78529187 / 50000000 : ℝ) ^ 2) ≤ (112819605254607037 / 62500000000000000 : ℝ) ^ 2 := by nlinarith [R_sq_le]
  exact halfplane_disjoint (-267335707 / 250000000 : ℝ) (78529187 / 50000000 : ℝ) (81476012101758757 / 25000000000000000 : ℝ) (by norm_num)
    (pent_far_le (e := (112819605254607037 / 62500000000000000 : ℝ)) (by norm_num) hR (by norm_num))
    (pent_far_ge (e := (112819605254607037 / 62500000000000000 : ℝ)) (by norm_num) hR (by norm_num))
lemma d2_4 : Disjoint (interior (pentagon (3431749619 / 1000000000 : ℝ) (3262254353 / 1000000000 : ℝ) (arccos (559705058434431 / 1393419941565569 : ℝ)))) (interior (pentagon (4832838093 / 1000000000 : ℝ) (2133854777 / 1000000000 : ℝ) (arccos (3493856215434639 / 4318643784565361 : ℝ)))) := by
  have hR : circumradius ^ 2 * ((700544237 / 500000000 : ℝ) ^ 2 + (-141049947 / 125000000 : ℝ) ^ 2) ≤ (809083628773157113 / 500000000000000000 : ℝ) ^ 2 := by nlinarith [R_sq_le]
  exact halfplane_disjoint (700544237 / 500000000 : ℝ) (-141049947 / 125000000 : ℝ) (343153208206468913 / 125000000000000000 : ℝ) (by norm_num)
    (pent_far_le (e := (809083628773157113 / 500000000000000000 : ℝ)) (by norm_num) hR (by norm_num))
    (pent_far_ge (e := (809083628773157113 / 500000000000000000 : ℝ)) (by norm_num) hR (by norm_num))
lemma d2_5 : Disjoint (interior (pentagon (3431749619 / 1000000000 : ℝ) (3262254353 / 1000000000 : ℝ) (arccos (559705058434431 / 1393419941565569 : ℝ)))) (interior (pentagon (2058684837 / 1000000000 : ℝ) (420490387 / 125000000 : ℝ) (arccos (926604690537318031 / 1073395309462681969 : ℝ)))) := by
  exact halfplane_disjoint (-995084871 / 1000000000 : ℝ) (24756439 / 250000000 : ℝ) (-12018215077 / 5000000000 : ℝ) (by norm_num)
    (pent_le hc2 hs2 (by linarith [R_lo, R_hi, P_lo, P_hi, C_lo, C_hi]) (by linarith [R_lo, R_hi, P_lo, P_hi, C_lo, C_hi]) (by linarith [R_lo, R_hi, P_lo, P_hi, C_lo, C_hi]) (by linarith [R_lo, R_hi, P_lo, P_hi, C_lo, C_hi]) (by linarith [R_lo, R_hi, P_lo, P_hi, C_lo, C_hi]))
    (pent_ge hc5 hs5 (by linarith [R_lo, R_hi, P_lo, P_hi, C_lo, C_hi]) (by linarith [R_lo, R_hi, P_lo, P_hi, C_lo, C_hi]) (by linarith [R_lo, R_hi, P_lo, P_hi, C_lo, C_hi]) (by linarith [R_lo, R_hi, P_lo, P_hi, C_lo, C_hi]) (by linarith [R_lo, R_hi, P_lo, P_hi, C_lo, C_hi]))
lemma d2_6 : Disjoint (interior (pentagon (3431749619 / 1000000000 : ℝ) (3262254353 / 1000000000 : ℝ) (arccos (559705058434431 / 1393419941565569 : ℝ)))) (interior (pentagon (427541651 / 100000000 : ℝ) (688191907 / 1000000000 : ℝ) (arccos (609321480728679 / 640678519271321 : ℝ)))) := by
  have hR : circumradius ^ 2 * ((843666891 / 1000000000 : ℝ) ^ 2 + (-1287031223 / 500000000 : ℝ) ^ 2) ≤ (7337571298877108797 / 2000000000000000000 : ℝ) ^ 2 := by nlinarith [R_sq_le]
  exact halfplane_disjoint (843666891 / 1000000000 : ℝ) (-1287031223 / 500000000 : ℝ) (-3666414476333217021 / 2000000000000000000 : ℝ) (by norm_num)
    (pent_far_le (e := (7337571298877108797 / 2000000000000000000 : ℝ)) (by norm_num) hR (by norm_num))
    (pent_far_ge (e := (7337571298877108797 / 2000000000000000000 : ℝ)) (by norm_num) hR (by norm_num))
lemma d2_7 : Disjoint (interior (pentagon (3431749619 / 1000000000 : ℝ) (3262254353 / 1000000000 : ℝ) (arccos (559705058434431 / 1393419941565569 : ℝ)))) (interior (pentagon (688191907 / 1000000000 : ℝ) (2889578283 / 1000000000 : ℝ) (arccos (115267567140471 / 373013682859529 : ℝ)))) := by
  have hR : circumradius ^ 2 * ((-171472357 / 62500000 : ℝ) ^ 2 + (-37267607 / 100000000 : ℝ) ^ 2) ≤ (1916499093056329961 / 500000000000000000 : ℝ) ^ 2 := by nlinarith [R_sq_le]
  exact halfplane_disjoint (-171472357 / 62500000 : ℝ) (-37267607 / 100000000 : ℝ) (-1699492269591071129 / 250000000000000000 : ℝ) (by norm_num)
    (pent_far_le (e := (1916499093056329961 / 500000000000000000 : ℝ)) (by norm_num) hR (by norm_num))
    (pent_far_ge (e := (1916499093056329961 / 500000000000000000 : ℝ)) (by norm_num) hR (by norm_num))
lemma d2_8 : Disjoint (interior (pentagon (3431749619 / 1000000000 : ℝ) (3262254353 / 1000000000 : ℝ) (arccos (559705058434431 / 1393419941565569 : ℝ)))) (interior (pentagon (478052591 / 100000000 : ℝ) (921971257 / 250000000 : ℝ) (arccos (232693732679495631 / 267306267320504369 : ℝ)))) := by
  exact halfplane_disjoint (870513569 / 1000000000 : ℝ) (492144417 / 1000000000 : ℝ) (1322073196461 / 250000000000 : ℝ) (by norm_num)
    (pent_le hc2 hs2 (by linarith [R_lo, R_hi, P_lo, P_hi, C_lo, C_hi]) (by linarith [R_lo, R_hi, P_lo, P_hi, C_lo, C_hi]) (by linarith [R_lo, R_hi, P_lo, P_hi, C_lo, C_hi]) (by linarith [R_lo, R_hi, P_lo, P_hi, C_lo, C_hi]) (by linarith [R_lo, R_hi, P_lo, P_hi, C_lo, C_hi]))
    (pent_ge hc8 hs8 (by linarith [R_lo, R_hi, P_lo, P_hi, C_lo, C_hi]) (by linarith [R_lo, R_hi, P_lo, P_hi, C_lo, C_hi]) (by linarith [R_lo, R_hi, P_lo, P_hi, C_lo, C_hi]) (by linarith [R_lo, R_hi, P_lo, P_hi, C_lo, C_hi]) (by linarith [R_lo, R_hi, P_lo, P_hi, C_lo, C_hi]))
lemma d2_9 : Disjoint (interior (pentagon (3431749619 / 1000000000 : ℝ) (3262254353 / 1000000000 : ℝ) (arccos (559705058434431 / 1393419941565569 : ℝ)))) (interior (pentagon (346666363 / 500000000 : ℝ) (2330244233 / 500000000 : ℝ) (arccos (62499975254507751 / 62500024745492249 : ℝ)))) := by
  have hR : circumradius ^ 2 * ((-2738416893 / 1000000000 : ℝ) ^ 2 + (1398234113 / 1000000000 : ℝ) ^ 2) ≤ (4726992857312335109 / 1000000000000000000 : ℝ) ^ 2 := by nlinarith [R_sq_le]
  exact halfplane_disjoint (-2738416893 / 1000000000 : ℝ) (1398234113 / 1000000000 : ℝ) (-109172950256234769 / 1000000000000000000 : ℝ) (by norm_num)
    (pent_far_le (e := (4726992857312335109 / 1000000000000000000 : ℝ)) (by norm_num) hR (by norm_num))
    (pent_far_ge (e := (4726992857312335109 / 1000000000000000000 : ℝ)) (by norm_num) hR (by norm_num))
lemma d2_10 : Disjoint (interior (pentagon (3431749619 / 1000000000 : ℝ) (3262254353 / 1000000000 : ℝ) (arccos (559705058434431 / 1393419941565569 : ℝ)))) (interior (pentagon (3634983 / 2000000 : ℝ) (948360003 / 500000000 : ℝ) (arccos (740383816821348399 / 1259616183178651601 : ℝ)))) := by
  have hR : circumradius ^ 2 * ((-1614258119 / 1000000000 : ℝ) ^ 2 + (-1365534347 / 1000000000 : ℝ) ^ 2) ≤ (447051332759413457 / 200000000000000000 : ℝ) ^ 2 := by nlinarith [R_sq_le]
  exact halfplane_disjoint (-1614258119 / 1000000000 : ℝ) (-1365534347 / 1000000000 : ℝ) (-7759193388720601867 / 1000000000000000000 : ℝ) (by norm_num)
    (pent_far_le (e := (447051332759413457 / 200000000000000000 : ℝ)) (by norm_num) hR (by norm_num))
    (pent_far_ge (e := (447051332759413457 / 200000000000000000 : ℝ)) (by norm_num) hR (by norm_num))
lemma d2_11 : Disjoint (interior (pentagon (3431749619 / 1000000000 : ℝ) (3262254353 / 1000000000 : ℝ) (arccos (559705058434431 / 1393419941565569 : ℝ)))) (interior (pentagon (776866263 / 200000000 : ℝ) (1186770703 / 250000000 : ℝ) (arccos (586557495560487399 / 1413442504439512601 : ℝ)))) := by
  exact halfplane_disjoint (414985041 / 1000000000 : ℝ) (454914117 / 500000000 : ℝ) (5242777342651 / 1000000000000 : ℝ) (by norm_num)
    (pent_le hc2 hs2 (by linarith [R_lo, R_hi, P_lo, P_hi, C_lo, C_hi]) (by linarith [R_lo, R_hi, P_lo, P_hi, C_lo, C_hi]) (by linarith [R_lo, R_hi, P_lo, P_hi, C_lo, C_hi]) (by linarith [R_lo, R_hi, P_lo, P_hi, C_lo, C_hi]) (by linarith [R_lo, R_hi, P_lo, P_hi, C_lo, C_hi]))
    (pent_ge hc11 hs11 (by linarith [R_lo, R_hi, P_lo, P_hi, C_lo, C_hi]) (by linarith [R_lo, R_hi, P_lo, P_hi, C_lo, C_hi]) (by linarith [R_lo, R_hi, P_lo, P_hi, C_lo, C_hi]) (by linarith [R_lo, R_hi, P_lo, P_hi, C_lo, C_hi]) (by linarith [R_lo, R_hi, P_lo, P_hi, C_lo, C_hi]))
lemma d2_12 : Disjoint (interior (pentagon (3431749619 / 1000000000 : ℝ) (3262254353 / 1000000000 : ℝ) (arccos (559705058434431 / 1393419941565569 : ℝ)))) (interior (pentagon (3385577897 / 1000000000 : ℝ) (174299027 / 100000000 : ℝ) (arccos (740383816821348399 / 1259616183178651601 : ℝ)))) := by
  exact halfplane_disjoint (-1 / 1000000000 : ℝ) (-1 : ℝ) (-2431182279297 / 1000000000000 : ℝ) (by norm_num)
    (pent_le hc2 hs2 (by linarith [R_lo, R_hi, P_lo, P_hi, C_lo, C_hi]) (by linarith [R_lo, R_hi, P_lo, P_hi, C_lo, C_hi]) (by linarith [R_lo, R_hi, P_lo, P_hi, C_lo, C_hi]) (by linarith [R_lo, R_hi, P_lo, P_hi, C_lo, C_hi]) (by linarith [R_lo, R_hi, P_lo, P_hi, C_lo, C_hi]))
    (pent_ge hc12 hs12 (by linarith [R_lo, R_hi, P_lo, P_hi, C_lo, C_hi]) (by linarith [R_lo, R_hi, P_lo, P_hi, C_lo, C_hi]) (by linarith [R_lo, R_hi, P_lo, P_hi, C_lo, C_hi]) (by linarith [R_lo, R_hi, P_lo, P_hi, C_lo, C_hi]) (by linarith [R_lo, R_hi, P_lo, P_hi, C_lo, C_hi]))
lemma d3_4 : Disjoint (interior (pentagon (2362406791 / 1000000000 : ℝ) (4832838093 / 1000000000 : ℝ) (arccos (740383816821348399 / 1259616183178651601 : ℝ)))) (interior (pentagon (4832838093 / 1000000000 : ℝ) (2133854777 / 1000000000 : ℝ) (arccos (3493856215434639 / 4318643784565361 : ℝ)))) := by
  have hR : circumradius ^ 2 * ((1235215651 / 500000000 : ℝ) ^ 2 + (-674745829 / 250000000 : ℝ) ^ 2) ≤ (669377087897388553 / 100000000000000000 : ℝ) ^ 2 := by nlinarith [R_sq_le]
  exact halfplane_disjoint (1235215651 / 500000000 : ℝ) (-674745829 / 250000000 : ℝ) (-8028356537790609 / 15625000000000000 : ℝ) (by norm_num)
    (pent_far_le (e := (669377087897388553 / 100000000000000000 : ℝ)) (by norm_num) hR (by norm_num))
    (pent_far_ge (e := (669377087897388553 / 100000000000000000 : ℝ)) (by norm_num) hR (by norm_num))
lemma d3_5 : Disjoint (interior (pentagon (2362406791 / 1000000000 : ℝ) (4832838093 / 1000000000 : ℝ) (arccos (740383816821348399 / 1259616183178651601 : ℝ)))) (interior (pentagon (2058684837 / 1000000000 : ℝ) (420490387 / 125000000 : ℝ) (arccos (926604690537318031 / 1073395309462681969 : ℝ)))) := by
  exact halfplane_disjoint (-401677227 / 1000000000 : ℝ) (-915781309 / 1000000000 : ℝ) (-2297868341559 / 500000000000 : ℝ) (by norm_num)
    (pent_le hc3 hs3 (by linarith [R_lo, R_hi, P_lo, P_hi, C_lo, C_hi]) (by linarith [R_lo, R_hi, P_lo, P_hi, C_lo, C_hi]) (by linarith [R_lo, R_hi, P_lo, P_hi, C_lo, C_hi]) (by linarith [R_lo, R_hi, P_lo, P_hi, C_lo, C_hi]) (by linarith [R_lo, R_hi, P_lo, P_hi, C_lo, C_hi]))
    (pent_ge hc5 hs5 (by linarith [R_lo, R_hi, P_lo, P_hi, C_lo, C_hi]) (by linarith [R_lo, R_hi, P_lo, P_hi, C_lo, C_hi]) (by linarith [R_lo, R_hi, P_lo, P_hi, C_lo, C_hi]) (by linarith [R_lo, R_hi, P_lo, P_hi, C_lo, C_hi]) (by linarith [R_lo, R_hi, P_lo, P_hi, C_lo, C_hi]))
lemma d3_6 : Disjoint (interior (pentagon (2362406791 / 1000000000 : ℝ) (4832838093 / 1000000000 : ℝ) (arccos (740383816821348399 / 1259616183178651601 : ℝ)))) (interior (pentagon (427541651 / 100000000 : ℝ) (688191907 / 1000000000 : ℝ) (arccos (609321480728679 / 640678519271321 : ℝ)))) := by
  have hR : circumradius ^ 2 * ((1913009719 / 1000000000 : ℝ) ^ 2 + (-2072323093 / 500000000 : ℝ) ^ 2) ≤ (20837698192112805557 / 2000000000000000000 : ℝ) ^ 2 := by nlinarith [R_sq_le]
  exact halfplane_disjoint (1913009719 / 1000000000 : ℝ) (-2072323093 / 500000000 : ℝ) (-10184495444473917581 / 2000000000000000000 : ℝ) (by norm_num)
    (pent_far_le (e := (20837698192112805557 / 2000000000000000000 : ℝ)) (by norm_num) hR (by norm_num))
    (pent_far_ge (e := (20837698192112805557 / 2000000000000000000 : ℝ)) (by norm_num) hR (by norm_num))
lemma d3_7 : Disjoint (interior (pentagon (2362406791 / 1000000000 : ℝ) (4832838093 / 1000000000 : ℝ) (arccos (740383816821348399 / 1259616183178651601 : ℝ)))) (interior (pentagon (688191907 / 1000000000 : ℝ) (2889578283 / 1000000000 : ℝ) (arccos (115267567140471 / 373013682859529 : ℝ)))) := by
  have hR : circumradius ^ 2 * ((-418553721 / 250000000 : ℝ) ^ 2 + (-194325981 / 100000000 : ℝ) ^ 2) ≤ (1644813541742092389 / 500000000000000000 : ℝ) ^ 2 := by nlinarith [R_sq_le]
  exact halfplane_disjoint (-418553721 / 250000000 : ℝ) (-194325981 / 100000000 : ℝ) (-2514252390608658699 / 250000000000000000 : ℝ) (by norm_num)
    (pent_far_le (e := (1644813541742092389 / 500000000000000000 : ℝ)) (by norm_num) hR (by norm_num))
    (pent_far_ge (e := (1644813541742092389 / 500000000000000000 : ℝ)) (by norm_num) hR (by norm_num))
lemma d3_8 : Disjoint (interior (pentagon (2362406791 / 1000000000 : ℝ) (4832838093 / 1000000000 : ℝ) (arccos (740383816821348399 / 1259616183178651601 : ℝ)))) (interior (pentagon (478052591 / 100000000 : ℝ) (921971257 / 250000000 : ℝ) (arccos (232693732679495631 / 267306267320504369 : ℝ)))) := by
  have hR : circumradius ^ 2 * ((2418119119 / 1000000000 : ℝ) ^ 2 + (-228990613 / 200000000 : ℝ) ^ 2) ≤ (3579108797363115193 / 1000000000000000000 : ℝ) ^ 2 := by nlinarith [R_sq_le]
  exact halfplane_disjoint (2418119119 / 1000000000 : ℝ) (-228990613 / 200000000 : ℝ) (3758317038306547277 / 1000000000000000000 : ℝ) (by norm_num)
    (pent_far_le (e := (3579108797363115193 / 1000000000000000000 : ℝ)) (by norm_num) hR (by norm_num))
    (pent_far_ge (e := (3579108797363115193 / 1000000000000000000 : ℝ)) (by norm_num) hR (by norm_num))
lemma d3_9 : Disjoint (interior (pentagon (2362406791 / 1000000000 : ℝ) (4832838093 / 1000000000 : ℝ) (arccos (740383816821348399 / 1259616183178651601 : ℝ)))) (interior (pentagon (346666363 / 500000000 : ℝ) (2330244233 / 500000000 : ℝ) (arccos (62499975254507751 / 62500024745492249 : ℝ)))) := by
  exact halfplane_disjoint (-237764129 / 250000000 : ℝ) (61803399 / 200000000 : ℝ) (-11634540223 / 250000000000 : ℝ) (by norm_num)
    (pent_le hc3 hs3 (by linarith [R_lo, R_hi, P_lo, P_hi, C_lo, C_hi]) (by linarith [R_lo, R_hi, P_lo, P_hi, C_lo, C_hi]) (by linarith [R_lo, R_hi, P_lo, P_hi, C_lo, C_hi]) (by linarith [R_lo, R_hi, P_lo, P_hi, C_lo, C_hi]) (by linarith [R_lo, R_hi, P_lo, P_hi, C_lo, C_hi]))
    (pent_ge hc9 hs9 (by linarith [R_lo, R_hi, P_lo, P_hi, C_lo, C_hi]) (by linarith [R_lo, R_hi, P_lo, P_hi, C_lo, C_hi]) (by linarith [R_lo, R_hi, P_lo, P_hi, C_lo, C_hi]) (by linarith [R_lo, R_hi, P_lo, P_hi, C_lo, C_hi]) (by linarith [R_lo, R_hi, P_lo, P_hi, C_lo, C_hi]))
lemma d3_10 : Disjoint (interior (pentagon (2362406791 / 1000000000 : ℝ) (4832838093 / 1000000000 : ℝ) (arccos (740383816821348399 / 1259616183178651601 : ℝ)))) (interior (pentagon (3634983 / 2000000 : ℝ) (948360003 / 500000000 : ℝ) (arccos (740383816821348399 / 1259616183178651601 : ℝ)))) := by
  have hR : circumradius ^ 2 * ((-544915291 / 1000000000 : ℝ) ^ 2 + (-2936118087 / 1000000000 : ℝ) ^ 2) ≤ (35670888380696617 / 8000000000000000 : ℝ) ^ 2 := by nlinarith [R_sq_le]
  exact halfplane_disjoint (-544915291 / 1000000000 : ℝ) (-2936118087 / 1000000000 : ℝ) (-11018233872790952147 / 1000000000000000000 : ℝ) (by norm_num)
    (pent_far_le (e := (35670888380696617 / 8000000000000000 : ℝ)) (by norm_num) hR (by norm_num))
    (pent_far_ge (e := (35670888380696617 / 8000000000000000 : ℝ)) (by norm_num) hR (by norm_num))
lemma d3_11 : Disjoint (interior (pentagon (2362406791 / 1000000000 : ℝ) (4832838093 / 1000000000 : ℝ) (arccos (740383816821348399 / 1259616183178651601 : ℝ)))) (interior (pentagon (776866263 / 200000000 : ℝ) (1186770703 / 250000000 : ℝ) (arccos (586557495560487399 / 1413442504439512601 : ℝ)))) := by
  exact halfplane_disjoint (993535501 / 1000000000 : ℝ) (-113521841 / 1000000000 : ℝ) (131606573557 / 50000000000 : ℝ) (by norm_num)
    (pent_le hc3 hs3 (by linarith [R_lo, R_hi, P_lo, P_hi, C_lo, C_hi]) (by linarith [R_lo, R_hi, P_lo, P_hi, C_lo, C_hi]) (by linarith [R_lo, R_hi, P_lo, P_hi, C_lo, C_hi]) (by linarith [R_lo, R_hi, P_lo, P_hi, C_lo, C_hi]) (by linarith [R_lo, R_hi, P_lo, P_hi, C_lo, C_hi]))
    (pent_ge hc11 hs11 (by linarith [R_lo, R_hi, P_lo, P_hi, C_lo, C_hi]) (by linarith [R_lo, R_hi, P_lo, P_hi, C_lo, C_hi]) (by linarith [R_lo, R_hi, P_lo, P_hi, C_lo, C_hi]) (by linarith [R_lo, R_hi, P_lo, P_hi, C_lo, C_hi]) (by linarith [R_lo, R_hi, P_lo, P_hi, C_lo, C_hi]))
lemma d3_12 : Disjoint (interior (pentagon (2362406791 / 1000000000 : ℝ) (4832838093 / 1000000000 : ℝ) (arccos (740383816821348399 / 1259616183178651601 : ℝ)))) (interior (pentagon (3385577897 / 1000000000 : ℝ) (174299027 / 100000000 : ℝ) (arccos (740383816821348399 / 1259616183178651601 : ℝ)))) := by
  have hR : circumradius ^ 2 * ((511585553 / 500000000 : ℝ) ^ 2 + (-3089847823 / 1000000000 : ℝ) ^ 2) ≤ (2118807736290220513 / 400000000000000000 : ℝ) ^ 2 := by nlinarith [R_sq_le]
  exact halfplane_disjoint (511585553 / 500000000 : ℝ) (-3089847823 / 1000000000 : ℝ) (-14437137101345178821 / 2000000000000000000 : ℝ) (by norm_num)
    (pent_far_le (e := (2118807736290220513 / 400000000000000000 : ℝ)) (by norm_num) hR (by norm_num))
    (pent_far_ge (e := (2118807736290220513 / 400000000000000000 : ℝ)) (by norm_num) hR (by norm_num))
lemma d4_5 : Disjoint (interior (pentagon (4832838093 / 1000000000 : ℝ) (2133854777 / 1000000000 : ℝ) (arccos (3493856215434639 / 4318643784565361 : ℝ)))) (interior (pentagon (2058684837 / 1000000000 : ℝ) (420490387 / 125000000 : ℝ) (arccos (926604690537318031 / 1073395309462681969 : ℝ)))) := by
  have hR : circumradius ^ 2 * ((-346769157 / 125000000 : ℝ) ^ 2 + (1230068319 / 1000000000 : ℝ) ^ 2) ≤ (9208994357182887297 / 2000000000000000000 : ℝ) ^ 2 := by nlinarith [R_sq_le]
  exact halfplane_disjoint (-346769157 / 125000000 : ℝ) (1230068319 / 1000000000 : ℝ) (-12355498388581654593 / 2000000000000000000 : ℝ) (by norm_num)
    (pent_far_le (e := (9208994357182887297 / 2000000000000000000 : ℝ)) (by norm_num) hR (by norm_num))
    (pent_far_ge (e := (9208994357182887297 / 2000000000000000000 : ℝ)) (by norm_num) hR (by norm_num))
lemma d4_6 : Disjoint (interior (pentagon (4832838093 / 1000000000 : ℝ) (2133854777 / 1000000000 : ℝ) (arccos (3493856215434639 / 4318643784565361 : ℝ)))) (interior (pentagon (427541651 / 100000000 : ℝ) (688191907 / 1000000000 : ℝ) (arccos (609321480728679 / 640678519271321 : ℝ)))) := by
  exact halfplane_disjoint (-587785253 / 1000000000 : ℝ) (-404508497 / 500000000 : ℝ) (-3757977713709 / 1000000000000 : ℝ) (by norm_num)
    (pent_le hc4 hs4 (by linarith [R_lo, R_hi, P_lo, P_hi, C_lo, C_hi]) (by linarith [R_lo, R_hi, P_lo, P_hi, C_lo, C_hi]) (by linarith [R_lo, R_hi, P_lo, P_hi, C_lo, C_hi]) (by linarith [R_lo, R_hi, P_lo, P_hi, C_lo, C_hi]) (by linarith [R_lo, R_hi, P_lo, P_hi, C_lo, C_hi]))
    (pent_ge hc6 hs6 (by linarith [R_lo, R_hi, P_lo, P_hi, C_lo, C_hi]) (by linarith [R_lo, R_hi, P_lo, P_hi, C_lo, C_hi]) (by linarith [R_lo, R_hi, P_lo, P_hi, C_lo, C_hi]) (by linarith [R_lo, R_hi, P_lo, P_hi, C_lo, C_hi]) (by linarith [R_lo, R_hi, P_lo, P_hi, C_lo, C_hi]))
lemma d4_7 : Disjoint (interior (pentagon (4832838093 / 1000000000 : ℝ) (2133854777 / 1000000000 : ℝ) (arccos (3493856215434639 / 4318643784565361 : ℝ)))) (interior (pentagon (688191907 / 1000000000 : ℝ) (2889578283 / 1000000000 : ℝ) (arccos (115267567140471 / 373013682859529 : ℝ)))) := by
  have hR : circumradius ^ 2 * ((-2072323093 / 500000000 : ℝ) ^ 2 + (377861753 / 500000000 : ℝ) ^ 2) ≤ (2218651253080659829 / 250000000000000000 : ℝ) ^ 2 := by nlinarith [R_sq_le]
  exact halfplane_disjoint (-2072323093 / 500000000 : ℝ) (377861753 / 500000000 : ℝ) (-477159737200801791 / 50000000000000000 : ℝ) (by norm_num)
    (pent_far_le (e := (2218651253080659829 / 250000000000000000 : ℝ)) (by norm_num) hR (by norm_num))
    (pent_far_ge (e := (2218651253080659829 / 250000000000000000 : ℝ)) (by norm_num) hR (by norm_num))
lemma d4_8 : Disjoint (interior (pentagon (4832838093 / 1000000000 : ℝ) (2133854777 / 1000000000 : ℝ) (arccos (3493856215434639 / 4318643784565361 : ℝ)))) (interior (pentagon (478052591 / 100000000 : ℝ) (921971257 / 250000000 : ℝ) (arccos (232693732679495631 / 267306267320504369 : ℝ)))) := by
  exact halfplane_disjoint (-49763417 / 250000000 : ℝ) (97998859 / 100000000 : ℝ) (246789002057 / 125000000000 : ℝ) (by norm_num)
    (pent_le hc4 hs4 (by linarith [R_lo, R_hi, P_lo, P_hi, C_lo, C_hi]) (by linarith [R_lo, R_hi, P_lo, P_hi, C_lo, C_hi]) (by linarith [R_lo, R_hi, P_lo, P_hi, C_lo, C_hi]) (by linarith [R_lo, R_hi, P_lo, P_hi, C_lo, C_hi]) (by linarith [R_lo, R_hi, P_lo, P_hi, C_lo, C_hi]))
    (pent_ge hc8 hs8 (by linarith [R_lo, R_hi, P_lo, P_hi, C_lo, C_hi]) (by linarith [R_lo, R_hi, P_lo, P_hi, C_lo, C_hi]) (by linarith [R_lo, R_hi, P_lo, P_hi, C_lo, C_hi]) (by linarith [R_lo, R_hi, P_lo, P_hi, C_lo, C_hi]) (by linarith [R_lo, R_hi, P_lo, P_hi, C_lo, C_hi]))
lemma d4_9 : Disjoint (interior (pentagon (4832838093 / 1000000000 : ℝ) (2133854777 / 1000000000 : ℝ) (arccos (3493856215434639 / 4318643784565361 : ℝ)))) (interior (pentagon (346666363 / 500000000 : ℝ) (2330244233 / 500000000 : ℝ) (arccos (62499975254507751 / 62500024745492249 : ℝ)))) := by
  have hR : circumradius ^ 2 * ((-4139505367 / 1000000000 : ℝ) ^ 2 + (2526633689 / 1000000000 : ℝ) ^ 2) ≤ (2351938248181155341 / 200000000000000000 : ℝ) ^ 2 := by nlinarith [R_sq_le]
  exact halfplane_disjoint (-4139505367 / 1000000000 : ℝ) (2526633689 / 1000000000 : ℝ) (-2854398615907986073 / 1000000000000000000 : ℝ) (by norm_num)
    (pent_far_le (e := (2351938248181155341 / 200000000000000000 : ℝ)) (by norm_num) hR (by norm_num))
    (pent_far_ge (e := (2351938248181155341 / 200000000000000000 : ℝ)) (by norm_num) hR (by norm_num))
lemma d4_10 : Disjoint (interior (pentagon (4832838093 / 1000000000 : ℝ) (2133854777 / 1000000000 : ℝ) (arccos (3493856215434639 / 4318643784565361 : ℝ)))) (interior (pentagon (3634983 / 2000000 : ℝ) (948360003 / 500000000 : ℝ) (arccos (740383816821348399 / 1259616183178651601 : ℝ)))) := by
  have hR : circumradius ^ 2 * ((-3015346593 / 1000000000 : ℝ) ^ 2 + (-237134771 / 1000000000 : ℝ) ^ 2) ≤ (914854797553393009 / 200000000000000000 : ℝ) ^ 2 := by nlinarith [R_sq_le]
  exact halfplane_disjoint (-3015346593 / 1000000000 : ℝ) (-237134771 / 1000000000 : ℝ) (-10504419054372353171 / 1000000000000000000 : ℝ) (by norm_num)
    (pent_far_le (e := (914854797553393009 / 200000000000000000 : ℝ)) (by norm_num) hR (by norm_num))
    (pent_far_ge (e := (914854797553393009 / 200000000000000000 : ℝ)) (by norm_num) hR (by norm_num))
lemma d4_11 : Disjoint (interior (pentagon (4832838093 / 1000000000 : ℝ) (2133854777 / 1000000000 : ℝ) (arccos (3493856215434639 / 4318643784565361 : ℝ)))) (interior (pentagon (776866263 / 200000000 : ℝ) (1186770703 / 250000000 : ℝ) (arccos (586557495560487399 / 1413442504439512601 : ℝ)))) := by
  have hR : circumradius ^ 2 * ((-474253389 / 500000000 : ℝ) ^ 2 + (522645607 / 200000000 : ℝ) ^ 2) ≤ (7728625870821902509 / 2000000000000000000 : ℝ) ^ 2 := by nlinarith [R_sq_le]
  exact halfplane_disjoint (-474253389 / 500000000 : ℝ) (522645607 / 200000000 : ℝ) (9713164746197860191 / 2000000000000000000 : ℝ) (by norm_num)
    (pent_far_le (e := (7728625870821902509 / 2000000000000000000 : ℝ)) (by norm_num) hR (by norm_num))
    (pent_far_ge (e := (7728625870821902509 / 2000000000000000000 : ℝ)) (by norm_num) hR (by norm_num))
lemma d4_12 : Disjoint (interior (pentagon (4832838093 / 1000000000 : ℝ) (2133854777 / 1000000000 : ℝ) (arccos (3493856215434639 / 4318643784565361 : ℝ)))) (interior (pentagon (3385577897 / 1000000000 : ℝ) (174299027 / 100000000 : ℝ) (arccos (740383816821348399 / 1259616183178651601 : ℝ)))) := by
  exact halfplane_disjoint (-951056517 / 1000000000 : ℝ) (-154508497 / 500000000 : ℝ) (-2223340763789 / 500000000000 : ℝ) (by norm_num)
    (pent_le hc4 hs4 (by linarith [R_lo, R_hi, P_lo, P_hi, C_lo, C_hi]) (by linarith [R_lo, R_hi, P_lo, P_hi, C_lo, C_hi]) (by linarith [R_lo, R_hi, P_lo, P_hi, C_lo, C_hi]) (by linarith [R_lo, R_hi, P_lo, P_hi, C_lo, C_hi]) (by linarith [R_lo, R_hi, P_lo, P_hi, C_lo, C_hi]))
    (pent_ge hc12 hs12 (by linarith [R_lo, R_hi, P_lo, P_hi, C_lo, C_hi]) (by linarith [R_lo, R_hi, P_lo, P_hi, C_lo, C_hi]) (by linarith [R_lo, R_hi, P_lo, P_hi, C_lo, C_hi]) (by linarith [R_lo, R_hi, P_lo, P_hi, C_lo, C_hi]) (by linarith [R_lo, R_hi, P_lo, P_hi, C_lo, C_hi]))
lemma d5_6 : Disjoint (interior (pentagon (2058684837 / 1000000000 : ℝ) (420490387 / 125000000 : ℝ) (arccos (926604690537318031 / 1073395309462681969 : ℝ)))) (interior (pentagon (427541651 / 100000000 : ℝ) (688191907 / 1000000000 : ℝ) (arccos (609321480728679 / 640678519271321 : ℝ)))) := by
  have hR : circumradius ^ 2 * ((2216731673 / 1000000000 : ℝ) ^ 2 + (-2675731189 / 1000000000 : ℝ) ^ 2) ≤ (241468734117374653 / 40000000000000000 : ℝ) ^ 2 := by nlinarith [R_sq_le]
  exact halfplane_disjoint (2216731673 / 1000000000 : ℝ) (-2675731189 / 1000000000 : ℝ) (799658145236233741 / 500000000000000000 : ℝ) (by norm_num)
    (pent_far_le (e := (241468734117374653 / 40000000000000000 : ℝ)) (by norm_num) hR (by norm_num))
    (pent_far_ge (e := (241468734117374653 / 40000000000000000 : ℝ)) (by norm_num) hR (by norm_num))
lemma d5_7 : Disjoint (interior (pentagon (2058684837 / 1000000000 : ℝ) (420490387 / 125000000 : ℝ) (arccos (926604690537318031 / 1073395309462681969 : ℝ)))) (interior (pentagon (688191907 / 1000000000 : ℝ) (2889578283 / 1000000000 : ℝ) (arccos (115267567140471 / 373013682859529 : ℝ)))) := by
  exact halfplane_disjoint (-17264929 / 20000000 : ℝ) (-126195673 / 250000000 : ℝ) (-2787010594417 / 1000000000000 : ℝ) (by norm_num)
    (pent_le hc5 hs5 (by linarith [R_lo, R_hi, P_lo, P_hi, C_lo, C_hi]) (by linarith [R_lo, R_hi, P_lo, P_hi, C_lo, C_hi]) (by linarith [R_lo, R_hi, P_lo, P_hi, C_lo, C_hi]) (by linarith [R_lo, R_hi, P_lo, P_hi, C_lo, C_hi]) (by linarith [R_lo, R_hi, P_lo, P_hi, C_lo, C_hi]))
    (pent_ge hc7 hs7 (by linarith [R_lo, R_hi, P_lo, P_hi, C_lo, C_hi]) (by linarith [R_lo, R_hi, P_lo, P_hi, C_lo, C_hi]) (by linarith [R_lo, R_hi, P_lo, P_hi, C_lo, C_hi]) (by linarith [R_lo, R_hi, P_lo, P_hi, C_lo, C_hi]) (by linarith [R_lo, R_hi, P_lo, P_hi, C_lo, C_hi]))
lemma d5_8 : Disjoint (interior (pentagon (2058684837 / 1000000000 : ℝ) (420490387 / 125000000 : ℝ) (arccos (926604690537318031 / 1073395309462681969 : ℝ)))) (interior (pentagon (478052591 / 100000000 : ℝ) (921971257 / 250000000 : ℝ) (arccos (232693732679495631 / 267306267320504369 : ℝ)))) := by
  have hR : circumradius ^ 2 * ((2721841073 / 1000000000 : ℝ) ^ 2 + (80990483 / 250000000 : ℝ) ^ 2) ≤ (7513370160054963953 / 2000000000000000000 : ℝ) ^ 2 := by nlinarith [R_sq_le]
  exact halfplane_disjoint (2721841073 / 1000000000 : ℝ) (80990483 / 250000000 : ℝ) (20899762102031947099 / 2000000000000000000 : ℝ) (by norm_num)
    (pent_far_le (e := (7513370160054963953 / 2000000000000000000 : ℝ)) (by norm_num) hR (by norm_num))
    (pent_far_ge (e := (7513370160054963953 / 2000000000000000000 : ℝ)) (by norm_num) hR (by norm_num))
lemma d5_9 : Disjoint (interior (pentagon (2058684837 / 1000000000 : ℝ) (420490387 / 125000000 : ℝ) (arccos (926604690537318031 / 1073395309462681969 : ℝ)))) (interior (pentagon (346666363 / 500000000 : ℝ) (2330244233 / 500000000 : ℝ) (arccos (62499975254507751 / 62500024745492249 : ℝ)))) := by
  have hR : circumradius ^ 2 * ((-1365352111 / 1000000000 : ℝ) ^ 2 + (129656537 / 100000000 : ℝ) ^ 2) ≤ (3545268145695393221 / 2000000000000000000 : ℝ) ^ 2 := by nlinarith [R_sq_le]
  exact halfplane_disjoint (-1365352111 / 1000000000 : ℝ) (129656537 / 100000000 : ℝ) (6646701156765682447 / 2000000000000000000 : ℝ) (by norm_num)
    (pent_far_le (e := (3545268145695393221 / 2000000000000000000 : ℝ)) (by norm_num) hR (by norm_num))
    (pent_far_ge (e := (3545268145695393221 / 2000000000000000000 : ℝ)) (by norm_num) hR (by norm_num))
lemma d5_10 : Disjoint (interior (pentagon (2058684837 / 1000000000 : ℝ) (420490387 / 125000000 : ℝ) (arccos (926604690537318031 / 1073395309462681969 : ℝ)))) (interior (pentagon (3634983 / 2000000 : ℝ) (948360003 / 500000000 : ℝ) (arccos (740383816821348399 / 1259616183178651601 : ℝ)))) := by
  exact halfplane_disjoint (-1 / 1000000000 : ℝ) (-1 : ℝ) (-2584911977617 / 1000000000000 : ℝ) (by norm_num)
    (pent_le hc5 hs5 (by linarith [R_lo, R_hi, P_lo, P_hi, C_lo, C_hi]) (by linarith [R_lo, R_hi, P_lo, P_hi, C_lo, C_hi]) (by linarith [R_lo, R_hi, P_lo, P_hi, C_lo, C_hi]) (by linarith [R_lo, R_hi, P_lo, P_hi, C_lo, C_hi]) (by linarith [R_lo, R_hi, P_lo, P_hi, C_lo, C_hi]))
    (pent_ge hc10 hs10 (by linarith [R_lo, R_hi, P_lo, P_hi, C_lo, C_hi]) (by linarith [R_lo, R_hi, P_lo, P_hi, C_lo, C_hi]) (by linarith [R_lo, R_hi, P_lo, P_hi, C_lo, C_hi]) (by linarith [R_lo, R_hi, P_lo, P_hi, C_lo, C_hi]) (by linarith [R_lo, R_hi, P_lo, P_hi, C_lo, C_hi]))
lemma d5_11 : Disjoint (interior (pentagon (2058684837 / 1000000000 : ℝ) (420490387 / 125000000 : ℝ) (arccos (926604690537318031 / 1073395309462681969 : ℝ)))) (interior (pentagon (776866263 / 200000000 : ℝ) (1186770703 / 250000000 : ℝ) (arccos (586557495560487399 / 1413442504439512601 : ℝ)))) := by
  have hR : circumradius ^ 2 * ((912823239 / 500000000 : ℝ) ^ 2 + (345789929 / 250000000 : ℝ) ^ 2) ≤ (262305793129950257 / 100000000000000000 : ℝ) ^ 2 := by nlinarith [R_sq_le]
  exact halfplane_disjoint (912823239 / 500000000 : ℝ) (345789929 / 250000000 : ℝ) (689645722961859837 / 62500000000000000 : ℝ) (by norm_num)
    (pent_far_le (e := (262305793129950257 / 100000000000000000 : ℝ)) (by norm_num) hR (by norm_num))
    (pent_far_ge (e := (262305793129950257 / 100000000000000000 : ℝ)) (by norm_num) hR (by norm_num))
lemma d5_12 : Disjoint (interior (pentagon (2058684837 / 1000000000 : ℝ) (420490387 / 125000000 : ℝ) (arccos (926604690537318031 / 1073395309462681969 : ℝ)))) (interior (pentagon (3385577897 / 1000000000 : ℝ) (174299027 / 100000000 : ℝ) (arccos (740383816821348399 / 1259616183178651601 : ℝ)))) := by
  have hR : circumradius ^ 2 * ((66344653 / 50000000 : ℝ) ^ 2 + (-810466413 / 500000000 : ℝ) ^ 2) ≤ (1097017104770127469 / 500000000000000000 : ℝ) ^ 2 := by nlinarith [R_sq_le]
  exact halfplane_disjoint (66344653 / 50000000 : ℝ) (-810466413 / 500000000 : ℝ) (-263502268981581569 / 500000000000000000 : ℝ) (by norm_num)
    (pent_far_le (e := (1097017104770127469 / 500000000000000000 : ℝ)) (by norm_num) hR (by norm_num))
    (pent_far_ge (e := (1097017104770127469 / 500000000000000000 : ℝ)) (by norm_num) hR (by norm_num))
lemma d6_7 : Disjoint (interior (pentagon (427541651 / 100000000 : ℝ) (688191907 / 1000000000 : ℝ) (arccos (609321480728679 / 640678519271321 : ℝ)))) (interior (pentagon (688191907 / 1000000000 : ℝ) (2889578283 / 1000000000 : ℝ) (arccos (115267567140471 / 373013682859529 : ℝ)))) := by
  have hR : circumradius ^ 2 * ((-3587224603 / 1000000000 : ℝ) ^ 2 + (275173297 / 125000000 : ℝ) ^ 2) ≤ (3542856465761384197 / 400000000000000000 : ℝ) ^ 2 := by nlinarith [R_sq_le]
  exact halfplane_disjoint (-3587224603 / 1000000000 : ℝ) (275173297 / 125000000 : ℝ) (-9929523680395352011 / 2000000000000000000 : ℝ) (by norm_num)
    (pent_far_le (e := (3542856465761384197 / 400000000000000000 : ℝ)) (by norm_num) hR (by norm_num))
    (pent_far_ge (e := (3542856465761384197 / 400000000000000000 : ℝ)) (by norm_num) hR (by norm_num))
lemma d6_8 : Disjoint (interior (pentagon (427541651 / 100000000 : ℝ) (688191907 / 1000000000 : ℝ) (arccos (609321480728679 / 640678519271321 : ℝ)))) (interior (pentagon (478052591 / 100000000 : ℝ) (921971257 / 250000000 : ℝ) (arccos (232693732679495631 / 267306267320504369 : ℝ)))) := by
  have hR : circumradius ^ 2 * ((2525547 / 5000000 : ℝ) ^ 2 + (2999693121 / 1000000000 : ℝ) ^ 2) ≤ (9253294326143080641 / 2000000000000000000 : ℝ) ^ 2 := by nlinarith [R_sq_le]
  exact halfplane_disjoint (2525547 / 5000000 : ℝ) (2999693121 / 1000000000 : ℝ) (3540225904217402427 / 400000000000000000 : ℝ) (by norm_num)
    (pent_far_le (e := (9253294326143080641 / 2000000000000000000 : ℝ)) (by norm_num) hR (by norm_num))
    (pent_far_ge (e := (9253294326143080641 / 2000000000000000000 : ℝ)) (by norm_num) hR (by norm_num))
lemma d6_9 : Disjoint (interior (pentagon (427541651 / 100000000 : ℝ) (688191907 / 1000000000 : ℝ) (arccos (609321480728679 / 640678519271321 : ℝ)))) (interior (pentagon (346666363 / 500000000 : ℝ) (2330244233 / 500000000 : ℝ) (arccos (62499975254507751 / 62500024745492249 : ℝ)))) := by
  have hR : circumradius ^ 2 * ((-447760473 / 125000000 : ℝ) ^ 2 + (3972296559 / 1000000000 : ℝ) ^ 2) ≤ (28610464188238999137 / 2000000000000000000 : ℝ) ^ 2 := by nlinarith [R_sq_le]
  exact halfplane_disjoint (-447760473 / 125000000 : ℝ) (3972296559 / 1000000000 : ℝ) (3448068575820747483 / 2000000000000000000 : ℝ) (by norm_num)
    (pent_far_le (e := (28610464188238999137 / 2000000000000000000 : ℝ)) (by norm_num) hR (by norm_num))
    (pent_far_ge (e := (28610464188238999137 / 2000000000000000000 : ℝ)) (by norm_num) hR (by norm_num))
lemma d6_10 : Disjoint (interior (pentagon (427541651 / 100000000 : ℝ) (688191907 / 1000000000 : ℝ) (arccos (609321480728679 / 640678519271321 : ℝ)))) (interior (pentagon (3634983 / 2000000 : ℝ) (948360003 / 500000000 : ℝ) (arccos (740383816821348399 / 1259616183178651601 : ℝ)))) := by
  have hR : circumradius ^ 2 * ((-245792501 / 100000000 : ℝ) ^ 2 + (1208528099 / 1000000000 : ℝ) ^ 2) ≤ (7501935520856053901 / 2000000000000000000 : ℝ) ^ 2 := by nlinarith [R_sq_le]
  exact halfplane_disjoint (-245792501 / 100000000 : ℝ) (1208528099 / 1000000000 : ℝ) (-11851972301107986713 / 2000000000000000000 : ℝ) (by norm_num)
    (pent_far_le (e := (7501935520856053901 / 2000000000000000000 : ℝ)) (by norm_num) hR (by norm_num))
    (pent_far_ge (e := (7501935520856053901 / 2000000000000000000 : ℝ)) (by norm_num) hR (by norm_num))
lemma d6_11 : Disjoint (interior (pentagon (427541651 / 100000000 : ℝ) (688191907 / 1000000000 : ℝ) (arccos (609321480728679 / 640678519271321 : ℝ)))) (interior (pentagon (776866263 / 200000000 : ℝ) (1186770703 / 250000000 : ℝ) (arccos (586557495560487399 / 1413442504439512601 : ℝ)))) := by
  have hR : circumradius ^ 2 * ((-78217039 / 200000000 : ℝ) ^ 2 + (811778181 / 200000000 : ℝ) ^ 2) ≤ (332550860168798141 / 40000000000000000 : ℝ) ^ 2 := by nlinarith [R_sq_le]
  exact halfplane_disjoint (-78217039 / 200000000 : ℝ) (811778181 / 200000000 : ℝ) (943501527691728991 / 100000000000000000 : ℝ) (by norm_num)
    (pent_far_le (e := (332550860168798141 / 40000000000000000 : ℝ)) (by norm_num) hR (by norm_num))
    (pent_far_ge (e := (332550860168798141 / 40000000000000000 : ℝ)) (by norm_num) hR (by norm_num))
lemma d6_12 : Disjoint (interior (pentagon (427541651 / 100000000 : ℝ) (688191907 / 1000000000 : ℝ) (arccos (609321480728679 / 640678519271321 : ℝ)))) (interior (pentagon (3385577897 / 1000000000 : ℝ) (174299027 / 100000000 : ℝ) (arccos (740383816821348399 / 1259616183178651601 : ℝ)))) := by
  exact halfplane_disjoint (-146946313 / 250000000 : ℝ) (161803399 / 200000000 : ℝ) (-126807591453 / 100000000000 : ℝ) (by norm_num)
    (pent_le hc6 hs6 (by linarith [R_lo, R_hi, P_lo, P_hi, C_lo, C_hi]) (by linarith [R_lo, R_hi, P_lo, P_hi, C_lo, C_hi]) (by linarith [R_lo, R_hi, P_lo, P_hi, C_lo, C_hi]) (by linarith [R_lo, R_hi, P_lo, P_hi, C_lo, C_hi]) (by linarith [R_lo, R_hi, P_lo, P_hi, C_lo, C_hi]))
    (pent_ge hc12 hs12 (by linarith [R_lo, R_hi, P_lo, P_hi, C_lo, C_hi]) (by linarith [R_lo, R_hi, P_lo, P_hi, C_lo, C_hi]) (by linarith [R_lo, R_hi, P_lo, P_hi, C_lo, C_hi]) (by linarith [R_lo, R_hi, P_lo, P_hi, C_lo, C_hi]) (by linarith [R_lo, R_hi, P_lo, P_hi, C_lo, C_hi]))
lemma d7_8 : Disjoint (interior (pentagon (688191907 / 1000000000 : ℝ) (2889578283 / 1000000000 : ℝ) (arccos (115267567140471 / 373013682859529 : ℝ)))) (interior (pentagon (478052591 / 100000000 : ℝ) (921971257 / 250000000 : ℝ) (arccos (232693732679495631 / 267306267320504369 : ℝ)))) := by
  have hR : circumradius ^ 2 * ((4092334003 / 1000000000 : ℝ) ^ 2 + (159661349 / 200000000 : ℝ) ^ 2) ≤ (8692245625611249517 / 1000000000000000000 : ℝ) ^ 2 := by nlinarith [R_sq_le]
  exact halfplane_disjoint (4092334003 / 1000000000 : ℝ) (159661349 / 200000000 : ℝ) (13815326600741182073 / 1000000000000000000 : ℝ) (by norm_num)
    (pent_far_le (e := (8692245625611249517 / 1000000000000000000 : ℝ)) (by norm_num) hR (by norm_num))
    (pent_far_ge (e := (8692245625611249517 / 1000000000000000000 : ℝ)) (by norm_num) hR (by norm_num))
lemma d7_9 : Disjoint (interior (pentagon (688191907 / 1000000000 : ℝ) (2889578283 / 1000000000 : ℝ) (arccos (115267567140471 / 373013682859529 : ℝ)))) (interior (pentagon (346666363 / 500000000 : ℝ) (2330244233 / 500000000 : ℝ) (arccos (62499975254507751 / 62500024745492249 : ℝ)))) := by
  have hR : circumradius ^ 2 * ((5140819 / 1000000000 : ℝ) ^ 2 + (1770910183 / 1000000000 : ℝ) ^ 2) ≤ (12544597217092337 / 8000000000000000 : ℝ) ^ 2 := by nlinarith [R_sq_le]
  exact halfplane_disjoint (5140819 / 1000000000 : ℝ) (1770910183 / 1000000000 : ℝ) (6688796128108049747 / 1000000000000000000 : ℝ) (by norm_num)
    (pent_far_le (e := (12544597217092337 / 8000000000000000 : ℝ)) (by norm_num) hR (by norm_num))
    (pent_far_ge (e := (12544597217092337 / 8000000000000000 : ℝ)) (by norm_num) hR (by norm_num))
lemma d7_10 : Disjoint (interior (pentagon (688191907 / 1000000000 : ℝ) (2889578283 / 1000000000 : ℝ) (arccos (115267567140471 / 373013682859529 : ℝ)))) (interior (pentagon (3634983 / 2000000 : ℝ) (948360003 / 500000000 : ℝ) (arccos (740383816821348399 / 1259616183178651601 : ℝ)))) := by
  exact halfplane_disjoint (404508497 / 500000000 : ℝ) (-146946313 / 250000000 : ℝ) (-453500560917 / 1000000000000 : ℝ) (by norm_num)
    (pent_le hc7 hs7 (by linarith [R_lo, R_hi, P_lo, P_hi, C_lo, C_hi]) (by linarith [R_lo, R_hi, P_lo, P_hi, C_lo, C_hi]) (by linarith [R_lo, R_hi, P_lo, P_hi, C_lo, C_hi]) (by linarith [R_lo, R_hi, P_lo, P_hi, C_lo, C_hi]) (by linarith [R_lo, R_hi, P_lo, P_hi, C_lo, C_hi]))
    (pent_ge hc10 hs10 (by linarith [R_lo, R_hi, P_lo, P_hi, C_lo, C_hi]) (by linarith [R_lo, R_hi, P_lo, P_hi, C_lo, C_hi]) (by linarith [R_lo, R_hi, P_lo, P_hi, C_lo, C_hi]) (by linarith [R_lo, R_hi, P_lo, P_hi, C_lo, C_hi]) (by linarith [R_lo, R_hi, P_lo, P_hi, C_lo, C_hi]))
lemma d7_11 : Disjoint (interior (pentagon (688191907 / 1000000000 : ℝ) (2889578283 / 1000000000 : ℝ) (arccos (115267567140471 / 373013682859529 : ℝ)))) (interior (pentagon (776866263 / 200000000 : ℝ) (1186770703 / 250000000 : ℝ) (arccos (586557495560487399 / 1413442504439512601 : ℝ)))) := by
  have hR : circumradius ^ 2 * ((199758713 / 62500000 : ℝ) ^ 2 + (1857504529 / 1000000000 : ℝ) ^ 2) ≤ (2733126038125220461 / 400000000000000000 : ℝ) ^ 2 := by nlinarith [R_sq_le]
  exact halfplane_disjoint (199758713 / 62500000 : ℝ) (1857504529 / 1000000000 : ℝ) (28799554234229931831 / 2000000000000000000 : ℝ) (by norm_num)
    (pent_far_le (e := (2733126038125220461 / 400000000000000000 : ℝ)) (by norm_num) hR (by norm_num))
    (pent_far_ge (e := (2733126038125220461 / 400000000000000000 : ℝ)) (by norm_num) hR (by norm_num))
lemma d7_12 : Disjoint (interior (pentagon (688191907 / 1000000000 : ℝ) (2889578283 / 1000000000 : ℝ) (arccos (115267567140471 / 373013682859529 : ℝ)))) (interior (pentagon (3385577897 / 1000000000 : ℝ) (174299027 / 100000000 : ℝ) (arccos (740383816821348399 / 1259616183178651601 : ℝ)))) := by
  have hR : circumradius ^ 2 * ((269738599 / 100000000 : ℝ) ^ 2 + (-1146588013 / 1000000000 : ℝ) ^ 2) ≤ (8590555250603568269 / 2000000000000000000 : ℝ) ^ 2 := by nlinarith [R_sq_le]
  exact halfplane_disjoint (269738599 / 100000000 : ℝ) (-1146588013 / 1000000000 : ℝ) (5676882023524090771 / 2000000000000000000 : ℝ) (by norm_num)
    (pent_far_le (e := (8590555250603568269 / 2000000000000000000 : ℝ)) (by norm_num) hR (by norm_num))
    (pent_far_ge (e := (8590555250603568269 / 2000000000000000000 : ℝ)) (by norm_num) hR (by norm_num))
lemma d8_9 : Disjoint (interior (pentagon (478052591 / 100000000 : ℝ) (921971257 / 250000000 : ℝ) (arccos (232693732679495631 / 267306267320504369 : ℝ)))) (interior (pentagon (346666363 / 500000000 : ℝ) (2330244233 / 500000000 : ℝ) (arccos (62499975254507751 / 62500024745492249 : ℝ)))) := by
  have hR : circumradius ^ 2 * ((-127724787 / 31250000 : ℝ) ^ 2 + (486301719 / 500000000 : ℝ) ^ 2) ≤ (176511055709454777 / 20000000000000000 : ℝ) ^ 2 := by nlinarith [R_sq_le]
  exact halfplane_disjoint (-127724787 / 31250000 : ℝ) (486301719 / 500000000 : ℝ) (-3563265236316566163 / 500000000000000000 : ℝ) (by norm_num)
    (pent_far_le (e := (176511055709454777 / 20000000000000000 : ℝ)) (by norm_num) hR (by norm_num))
    (pent_far_ge (e := (176511055709454777 / 20000000000000000 : ℝ)) (by norm_num) hR (by norm_num))
lemma d8_10 : Disjoint (interior (pentagon (478052591 / 100000000 : ℝ) (921971257 / 250000000 : ℝ) (arccos (232693732679495631 / 267306267320504369 : ℝ)))) (interior (pentagon (3634983 / 2000000 : ℝ) (948360003 / 500000000 : ℝ) (arccos (740383816821348399 / 1259616183178651601 : ℝ)))) := by
  have hR : circumradius ^ 2 * ((-296303441 / 100000000 : ℝ) ^ 2 + (-895582511 / 500000000 : ℝ) ^ 2) ≤ (1498480631360038573 / 250000000000000000 : ℝ) ^ 2 := by nlinarith [R_sq_le]
  exact halfplane_disjoint (-296303441 / 100000000 : ℝ) (-895582511 / 500000000 : ℝ) (-461767215971796857 / 31250000000000000 : ℝ) (by norm_num)
    (pent_far_le (e := (1498480631360038573 / 250000000000000000 : ℝ)) (by norm_num) hR (by norm_num))
    (pent_far_ge (e := (1498480631360038573 / 250000000000000000 : ℝ)) (by norm_num) hR (by norm_num))
lemma d8_11 : Disjoint (interior (pentagon (478052591 / 100000000 : ℝ) (921971257 / 250000000 : ℝ) (arccos (232693732679495631 / 267306267320504369 : ℝ)))) (interior (pentagon (776866263 / 200000000 : ℝ) (1186770703 / 250000000 : ℝ) (arccos (586557495560487399 / 1413442504439512601 : ℝ)))) := by
  exact halfplane_disjoint (-737060641 / 1000000000 : ℝ) (337913307 / 500000000 : ℝ) (-342974732859 / 1000000000000 : ℝ) (by norm_num)
    (pent_le hc8 hs8 (by linarith [R_lo, R_hi, P_lo, P_hi, C_lo, C_hi]) (by linarith [R_lo, R_hi, P_lo, P_hi, C_lo, C_hi]) (by linarith [R_lo, R_hi, P_lo, P_hi, C_lo, C_hi]) (by linarith [R_lo, R_hi, P_lo, P_hi, C_lo, C_hi]) (by linarith [R_lo, R_hi, P_lo, P_hi, C_lo, C_hi]))
    (pent_ge hc11 hs11 (by linarith [R_lo, R_hi, P_lo, P_hi, C_lo, C_hi]) (by linarith [R_lo, R_hi, P_lo, P_hi, C_lo, C_hi]) (by linarith [R_lo, R_hi, P_lo, P_hi, C_lo, C_hi]) (by linarith [R_lo, R_hi, P_lo, P_hi, C_lo, C_hi]) (by linarith [R_lo, R_hi, P_lo, P_hi, C_lo, C_hi]))
lemma d8_12 : Disjoint (interior (pentagon (478052591 / 100000000 : ℝ) (921971257 / 250000000 : ℝ) (arccos (232693732679495631 / 267306267320504369 : ℝ)))) (interior (pentagon (3385577897 / 1000000000 : ℝ) (174299027 / 100000000 : ℝ) (arccos (740383816821348399 / 1259616183178651601 : ℝ)))) := by
  have hR : circumradius ^ 2 * ((-1394948013 / 1000000000 : ℝ) ^ 2 + (-972447379 / 500000000 : ℝ) ^ 2) ≤ (5728495578668526733 / 2000000000000000000 : ℝ) ^ 2 := by nlinarith [R_sq_le]
  exact halfplane_disjoint (-1394948013 / 1000000000 : ℝ) (-972447379 / 500000000 : ℝ) (-175630169423666187 / 16000000000000000 : ℝ) (by norm_num)
    (pent_far_le (e := (5728495578668526733 / 2000000000000000000 : ℝ)) (by norm_num) hR (by norm_num))
    (pent_far_ge (e := (5728495578668526733 / 2000000000000000000 : ℝ)) (by norm_num) hR (by norm_num))
lemma d9_10 : Disjoint (interior (pentagon (346666363 / 500000000 : ℝ) (2330244233 / 500000000 : ℝ) (arccos (62499975254507751 / 62500024745492249 : ℝ)))) (interior (pentagon (3634983 / 2000000 : ℝ) (948360003 / 500000000 : ℝ) (arccos (740383816821348399 / 1259616183178651601 : ℝ)))) := by
  have hR : circumradius ^ 2 * ((562079387 / 500000000 : ℝ) ^ 2 + (-138188423 / 50000000 : ℝ) ^ 2) ≤ (2225537262412988669 / 500000000000000000 : ℝ) ^ 2 := by nlinarith [R_sq_le]
  exact halfplane_disjoint (562079387 / 500000000 : ℝ) (-138188423 / 50000000 : ℝ) (-3825010219232183549 / 500000000000000000 : ℝ) (by norm_num)
    (pent_far_le (e := (2225537262412988669 / 500000000000000000 : ℝ)) (by norm_num) hR (by norm_num))
    (pent_far_ge (e := (2225537262412988669 / 500000000000000000 : ℝ)) (by norm_num) hR (by norm_num))
lemma d9_11 : Disjoint (interior (pentagon (346666363 / 500000000 : ℝ) (2330244233 / 500000000 : ℝ) (arccos (62499975254507751 / 62500024745492249 : ℝ)))) (interior (pentagon (776866263 / 200000000 : ℝ) (1186770703 / 250000000 : ℝ) (arccos (586557495560487399 / 1413442504439512601 : ℝ)))) := by
  have hR : circumradius ^ 2 * ((3190998589 / 1000000000 : ℝ) ^ 2 + (43297173 / 500000000 : ℝ) ^ 2) ≤ (10189970575759158637 / 2000000000000000000 : ℝ) ^ 2 := by nlinarith [R_sq_le]
  exact halfplane_disjoint (3190998589 / 1000000000 : ℝ) (43297173 / 500000000 : ℝ) (15421961978013832337 / 2000000000000000000 : ℝ) (by norm_num)
    (pent_far_le (e := (10189970575759158637 / 2000000000000000000 : ℝ)) (by norm_num) hR (by norm_num))
    (pent_far_ge (e := (10189970575759158637 / 2000000000000000000 : ℝ)) (by norm_num) hR (by norm_num))
lemma d9_12 : Disjoint (interior (pentagon (346666363 / 500000000 : ℝ) (2330244233 / 500000000 : ℝ) (arccos (62499975254507751 / 62500024745492249 : ℝ)))) (interior (pentagon (3385577897 / 1000000000 : ℝ) (174299027 / 100000000 : ℝ) (arccos (740383816821348399 / 1259616183178651601 : ℝ)))) := by
  have hR : circumradius ^ 2 * ((2692245171 / 1000000000 : ℝ) ^ 2 + (-729374549 / 250000000 : ℝ) ^ 2) ≤ (15759979784436073657 / 2000000000000000000 : ℝ) ^ 2 := by nlinarith [R_sq_le]
  exact halfplane_disjoint (2692245171 / 1000000000 : ℝ) (-729374549 / 250000000 : ℝ) (-7700710232692008723 / 2000000000000000000 : ℝ) (by norm_num)
    (pent_far_le (e := (15759979784436073657 / 2000000000000000000 : ℝ)) (by norm_num) hR (by norm_num))
    (pent_far_ge (e := (15759979784436073657 / 2000000000000000000 : ℝ)) (by norm_num) hR (by norm_num))
lemma d10_11 : Disjoint (interior (pentagon (3634983 / 2000000 : ℝ) (948360003 / 500000000 : ℝ) (arccos (740383816821348399 / 1259616183178651601 : ℝ)))) (interior (pentagon (776866263 / 200000000 : ℝ) (1186770703 / 250000000 : ℝ) (arccos (586557495560487399 / 1413442504439512601 : ℝ)))) := by
  have hR : circumradius ^ 2 * ((413367963 / 200000000 : ℝ) ^ 2 + (1425181403 / 500000000 : ℝ) ^ 2) ≤ (12396394946697427861 / 2000000000000000000 : ℝ) ^ 2 := by nlinarith [R_sq_le]
  exact halfplane_disjoint (413367963 / 200000000 : ℝ) (1425181403 / 500000000 : ℝ) (30722002854942566533 / 2000000000000000000 : ℝ) (by norm_num)
    (pent_far_le (e := (12396394946697427861 / 2000000000000000000 : ℝ)) (by norm_num) hR (by norm_num))
    (pent_far_ge (e := (12396394946697427861 / 2000000000000000000 : ℝ)) (by norm_num) hR (by norm_num))
lemma d10_12 : Disjoint (interior (pentagon (3634983 / 2000000 : ℝ) (948360003 / 500000000 : ℝ) (arccos (740383816821348399 / 1259616183178651601 : ℝ)))) (interior (pentagon (3385577897 / 1000000000 : ℝ) (174299027 / 100000000 : ℝ) (arccos (740383816821348399 / 1259616183178651601 : ℝ)))) := by
  exact halfplane_disjoint (237764129 / 250000000 : ℝ) (-61803399 / 200000000 : ℝ) (996535142293 / 500000000000 : ℝ) (by norm_num)
    (pent_le hc10 hs10 (by linarith [R_lo, R_hi, P_lo, P_hi, C_lo, C_hi]) (by linarith [R_lo, R_hi, P_lo, P_hi, C_lo, C_hi]) (by linarith [R_lo, R_hi, P_lo, P_hi, C_lo, C_hi]) (by linarith [R_lo, R_hi, P_lo, P_hi, C_lo, C_hi]) (by linarith [R_lo, R_hi, P_lo, P_hi, C_lo, C_hi]))
    (pent_ge hc12 hs12 (by linarith [R_lo, R_hi, P_lo, P_hi, C_lo, C_hi]) (by linarith [R_lo, R_hi, P_lo, P_hi, C_lo, C_hi]) (by linarith [R_lo, R_hi, P_lo, P_hi, C_lo, C_hi]) (by linarith [R_lo, R_hi, P_lo, P_hi, C_lo, C_hi]) (by linarith [R_lo, R_hi, P_lo, P_hi, C_lo, C_hi]))
lemma d11_12 : Disjoint (interior (pentagon (776866263 / 200000000 : ℝ) (1186770703 / 250000000 : ℝ) (arccos (586557495560487399 / 1413442504439512601 : ℝ)))) (interior (pentagon (3385577897 / 1000000000 : ℝ) (174299027 / 100000000 : ℝ) (arccos (740383816821348399 / 1259616183178651601 : ℝ)))) := by
  have hR : circumradius ^ 2 * ((-249376709 / 500000000 : ℝ) ^ 2 + (-1502046271 / 500000000 : ℝ) ^ 2) ≤ (1159165871608338061 / 250000000000000000 : ℝ) ^ 2 := by nlinarith [R_sq_le]
  exact halfplane_disjoint (-249376709 / 500000000 : ℝ) (-1502046271 / 500000000 : ℝ) (-1156133610535292053 / 100000000000000000 : ℝ) (by norm_num)
    (pent_far_le (e := (1159165871608338061 / 250000000000000000 : ℝ)) (by norm_num) hR (by norm_num))
    (pent_far_ge (e := (1159165871608338061 / 250000000000000000 : ℝ)) (by norm_num) hR (by norm_num))

theorem proof : PacksInSquare 13 (552103 / 100000 : ℝ) := by
  refine ⟨![(623934821 / 250000000 : ℝ), (802776843 / 1000000000 : ℝ), (3431749619 / 1000000000 : ℝ), (2362406791 / 1000000000 : ℝ), (4832838093 / 1000000000 : ℝ), (2058684837 / 1000000000 : ℝ), (427541651 / 100000000 : ℝ), (688191907 / 1000000000 : ℝ), (478052591 / 100000000 : ℝ), (346666363 / 500000000 : ℝ), (3634983 / 2000000 : ℝ), (776866263 / 200000000 : ℝ), (3385577897 / 1000000000 : ℝ)],
    ![(688191907 / 1000000000 : ℝ), (191580027 / 250000000 : ℝ), (3262254353 / 1000000000 : ℝ), (4832838093 / 1000000000 : ℝ), (2133854777 / 1000000000 : ℝ), (420490387 / 125000000 : ℝ), (688191907 / 1000000000 : ℝ), (2889578283 / 1000000000 : ℝ), (921971257 / 250000000 : ℝ), (2330244233 / 500000000 : ℝ), (948360003 / 500000000 : ℝ), (1186770703 / 250000000 : ℝ), (174299027 / 100000000 : ℝ)],
    ![arccos (609321480728679 / 640678519271321 : ℝ), arccos (61206391959301831 / 63793608040698169 : ℝ), arccos (559705058434431 / 1393419941565569 : ℝ), arccos (740383816821348399 / 1259616183178651601 : ℝ), arccos (3493856215434639 / 4318643784565361 : ℝ), arccos (926604690537318031 / 1073395309462681969 : ℝ), arccos (609321480728679 / 640678519271321 : ℝ), arccos (115267567140471 / 373013682859529 : ℝ), arccos (232693732679495631 / 267306267320504369 : ℝ), arccos (62499975254507751 / 62500024745492249 : ℝ), arccos (740383816821348399 / 1259616183178651601 : ℝ), arccos (586557495560487399 / 1413442504439512601 : ℝ), arccos (740383816821348399 / 1259616183178651601 : ℝ)], ?_, ?_⟩
  · intro i
    fin_cases i
    · exact box0
    · exact box1
    · exact box2
    · exact box3
    · exact box4
    · exact box5
    · exact box6
    · exact box7
    · exact box8
    · exact box9
    · exact box10
    · exact box11
    · exact box12
  · intro i j hij
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · exact d0_1
    · exact d0_2
    · exact d0_3
    · exact d0_4
    · exact d0_5
    · exact d0_6
    · exact d0_7
    · exact d0_8
    · exact d0_9
    · exact d0_10
    · exact d0_11
    · exact d0_12
    · exact (d0_1).symm
    · exact absurd rfl hij
    · exact d1_2
    · exact d1_3
    · exact d1_4
    · exact d1_5
    · exact d1_6
    · exact d1_7
    · exact d1_8
    · exact d1_9
    · exact d1_10
    · exact d1_11
    · exact d1_12
    · exact (d0_2).symm
    · exact (d1_2).symm
    · exact absurd rfl hij
    · exact d2_3
    · exact d2_4
    · exact d2_5
    · exact d2_6
    · exact d2_7
    · exact d2_8
    · exact d2_9
    · exact d2_10
    · exact d2_11
    · exact d2_12
    · exact (d0_3).symm
    · exact (d1_3).symm
    · exact (d2_3).symm
    · exact absurd rfl hij
    · exact d3_4
    · exact d3_5
    · exact d3_6
    · exact d3_7
    · exact d3_8
    · exact d3_9
    · exact d3_10
    · exact d3_11
    · exact d3_12
    · exact (d0_4).symm
    · exact (d1_4).symm
    · exact (d2_4).symm
    · exact (d3_4).symm
    · exact absurd rfl hij
    · exact d4_5
    · exact d4_6
    · exact d4_7
    · exact d4_8
    · exact d4_9
    · exact d4_10
    · exact d4_11
    · exact d4_12
    · exact (d0_5).symm
    · exact (d1_5).symm
    · exact (d2_5).symm
    · exact (d3_5).symm
    · exact (d4_5).symm
    · exact absurd rfl hij
    · exact d5_6
    · exact d5_7
    · exact d5_8
    · exact d5_9
    · exact d5_10
    · exact d5_11
    · exact d5_12
    · exact (d0_6).symm
    · exact (d1_6).symm
    · exact (d2_6).symm
    · exact (d3_6).symm
    · exact (d4_6).symm
    · exact (d5_6).symm
    · exact absurd rfl hij
    · exact d6_7
    · exact d6_8
    · exact d6_9
    · exact d6_10
    · exact d6_11
    · exact d6_12
    · exact (d0_7).symm
    · exact (d1_7).symm
    · exact (d2_7).symm
    · exact (d3_7).symm
    · exact (d4_7).symm
    · exact (d5_7).symm
    · exact (d6_7).symm
    · exact absurd rfl hij
    · exact d7_8
    · exact d7_9
    · exact d7_10
    · exact d7_11
    · exact d7_12
    · exact (d0_8).symm
    · exact (d1_8).symm
    · exact (d2_8).symm
    · exact (d3_8).symm
    · exact (d4_8).symm
    · exact (d5_8).symm
    · exact (d6_8).symm
    · exact (d7_8).symm
    · exact absurd rfl hij
    · exact d8_9
    · exact d8_10
    · exact d8_11
    · exact d8_12
    · exact (d0_9).symm
    · exact (d1_9).symm
    · exact (d2_9).symm
    · exact (d3_9).symm
    · exact (d4_9).symm
    · exact (d5_9).symm
    · exact (d6_9).symm
    · exact (d7_9).symm
    · exact (d8_9).symm
    · exact absurd rfl hij
    · exact d9_10
    · exact d9_11
    · exact d9_12
    · exact (d0_10).symm
    · exact (d1_10).symm
    · exact (d2_10).symm
    · exact (d3_10).symm
    · exact (d4_10).symm
    · exact (d5_10).symm
    · exact (d6_10).symm
    · exact (d7_10).symm
    · exact (d8_10).symm
    · exact (d9_10).symm
    · exact absurd rfl hij
    · exact d10_11
    · exact d10_12
    · exact (d0_11).symm
    · exact (d1_11).symm
    · exact (d2_11).symm
    · exact (d3_11).symm
    · exact (d4_11).symm
    · exact (d5_11).symm
    · exact (d6_11).symm
    · exact (d7_11).symm
    · exact (d8_11).symm
    · exact (d9_11).symm
    · exact (d10_11).symm
    · exact absurd rfl hij
    · exact d11_12
    · exact (d0_12).symm
    · exact (d1_12).symm
    · exact (d2_12).symm
    · exact (d3_12).symm
    · exact (d4_12).symm
    · exact (d5_12).symm
    · exact (d6_12).symm
    · exact (d7_12).symm
    · exact (d8_12).symm
    · exact (d9_12).symm
    · exact (d10_12).symm
    · exact (d11_12).symm
    · exact absurd rfl hij

end Submissions.PentagonsThirteenAttain.LoydRecord
