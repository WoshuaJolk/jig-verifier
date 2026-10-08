import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic

namespace Submissions.PentagonCornerReach.Edges

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

end Submissions.PentagonCornerReach.Edges
