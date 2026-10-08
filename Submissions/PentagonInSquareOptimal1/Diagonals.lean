import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Algebra.Order.Round
import Mathlib.Tactic

namespace Submissions.PentagonInSquareOptimal1.Diagonals

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


lemma S5_pos : 0 < sin (π / 5) := sin_pos_of_pos_of_lt_pi (by positivity) (by linarith [pi_pos])

lemma R_pos : 0 < circumradius := by unfold circumradius; have := S5_pos; positivity

lemma sqrt5_sq : √5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)

/-- The diagonal of the unit regular pentagon is the golden ratio. -/
lemma diag_eq : 2 * circumradius * sin (2 * π / 5) = (1 + √5) / 2 := by
  have h := S5_pos
  unfold circumradius
  rw [show 2 * π / 5 = 2 * (π / 5) by ring, sin_two_mul, cos_pi_div_five]
  field_simp
  norm_num

lemma phi_pos : 0 < (1 + √5) / 2 := by positivity

/-! ### Every vertex, indexed by an arbitrary integer, lies in the pentagon. -/

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

lemma vert_bounds {a b θ s : ℝ} (h : pentagon a b θ ⊆ Set.Icc 0 s ×ˢ Set.Icc 0 s) (m : ℤ) :
    0 ≤ a + circumradius * cos (θ + 2 * π * (m : ℝ) / 5) ∧
    a + circumradius * cos (θ + 2 * π * (m : ℝ) / 5) ≤ s ∧
    0 ≤ b + circumradius * sin (θ + 2 * π * (m : ℝ) / 5) ∧
    b + circumradius * sin (θ + 2 * π * (m : ℝ) / 5) ≤ s := by
  obtain ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩ := h (vert_mem a b θ m)
  exact ⟨h1, h2, h3, h4⟩

/-! ### The diagonal through vertices `j-1` and `j+1` has length the golden ratio and direction
perpendicular to `θ + 2πj/5`; both of its projections must fit in the square. -/

lemma diag_bound {a b θ s : ℝ} (h : pentagon a b θ ⊆ Set.Icc 0 s ×ˢ Set.Icc 0 s) (j : ℤ) :
    (1 + √5) / 2 * |sin (θ + 2 * π * (j : ℝ) / 5)| ≤ s ∧
    (1 + √5) / 2 * |cos (θ + 2 * π * (j : ℝ) / 5)| ≤ s := by
  obtain ⟨x1l, x1u, y1l, y1u⟩ := vert_bounds h (j - 1)
  obtain ⟨x2l, x2u, y2l, y2u⟩ := vert_bounds h (j + 1)
  set γ := θ + 2 * π * (j : ℝ) / 5 with hγ
  have e1 : θ + 2 * π * ((j - 1 : ℤ) : ℝ) / 5 = γ - 2 * π / 5 := by rw [hγ]; push_cast; ring
  have e2 : θ + 2 * π * ((j + 1 : ℤ) : ℝ) / 5 = γ + 2 * π / 5 := by rw [hγ]; push_cast; ring
  rw [e1] at x1l x1u y1l y1u
  rw [e2] at x2l x2u y2l y2u
  have dx : circumradius * cos (γ + 2 * π / 5) - circumradius * cos (γ - 2 * π / 5)
      = -((2 * circumradius * sin (2 * π / 5)) * sin γ) := by rw [cos_add, cos_sub]; ring
  have dy : circumradius * sin (γ + 2 * π / 5) - circumradius * sin (γ - 2 * π / 5)
      = (2 * circumradius * sin (2 * π / 5)) * cos γ := by rw [sin_add, sin_sub]; ring
  rw [diag_eq] at dx dy
  have hφ := phi_pos
  constructor
  · have k : |(1 + √5) / 2 * sin γ| ≤ s := abs_le.mpr ⟨by linarith, by linarith⟩
    rwa [abs_mul, abs_of_pos hφ] at k
  · have k : |(1 + √5) / 2 * cos γ| ≤ s := abs_le.mpr ⟨by linarith, by linarith⟩
    rwa [abs_mul, abs_of_pos hφ] at k

/-! ### Every orientation has a diagonal within `π/20` of one of the two axes. -/

lemma axis_close (θ : ℝ) : ∃ j : ℤ,
    cos (π / 20) ≤ |sin (θ + 2 * π * (j : ℝ) / 5)| ∨
    cos (π / 20) ≤ |cos (θ + 2 * π * (j : ℝ) / 5)| := by
  have hp : 0 < π / 10 := by positivity
  set n := round (θ / (π / 10)) with hn
  have hε : |θ - (n : ℝ) * (π / 10)| ≤ π / 20 := by
    have h := abs_sub_round (θ / (π / 10))
    have e : θ - (n : ℝ) * (π / 10) = (θ / (π / 10) - n) * (π / 10) := by field_simp
    rw [e, abs_mul, abs_of_pos hp]
    calc |θ / (π / 10) - ↑n| * (π / 10) ≤ 1 / 2 * (π / 10) := by gcongr
      _ = π / 20 := by ring
  refine ⟨n, ?_⟩
  set ε := θ - (n : ℝ) * (π / 10) with hεdef
  have hθ : θ + 2 * π * (n : ℝ) / 5 = ε + (n : ℝ) * (π / 2) := by rw [hεdef]; ring
  have hc : cos (π / 20) ≤ cos ε := by
    rw [← cos_abs ε]
    exact cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _) (by linarith [pi_pos]) hε
  rw [hθ]
  obtain ⟨p, hp2 | hp2⟩ := Int.even_or_odd' n
  · right
    rw [show (n : ℝ) * (π / 2) = (p : ℝ) * π by rw [hp2]; push_cast; ring,
      cos_add_int_mul_pi, abs_mul, abs_neg_one_zpow, one_mul]
    exact hc.trans (le_abs_self _)
  · left
    rw [show ε + (n : ℝ) * (π / 2) = (ε + π / 2) + (p : ℝ) * π by rw [hp2]; push_cast; ring,
      sin_add_int_mul_pi, abs_mul, abs_neg_one_zpow, one_mul, sin_add_pi_div_two]
    exact hc.trans (le_abs_self _)

theorem lower_bound {s : ℝ} (hs : PacksInSquare 1 s) :
    (1 + √5) / 2 * cos (π / 20) ≤ s := by
  obtain ⟨a, b, θ, hsub, -⟩ := hs
  have h := hsub 0
  obtain ⟨j, hj | hj⟩ := axis_close (θ 0)
  · exact (mul_le_mul_of_nonneg_left hj phi_pos.le).trans (diag_bound h j).1
  · exact (mul_le_mul_of_nonneg_left hj phi_pos.le).trans (diag_bound h j).2

/-! ### Attainment: rotate by `π/20` and centre at `(R cos(3π/20), R cos(3π/20))`. -/

lemma side_eq : circumradius * (cos (π / 20) + cos (3 * π / 20)) = (1 + √5) / 2 * cos (π / 20) := by
  have h := S5_pos
  have hc10 : 0 < cos (π / 10) := cos_pos_of_mem_Ioo ⟨by linarith [pi_pos], by linarith [pi_pos]⟩
  have hs10 : sin (π / 10) = (√5 - 1) / 4 := by
    rw [← cos_pi_div_two_sub, show π / 2 - π / 10 = 2 * (π / 5) by ring, cos_two_mul,
      cos_pi_div_five]
    nlinarith [sqrt5_sq]
  have hS : sin (π / 5) = 2 * sin (π / 10) * cos (π / 10) := by
    rw [show π / 5 = 2 * (π / 10) by ring, sin_two_mul]
  rw [cos_add_cos, show (π / 20 + 3 * π / 20) / 2 = π / 10 by ring,
    show (π / 20 - 3 * π / 20) / 2 = -(π / 20) by ring, cos_neg]
  unfold circumradius
  rw [hS, hs10]
  have h5 : (0:ℝ) < √5 - 1 := by nlinarith [sqrt5_sq, Real.sqrt_nonneg 5]
  field_simp
  linear_combination (-cos (π / 20)) * sqrt5_sq

lemma coord_ok {t : ℝ} (h1 : π / 20 ≤ t) (h2 : t ≤ 17 * π / 20) :
    0 ≤ circumradius * cos (3 * π / 20) + circumradius * cos t ∧
    circumradius * cos (3 * π / 20) + circumradius * cos t ≤ (1 + √5) / 2 * cos (π / 20) := by
  have hR := R_pos
  have hpi := pi_pos
  have lo : cos (17 * π / 20) ≤ cos t := cos_le_cos_of_nonneg_of_le_pi (by linarith) (by linarith) h2
  have hi : cos t ≤ cos (π / 20) := cos_le_cos_of_nonneg_of_le_pi (by linarith) (by linarith) h1
  have e : cos (17 * π / 20) = -cos (3 * π / 20) := by
    rw [show 17 * π / 20 = π - 3 * π / 20 by ring, cos_pi_sub]
  rw [← side_eq]
  constructor <;> nlinarith [mul_le_mul_of_nonneg_left lo hR.le, mul_le_mul_of_nonneg_left hi hR.le]

lemma attained : PacksInSquare 1 ((1 + √5) / 2 * cos (π / 20)) := by
  have hpi := pi_pos
  refine ⟨fun _ => circumradius * cos (3 * π / 20), fun _ => circumradius * cos (3 * π / 20),
    fun _ => π / 20, ?_, ?_⟩
  · intro i
    apply convexHull_min _ ((convex_Icc _ _).prod (convex_Icc _ _))
    rintro _ ⟨k, rfl⟩
    suffices H : ∀ k : ℕ, k < 5 →
        (circumradius * cos (3 * π / 20) + circumradius * cos (π / 20 + 2 * π * (k : ℝ) / 5),
         circumradius * cos (3 * π / 20) + circumradius * sin (π / 20 + 2 * π * (k : ℝ) / 5)) ∈
        Set.Icc (0:ℝ) ((1 + √5) / 2 * cos (π / 20)) ×ˢ Set.Icc (0:ℝ) ((1 + √5) / 2 * cos (π / 20)) from
      H k k.isLt
    intro k hk
    rw [← cos_pi_div_two_sub]
    simp only [Set.mem_prod, Set.mem_Icc]
    interval_cases k
    · rw [show π / 20 + 2 * π * ((0:ℕ):ℝ) / 5 = π / 20 by push_cast; ring,
        show π / 2 - π / 20 = 9 * π / 20 by ring]
      exact ⟨coord_ok (by linarith) (by linarith), coord_ok (by linarith) (by linarith)⟩
    · rw [show π / 20 + 2 * π * ((1:ℕ):ℝ) / 5 = 9 * π / 20 by push_cast; ring,
        show π / 2 - 9 * π / 20 = π / 20 by ring]
      exact ⟨coord_ok (by linarith) (by linarith), coord_ok (by linarith) (by linarith)⟩
    · rw [show π / 20 + 2 * π * ((2:ℕ):ℝ) / 5 = 17 * π / 20 by push_cast; ring,
        show π / 2 - 17 * π / 20 = -(7 * π / 20) by ring, cos_neg]
      exact ⟨coord_ok (by linarith) (by linarith), coord_ok (by linarith) (by linarith)⟩
    · rw [show π / 20 + 2 * π * ((3:ℕ):ℝ) / 5 = -(15 * π / 20) + 2 * π by push_cast; ring,
        show π / 2 - (-(15 * π / 20) + 2 * π) = -(15 * π / 20) by ring, cos_add_two_pi, cos_neg]
      exact ⟨coord_ok (by linarith) (by linarith), coord_ok (by linarith) (by linarith)⟩
    · rw [show π / 20 + 2 * π * ((4:ℕ):ℝ) / 5 = -(7 * π / 20) + 2 * π by push_cast; ring,
        show π / 2 - (-(7 * π / 20) + 2 * π) = -(-(17 * π / 20) + 2 * π) by ring]
      simp only [cos_neg, cos_add_two_pi]
      exact ⟨coord_ok (by linarith) (by linarith), coord_ok (by linarith) (by linarith)⟩
  · intro i j hij
    exact absurd (Subsingleton.elim i j) hij

theorem proof : IsLeast {s : ℝ | PacksInSquare 1 s} ((1 + √5) / 2 * cos (π / 20)) :=
  ⟨attained, fun _ hs => lower_bound hs⟩

end Submissions.PentagonInSquareOptimal1.Diagonals
