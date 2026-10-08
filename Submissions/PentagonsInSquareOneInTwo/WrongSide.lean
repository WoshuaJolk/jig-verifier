import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Analysis.Convex.Basic
import Mathlib.Tactic

namespace Submissions.PentagonsInSquareOneInTwo.WrongSide

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

lemma circumradius_pos : 0 < circumradius := by
  unfold circumradius
  have : 0 < Real.sin (Real.pi / 5) :=
    Real.sin_pos_of_pos_of_lt_pi (by positivity) (by linarith [Real.pi_pos])
  positivity

lemma circumradius_le_one : circumradius ≤ 1 := by
  unfold circumradius
  have h6 : Real.sin (Real.pi / 6) ≤ Real.sin (Real.pi / 5) :=
    Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith [Real.pi_pos])
      (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])
  rw [Real.sin_pi_div_six] at h6
  rw [div_le_one (by linarith)]
  linarith

theorem proof : PacksInSquare 1 3 := by
  refine ⟨fun _ => 3/2, fun _ => 3/2, fun _ => 0, ?_, ?_⟩
  · intro i
    apply convexHull_min _ ((convex_Icc 0 3).prod (convex_Icc 0 3))
    rintro _ ⟨k, rfl⟩
    have hR0 := circumradius_pos
    have hR1 := circumradius_le_one
    set c := Real.cos (0 + 2 * Real.pi * ((k : ℕ) : ℝ) / 5)
    set s := Real.sin (0 + 2 * Real.pi * ((k : ℕ) : ℝ) / 5)
    have hc1 := Real.neg_one_le_cos (0 + 2 * Real.pi * ((k : ℕ) : ℝ) / 5)
    have hc2 := Real.cos_le_one (0 + 2 * Real.pi * ((k : ℕ) : ℝ) / 5)
    have hs1 := Real.neg_one_le_sin (0 + 2 * Real.pi * ((k : ℕ) : ℝ) / 5)
    have hs2 := Real.sin_le_one (0 + 2 * Real.pi * ((k : ℕ) : ℝ) / 5)
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> simp only <;> nlinarith
  · intro i j hij
    exact absurd (Subsingleton.elim i j) hij

end Submissions.PentagonsInSquareOneInTwo.WrongSide
