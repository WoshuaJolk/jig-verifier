import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Topology.Instances.Real.Lemmas

namespace Statements.PentagonsThreeAttain

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

/-- Three unit regular pentagons fit in a square of side `s3` ≈ 2.90812. -/
abbrev statement : Prop := PacksInSquare 3 s3

theorem target : statement := sorry

end Statements.PentagonsThreeAttain
