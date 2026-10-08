import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Topology.Instances.Real.Lemmas

namespace Statements.PentagonsTwoReduction

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

/-- The corner lemma implies the lower bound for two pentagons: if every unit pentagon in the
quadrant `x, y ≥ 0` contains a point with both coordinates at least `sStar / 2`, then any square
holding two unit pentagons with disjoint interiors has side at least `sStar`. -/
abbrev statement : Prop :=
  (∀ a b θ : ℝ, pentagon a b θ ⊆ Set.Ici 0 ×ˢ Set.Ici 0 →
    ∃ p ∈ pentagon a b θ, sStar / 2 ≤ p.1 ∧ sStar / 2 ≤ p.2) →
  ∀ s : ℝ, PacksInSquare 2 s → sStar ≤ s

theorem target : statement := sorry

end Statements.PentagonsTwoReduction
