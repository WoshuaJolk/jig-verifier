import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Finset.Prod
import Mathlib.Order.Filter.AtTopBot.CountablyGenerated
import Mathlib.Order.Lattice.Nat
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace Statements.Erdos956ConvexTranslateUnitDistances

open Filter

abbrev Point := EuclideanSpace ℝ (Fin 2)
abbrev Configuration (n : ℕ) := Fin n → Point

def translate (C : Set Point) (x : Point) : Set Point := {p | p - x ∈ C}

def HasDisjointTranslates {n : ℕ} (C : Set Point)
    (X : Configuration n) : Prop :=
  Function.Injective X ∧
    ∀ i j, i ≠ j → Disjoint (translate C (X i)) (translate C (X j))

noncomputable def setDistance (A B : Set Point) : ℝ :=
  sInf {d : ℝ | ∃ a ∈ A, ∃ b ∈ B, d = dist a b}

noncomputable def unitPairs {n : ℕ} (C : Set Point)
    (X : Configuration n) : Finset (Fin n × Fin n) :=
  (Finset.univ ×ˢ Finset.univ).filter fun ij =>
    ij.1 < ij.2 ∧
      setDistance (translate C (X ij.1)) (translate C (X ij.2)) = 1

noncomputable def convexTranslateUnitNumber (n : ℕ) : ℕ :=
  sSup {m : ℕ | ∃ C : Set Point, ∃ X : Configuration n,
    C.Nonempty ∧ Convex ℝ C ∧ IsCompact C ∧
      HasDisjointTranslates C X ∧ (unitPairs C X).card = m}

/-- The superlinear lower-bound conjecture in Erdős problem 956. -/
abbrev statement : Prop :=
  ∃ c : ℝ, 0 < c ∧
    ∀ᶠ n : ℕ in atTop,
      (n : ℝ) ^ (1 + c) < convexTranslateUnitNumber n

theorem target : statement := sorry

end Statements.Erdos956ConvexTranslateUnitDistances
