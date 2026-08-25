import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Topology.Order.OrderClosed

open Filter
open scoped Topology

/-!
# Erdős problem 588

For fixed `k ≥ 4`, is the maximum number of lines containing at least `k`
points of an `n`-point planar set with no `k+1` collinear points `o(n²)`?
-/

namespace Statements.Erdos588RichLinesSubquadratic

abbrev Point := EuclideanSpace ℝ (Fin 2)

def lineThrough (p q : Point) : Set Point :=
  {r | Collinear ℝ {p, q, r}}

def CandidateLine (A : Finset Point) (L : Set Point) : Prop :=
  ∃ p ∈ A, ∃ q ∈ A, p ≠ q ∧ L = lineThrough p q

def Admissible (k : ℕ) (A : Finset Point) : Prop :=
  ∀ ⦃p q⦄, p ∈ A → q ∈ A → p ≠ q →
    Set.ncard ((A : Set Point) ∩ lineThrough p q) ≤ k

noncomputable def richLineCount (k : ℕ) (A : Finset Point) : ℕ :=
  Set.ncard {L : Set Point |
    CandidateLine A L ∧ k ≤ Set.ncard ((A : Set Point) ∩ L)}

noncomputable def richLineMax (k n : ℕ) : ℕ :=
  sSup {m : ℕ | ∃ A : Finset Point,
    A.card = n ∧ Admissible k A ∧ m = richLineCount k A}

abbrev statement : Prop :=
  ∀ k : ℕ, 4 ≤ k →
    Tendsto
      (fun n : ℕ => (richLineMax k n : ℝ) / (n : ℝ) ^ 2)
      atTop (𝓝 0)

theorem target : statement := sorry

end Statements.Erdos588RichLinesSubquadratic
