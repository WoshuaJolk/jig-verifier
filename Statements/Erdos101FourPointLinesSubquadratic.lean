import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Data.Set.Card
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.Topology.Instances.Nat

namespace Statements.Erdos101FourPointLinesSubquadratic

open Filter

abbrev Point := EuclideanSpace ℝ (Fin 2)

def determinedLines (S : Set Point) : Set (AffineSubspace ℝ Point) :=
  {L | ∃ p ∈ S, ∃ q ∈ S, p ≠ q ∧ L = affineSpan ℝ {p, q}}

def linesWithExactlyFour (S : Set Point) : Set (AffineSubspace ℝ Point) :=
  {L ∈ determinedLines S | ((L : Set Point) ∩ S).ncard = 4}

def NoFiveCollinear (S : Set Point) : Prop :=
  ∀ p ∈ S, ∀ q ∈ S, p ≠ q →
    (((affineSpan ℝ {p, q} : AffineSubspace ℝ Point) : Set Point) ∩ S).ncard ≤ 4

noncomputable def maximumFourPointLines (n : ℕ) : ℕ :=
  sSup {count : ℕ | ∃ S : Set Point,
    S.Finite ∧ S.ncard = n ∧ NoFiveCollinear S ∧
      (linesWithExactlyFour S).ncard = count}

/-- Erdős Problem 101: with no five collinear, the number of lines containing
exactly four points is subquadratic. -/
abbrev statement : Prop :=
  (fun n => (maximumFourPointLines n : ℝ)) =o[atTop]
    (fun n => (n : ℝ) ^ 2)

theorem target : statement := sorry

end Statements.Erdos101FourPointLinesSubquadratic
