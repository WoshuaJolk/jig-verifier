import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Finset.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.Order.Filter.AtTopBot.CountablyGenerated
import Mathlib.Order.LiminfLimsup
import Mathlib.Topology.Instances.ENNReal.Lemmas

namespace Statements.Erdos1040CapacityPolynomialSublevels

open Filter MeasureTheory

def indexPairs (n : ℕ) : Finset (Fin n × Fin n) :=
  (Finset.univ ×ˢ Finset.univ).filter fun ij => ij.1 < ij.2

noncomputable def vandermondeRoot (n : ℕ) (z : Fin n → ℂ) : ENNReal :=
  ENNReal.rpow
    (∏ ij ∈ indexPairs n, ENNReal.ofReal (dist (z ij.1) (z ij.2)))
    ((n.choose 2 : ℝ)⁻¹)

noncomputable def diameterAt (n : ℕ) (F : Set ℂ) : ENNReal :=
  ⨆ z : Fin n → ℂ, ⨆ (_ : ∀ i, z i ∈ F), vandermondeRoot n z

noncomputable def transfiniteDiameter (F : Set ℂ) : ENNReal :=
  limsup (fun n => diameterAt n F) atTop

def rootProduct (roots : List ℂ) (z : ℂ) : ℂ :=
  (roots.map fun r => z - r).prod

noncomputable def polynomialSublevelInfimum (F : Set ℂ) : ENNReal :=
  ⨅ roots : {l : List ℂ // l ≠ [] ∧ ∀ z ∈ l, z ∈ F},
    volume {z : ℂ | ‖rootProduct roots.1 z‖ < 1}

/-- The still-open capacity-at-least-one implication in Erdős problem 1040. -/
abbrev statement : Prop :=
  ∀ F : Set ℂ, IsClosed F → F.Infinite →
    1 ≤ transfiniteDiameter F → polynomialSublevelInfimum F = 0

theorem target : statement := sorry

end Statements.Erdos1040CapacityPolynomialSublevels
