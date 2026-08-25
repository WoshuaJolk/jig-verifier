import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Topology.Algebra.Order.LiminfLimsup

open Filter MeasureTheory
open scoped Topology

/-!
# Erdős problem 1131

For distinct interpolation nodes in `[-1,1]`, let `I` be the integral of the
sum of the squares of their Lagrange basis polynomials.  Is its minimum
`2 - (1 + o(1))/n`?
-/

namespace Statements.Erdos1131LagrangeEnergyMinimum

noncomputable def lagrangeBasis {n : ℕ} (nodes : Fin n → ℝ)
    (k : Fin n) (t : ℝ) : ℝ :=
  ∏ i ∈ Finset.univ.erase k, (t - nodes i) / (nodes k - nodes i)

def Admissible {n : ℕ} (nodes : Fin n → ℝ) : Prop :=
  Function.Injective nodes ∧
    ∀ k, nodes k ∈ Set.Icc (-1 : ℝ) 1

noncomputable def energy {n : ℕ} (nodes : Fin n → ℝ) : ℝ :=
  ∫ t in Set.Icc (-1 : ℝ) 1,
    (∑ k : Fin n, (lagrangeBasis nodes k t) ^ 2) ∂volume

noncomputable def minimumEnergy (n : ℕ) : ℝ :=
  sInf {v : ℝ | ∃ nodes : Fin n → ℝ,
    Admissible nodes ∧ v = energy nodes}

abbrev statement : Prop :=
  Tendsto
    (fun n : ℕ => (n : ℝ) * (2 - minimumEnergy n))
    atTop (𝓝 1)

theorem target : statement := sorry

end Statements.Erdos1131LagrangeEnergyMinimum
