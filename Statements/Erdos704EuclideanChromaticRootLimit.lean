import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Order.Lattice.Nat
import Mathlib.Order.Filter.AtTopBot.CountablyGenerated
import Mathlib.Topology.Instances.ENNReal.Lemmas

namespace Statements.Erdos704EuclideanChromaticRootLimit

open Filter
open scoped BigOperators

abbrev Point (n : ℕ) := Fin n → ℝ

def squaredDistance {n : ℕ} (p q : Point n) : ℝ :=
  ∑ i : Fin n, (p i - q i) ^ 2

def HasProperColoring (n m : ℕ) : Prop :=
  ∃ color : Point n → Fin m, ∀ p q : Point n,
    squaredDistance p q = 1 → color p ≠ color q

noncomputable def euclideanChromatic (n : ℕ) : ℕ :=
  sInf {m : ℕ | HasProperColoring n m}

/-- Erdős problem 704: existence of the exponential growth-rate limit for
    chromatic numbers of Euclidean unit-distance graphs. -/
abbrev statement : Prop :=
  ∃ L : ℝ, Tendsto
    (fun n => (euclideanChromatic n : ℝ) ^ ((1 : ℝ) / n))
    atTop (nhds L)

theorem target : statement := sorry

end Statements.Erdos704EuclideanChromaticRootLimit
