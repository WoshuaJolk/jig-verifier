import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Topology.Instances.Nat

namespace Statements.Erdos77DiagonalRamseyGrowthLimit

open Filter

def MonochromaticClique (k n : ℕ) (color : Fin n → Fin n → Fin 2) : Prop :=
  ∃ vertices : Fin k ↪ Fin n, ∃ c : Fin 2,
    ∀ ⦃i j⦄, i ≠ j → color (vertices i) (vertices j) = c

def RamseyProperty (k n : ℕ) : Prop :=
  ∀ color : Fin n → Fin n → Fin 2,
    (∀ i j, color i j = color j i) →
      MonochromaticClique k n color

noncomputable def ramseyNumber (k : ℕ) : ℕ :=
  sInf {n : ℕ | RamseyProperty k n}

/-- The existence part of Erdős Problem 77: diagonal Ramsey numbers have
an exponential growth constant. -/
abbrev statement : Prop :=
  ∃ L : ℝ,
    Tendsto
      (fun k => (ramseyNumber k : ℝ) ^ (1 / (k : ℝ)))
      atTop (nhds L)

theorem target : statement := sorry

end Statements.Erdos77DiagonalRamseyGrowthLimit
