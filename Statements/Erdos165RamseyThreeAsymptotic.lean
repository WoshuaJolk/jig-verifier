import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Order.Filter.AtTopBot.CountablyGenerated

open Filter SimpleGraph

namespace Statements.Erdos165RamseyThreeAsymptotic

def RamseyProperty (N k : ℕ) : Prop :=
  ∀ G : SimpleGraph (Fin N),
    (∃ triangle : Finset (Fin N), G.IsNClique 3 triangle) ∨
    (∃ independent : Finset (Fin N), Gᶜ.IsNClique k independent)

noncomputable def ramseyThree (k : ℕ) : ℕ :=
  sInf {N : ℕ | RamseyProperty N k}

/-- The currently conjectured answer to Erdős Problem 165:
`R(3,k) ~ k²/(2 log k)`. -/
abbrev statement : Prop :=
  Tendsto
    (fun k : ℕ =>
      (ramseyThree k : ℝ) * Real.log (k : ℝ) / (k : ℝ) ^ 2)
    atTop (nhds (1 / 2 : ℝ))

theorem target : statement := sorry

end Statements.Erdos165RamseyThreeAsymptotic
