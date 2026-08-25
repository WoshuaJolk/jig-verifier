import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.NumberTheory.FermatPsp
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Topology.Instances.EReal.Lemmas

namespace Statements.Erdos1057CarmichaelDensityExponent

open Filter Set Topology

def IsCarmichael (n : ℕ) : Prop :=
  ∀ b ≥ 1, n.Coprime b → n.FermatPsp b

noncomputable def carmichaelCounting (x : ℝ) : ℝ :=
  ({n : ℕ | IsCarmichael n ∧ (n : ℝ) ≤ x}.ncard : ℝ)

/-- Erdős Problem 1057: the number `C(x)` of Carmichael numbers at most
`x` is `x^(1-o(1))`. -/
abbrev statement : Prop :=
  Tendsto (fun x : ℝ ↦ Real.log (carmichaelCounting x) / Real.log x)
    atTop (𝓝 1)

theorem target : statement := sorry

end Statements.Erdos1057CarmichaelDensityExponent
