import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Lattice
import Mathlib.Data.Rat.Defs
import Mathlib.Order.Filter.AtTopBot.CountablyGenerated

open Asymptotics Filter

namespace Statements.Erdos304UnitFractionLength

def unitFractionExpressible (a b : ℕ) : Set ℕ :=
  {k | ∃ s : Finset ℕ,
    s.card = k ∧ (∀ n ∈ s, n > 1) ∧
      (a / b : ℚ) = ∑ n ∈ s, (n : ℚ)⁻¹}

noncomputable def smallestCollection (a b : ℕ) : ℕ :=
  sInf (unitFractionExpressible a b)

noncomputable def smallestCollectionTo (b : ℕ) : ℕ :=
  sSup {smallestCollection a b | a ∈ Finset.Ico 1 b}

/-- Erdős Problem 304. -/
abbrev statement : Prop :=
  (fun b : ℕ => (smallestCollectionTo b : ℝ)) =O[atTop]
    (fun b : ℕ => Real.log (Real.log b))

theorem target : statement := sorry

end Statements.Erdos304UnitFractionLength
