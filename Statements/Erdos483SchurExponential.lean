import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Fin.Basic
import Mathlib.Order.Filter.AtTopBot.Basic

open Filter

/-!
# Erdős problem 483

Is the Schur number bounded above by `C^k` for an absolute constant `C`?
-/

namespace Statements.Erdos483SchurExponential

def ForcesSchur (colors N : ℕ) : Prop :=
  ∀ coloring : ℕ → Fin colors,
    ∃ a b c : ℕ,
      1 ≤ a ∧ a ≤ N ∧
      1 ≤ b ∧ b ≤ N ∧
      1 ≤ c ∧ c ≤ N ∧
      a + b = c ∧
      coloring a = coloring b ∧ coloring b = coloring c

noncomputable def schurNumber (colors : ℕ) : ℕ :=
  sInf {N : ℕ | ForcesSchur colors N}

abbrev statement : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ᶠ k : ℕ in atTop, (schurNumber k : ℝ) < C ^ k

theorem target : statement := sorry

end Statements.Erdos483SchurExponential
