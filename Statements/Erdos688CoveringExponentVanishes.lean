import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Order.Filter.AtTopBot.CountablyGenerated
import Mathlib.Order.Lattice

open Filter Real

namespace Statements.Erdos688CoveringExponentVanishes

def Coverable (n : ℕ) (ε : ℝ) : Prop :=
  ∃ a : ℕ → ℕ, ∀ m : ℕ, 1 ≤ m → m ≤ n →
    ∃ p : ℕ, p.Prime ∧ (n : ℝ) ^ ε < p ∧ p ≤ n ∧ a p ≡ m [MOD p]

noncomputable def epsilonFunction (n : ℕ) : ℝ :=
  sSup {ε : ℝ | Coverable n ε}

/-- Erdős Problem 688: the optimal covering exponent tends to zero. -/
abbrev statement : Prop :=
  epsilonFunction =o[atTop] (fun _ : ℕ => (1 : ℝ))

theorem target : statement := sorry

end Statements.Erdos688CoveringExponentVanishes
