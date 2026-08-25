import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Set.Card

namespace Statements.Erdos873LCMWindowSubpower

def blockLCM (a : ℕ → ℕ) (i k : ℕ) : ℕ :=
  (Finset.range k).lcm (fun j => a (i + j))

noncomputable def windowCount (a : ℕ → ℕ) (X : ℝ) (k : ℕ) : ℕ∞ :=
  {i : ℕ | (blockLCM a i k : ℝ) < X}.encard

/-- Erdős Problem 873: consecutive LCM windows in every increasing positive
sequence have counting function below every positive power. -/
abbrev statement : Prop :=
  ∀ a : ℕ → ℕ, 0 < a 0 → StrictMono a →
    ∀ ε : ℝ, 0 < ε → ∃ k : ℕ, ∀ X : ℝ, 0 < X →
      windowCount a X k < (X ^ ε).toEReal

theorem target : statement := sorry

end Statements.Erdos873LCMWindowSubpower
