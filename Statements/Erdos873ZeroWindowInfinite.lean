import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Set.Card

namespace Statements.Erdos873ZeroWindowInfinite

def blockLCM (a : ℕ → ℕ) (i k : ℕ) : ℕ :=
  (Finset.range k).lcm (fun j => a (i + j))

noncomputable def windowCount (a : ℕ → ℕ) (X : ℝ) (k : ℕ) : ℕ∞ :=
  {i : ℕ | (blockLCM a i k : ℝ) < X}.encard

/-- Empty LCM windows have value one, so at threshold two every index is
counted and the extended count is infinite. -/
abbrev statement : Prop :=
  ∀ a : ℕ → ℕ, windowCount a 2 0 = ⊤

theorem target : statement := sorry

end Statements.Erdos873ZeroWindowInfinite
