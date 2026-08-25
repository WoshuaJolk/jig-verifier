import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.ENat.Basic

namespace Statements.Erdos873OneWindowNaturalThreshold

def blockLCM (a : ℕ → ℕ) (i k : ℕ) : ℕ :=
  (Finset.range k).lcm (fun j => a (i + j))

noncomputable def windowCount (a : ℕ → ℕ) (X : ℝ) (k : ℕ) : ℕ∞ :=
  {i : ℕ | (blockLCM a i k : ℝ) < X}.encard

/-- A one-term window in a positive strictly increasing sequence has fewer
than `N` starts below every positive natural threshold `N`. -/
abbrev statement : Prop :=
  ∀ a : ℕ → ℕ, 0 < a 0 → StrictMono a →
    ∀ N : ℕ, 0 < N → windowCount a (N : ℝ) 1 < (N : ℕ∞)

theorem target : statement := sorry

end Statements.Erdos873OneWindowNaturalThreshold
