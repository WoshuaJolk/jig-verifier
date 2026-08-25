import Mathlib.NumberTheory.SmoothNumbers
import Mathlib.Order.Lattice.Nat

namespace Statements.Erdos961BaseWindowBound

def HasRoughInEveryWindow (k n : ℕ) : Prop :=
  ∀ m ≥ k + 1, ∃ i ∈ Set.Ico m (m + n),
    i ∉ Nat.smoothNumbers (k + 1)

noncomputable def f (k : ℕ) : ℕ :=
  sInf {n | HasRoughInEveryWindow k n}

/-- For the base smoothness bound `k=1`, every eligible singleton window
already contains a prime factor greater than one. -/
abbrev statement : Prop :=
  HasRoughInEveryWindow 1 1 ∧ f 1 ≤ 1

theorem target : statement := sorry

end Statements.Erdos961BaseWindowBound
