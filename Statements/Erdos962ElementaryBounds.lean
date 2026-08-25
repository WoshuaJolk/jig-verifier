import Mathlib.Data.Nat.Find
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Order.Interval.Set.Nat

namespace Statements.Erdos962ElementaryBounds

def HasLargePrimeBlock (n width : ℕ) : Prop :=
  ∃ start ≤ n, ∀ offset ∈ Set.Icc 1 width,
    ∃ p : ℕ, p.Prime ∧ width < p ∧ p ∣ start + offset

noncomputable def maxWidth (n : ℕ) : ℕ :=
  open scoped Classical in
  Nat.findGreatest (fun width => HasLargePrimeBlock n width) n

/-- The elementary bounds built into, and nontrivially witnessed by, the
maximal block-length definition. -/
abbrev statement : Prop :=
  (∀ n : ℕ, maxWidth n ≤ n) ∧
    ∀ n : ℕ, 1 ≤ n → 1 ≤ maxWidth n

theorem target : statement := sorry

end Statements.Erdos962ElementaryBounds
