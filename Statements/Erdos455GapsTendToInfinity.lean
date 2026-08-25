import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Order.Filter.AtTopBot.Basic

open Filter

namespace Statements.Erdos455GapsTendToInfinity

def gap (q : ℕ → ℕ) (n : ℕ) : ℕ :=
  q (n + 1) - q n

/-- Every convex increasing prime sequence has gaps tending to infinity. -/
abbrev statement : Prop :=
  ∀ q : ℕ → ℕ, StrictMono q →
    (∀ n, (q n).Prime ∧
      q (n + 2) - q (n + 1) ≥ q (n + 1) - q n) →
    Tendsto (gap q) atTop atTop

theorem target : statement := sorry

end Statements.Erdos455GapsTendToInfinity
