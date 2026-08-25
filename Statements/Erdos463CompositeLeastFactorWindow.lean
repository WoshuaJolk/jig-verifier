import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Order.Filter.AtTopBot.Archimedean

open Filter

namespace Statements.Erdos463CompositeLeastFactorWindow

private abbrev IsComposite (m : ℕ) : Prop :=
  1 < m ∧ ¬m.Prime

/-- Erdős Problem 463: composite numbers should eventually cross every
diverging lower offset while remaining within their least-prime-factor window. -/
abbrev statement : Prop :=
  ∃ f : ℕ → ℕ, Tendsto f atTop atTop ∧
    ∀ᶠ n in atTop,
      ∃ m : ℕ, IsComposite m ∧
        n + f n < m ∧ m < n + m.minFac

theorem target : statement := sorry

end Statements.Erdos463CompositeLeastFactorWindow
