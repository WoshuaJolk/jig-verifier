import Mathlib.Data.Nat.Basic

namespace Statements.ErdosStrausShiftObstruction409577

/-- Failure of the shifted-divisor construction for two explicit inputs,
with no search cutoff on any parameter. This does not refute Erdos-Straus. -/
abbrev statement : Prop :=
  ∀ n : ℕ, (n = 409 ∨ n = 577) →
    ∀ a b g m : ℕ, 0 < a → 0 < b → 0 < m →
      n + a = b * g → g + 1 ≠ 4 * a * m

end Statements.ErdosStrausShiftObstruction409577
