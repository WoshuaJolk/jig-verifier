import Mathlib.Data.Nat.Totient

namespace Statements.Erdos1135ShortOddCycles

abbrev statement : Prop :=
  ∀ a b c k l m : ℕ, 0 < a → 0 < b → 0 < c →
    Odd a → Odd b → Odd c → 0 < k → 0 < l → 0 < m →
    3 * a + 1 = 2 ^ k * b → 3 * b + 1 = 2 ^ l * c →
    (c = a ∨ 3 * c + 1 = 2 ^ m * a) → a = 1 ∧ b = 1 ∧ c = 1

end Statements.Erdos1135ShortOddCycles
